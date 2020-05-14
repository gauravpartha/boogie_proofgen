﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie
{
    public enum MoverType
    {
        Atomic,
        Right,
        Left,
        Both
    }

    public class LayerRange
    {
        public static int Min = 0;
        public static int Max = int.MaxValue;
        public static LayerRange MinMax = new LayerRange(Min, Max);

        public int lowerLayerNum;
        public int upperLayerNum;
        
        public LayerRange(int layer) : this(layer, layer) { }

        public LayerRange(int lower, int upper)
        {
            Debug.Assert(lower <= upper);
            this.lowerLayerNum = lower;
            this.upperLayerNum = upper;
        }

        public bool Contains(int layerNum)
        {
            return lowerLayerNum <= layerNum && layerNum <= upperLayerNum;
        }

        public bool Subset(LayerRange other)
        {
            return other.lowerLayerNum <= lowerLayerNum && upperLayerNum <= other.upperLayerNum;
        }

        public bool OverlapsWith(LayerRange other)
        {
            return lowerLayerNum <= other.upperLayerNum && other.lowerLayerNum <= upperLayerNum;
        }

        public override string ToString()
        {
            return $"[{lowerLayerNum}, {upperLayerNum}]";
        }

        public override bool Equals(object obj)
        {
            LayerRange other = obj as LayerRange;
            if (obj == null)
            {
                return false;
            }
            return lowerLayerNum == other.lowerLayerNum && upperLayerNum == other.upperLayerNum;
        }

        public override int GetHashCode()
        {
            return (23 * 31 + lowerLayerNum) * 31 + upperLayerNum;
        }
    }

    public abstract class Action
    {
        public Procedure proc;
        public Implementation impl;
        public LayerRange layerRange;
        public List<AssertCmd> gate;
        public HashSet<Variable> gateUsedGlobalVars;
        public HashSet<Variable> actionUsedGlobalVars;
        public HashSet<Variable> modifiedGlobalVars;

        protected Action(Procedure proc, Implementation impl, LayerRange layerRange)
        {
            this.proc = proc;
            this.impl = impl;
            this.layerRange = layerRange;

            CivlUtil.AddInlineAttribute(proc);
            CivlUtil.AddInlineAttribute(impl);

            // The gate of an action is represented as asserts at the beginning of the procedure body.
            gate = impl.Blocks[0].cmds.TakeWhile((c, i) => c is AssertCmd).Cast<AssertCmd>().ToList();
            // We separate the gate from the action
            impl.Blocks[0].cmds.RemoveRange(0, gate.Count);

            gateUsedGlobalVars = new HashSet<Variable>(VariableCollector.Collect(gate).Where(x => x is GlobalVariable));
            actionUsedGlobalVars = new HashSet<Variable>(VariableCollector.Collect(impl).Where(x => x is GlobalVariable));
            modifiedGlobalVars = new HashSet<Variable>(AssignedVariables().Where(x => x is GlobalVariable));

            // We usually declare the Boogie procedure and implementation of an atomic action together.
            // Since Boogie only stores the supplied attributes (in particular linearity) in the procedure parameters,
            // we copy them into the implementation parameters here.
            for (int i = 0; i < proc.InParams.Count; i++)
            {
                impl.InParams[i].Attributes = proc.InParams[i].Attributes;
            }
            for (int i = 0; i < proc.OutParams.Count; i++)
            {
                impl.OutParams[i].Attributes = proc.OutParams[i].Attributes;
            }
        }

        public bool HasAssumeCmd => impl.Blocks.Any(b => b.Cmds.Any(c => c is AssumeCmd));
        
        protected List<Variable> AssignedVariables()
        {
            List<Variable> modifiedVars = new List<Variable>();
            foreach (Cmd cmd in impl.Blocks.SelectMany(b => b.Cmds))
            {
                cmd.AddAssignedVariables(modifiedVars);
            }
            return modifiedVars;
        }
    }

    public class IntroductionAction : Action
    {
        public IntroductionAction(Procedure proc, Implementation impl, LayerRange layerRange) :
            base(proc, impl, layerRange)
        {
        }

        public int LayerNum => layerRange.lowerLayerNum; // layerRange.lowerLayerNum == layerRange.upperLayerNum
    }
    
    public class AtomicAction : Action
    {
        public MoverType moverType;
        public AtomicAction refinedAction;

        public List<AssertCmd> firstGate;
        public Implementation firstImpl;
        public List<AssertCmd> secondGate;
        public Implementation secondImpl;
        
        public DatatypeConstructor pendingAsyncCtor;
        public HashSet<AtomicAction> pendingAsyncs;
        public bool hasChoice; // only relevant for invariant actions

        public Dictionary<Variable, Function> triggerFunctions;

        public AtomicAction(Procedure proc, Implementation impl, LayerRange layerRange, MoverType moverType):
            base(proc, impl, layerRange)
        {
            this.moverType = moverType;
            AtomicActionDuplicator.SetupCopy(this, ref firstGate, ref firstImpl, "first_");
            AtomicActionDuplicator.SetupCopy(this, ref secondGate, ref secondImpl, "second_");
            DeclareTriggerFunctions();
        }

        public bool IsRightMover { get { return moverType == MoverType.Right || moverType == MoverType.Both; } }
        public bool IsLeftMover { get { return moverType == MoverType.Left || moverType == MoverType.Both; } }

        public bool HasPendingAsyncs => pendingAsyncs != null;

        public bool TriviallyCommutesWith(AtomicAction other)
        {
            return this.modifiedGlobalVars.Intersect(other.actionUsedGlobalVars).Count() == 0 &&
                   this.actionUsedGlobalVars.Intersect(other.modifiedGlobalVars).Count() == 0;
        }

        private void DeclareTriggerFunctions()
        {
            triggerFunctions = new Dictionary<Variable, Function>();
            foreach(var v in impl.LocVars)
            {
                List<Variable> args = new List<Variable> { VarHelper.Formal(v.Name, v.TypedIdent.Type, true) };
                Variable result = VarHelper.Formal("r", Type.Bool, false);
                triggerFunctions[v] = new Function(Token.NoToken, $"Trigger_{impl.Name}_{v.Name}", args, result);
            }
            for (int i = 0; i < impl.LocVars.Count; i++)
            {
                triggerFunctions[firstImpl.LocVars[i]] = triggerFunctions[impl.LocVars[i]];
                triggerFunctions[secondImpl.LocVars[i]] = triggerFunctions[impl.LocVars[i]];
            }
        }

        public void AddTriggerAssumes(Program program)
        {
            foreach (Variable v in impl.LocVars)
            {
                var f = triggerFunctions[v];
                program.AddTopLevelDeclaration(f);
                var assume = CmdHelper.AssumeCmd(ExprHelper.FunctionCall(f, Expr.Ident(v)));
                impl.Blocks[0].Cmds.Insert(0, assume);
            }
        }
    }

    public abstract class YieldingProc
    {
        public Procedure proc;
        public MoverType moverType;
        public int upperLayer;

        public YieldingProc(Procedure proc, MoverType moverType, int upperLayer)
        {
            this.proc = proc;
            this.moverType = moverType;
            this.upperLayer = upperLayer;
        }

        public bool IsRightMover { get { return moverType == MoverType.Right || moverType == MoverType.Both; } }
        public bool IsLeftMover { get { return moverType == MoverType.Left || moverType == MoverType.Both; } }
    }

    public class SkipProc : YieldingProc
    {
        public HashSet<Variable> hiddenFormals;

        public SkipProc(Procedure proc, int upperLayer)
            : base(proc, MoverType.Both, upperLayer)
        {
            hiddenFormals = new HashSet<Variable>(proc.InParams.Union(proc.OutParams));
        }
    }

    public class MoverProc : YieldingProc
    {
        public HashSet<Variable> modifiedGlobalVars;

        public MoverProc(Procedure proc, MoverType moverType, int upperLayer)
            : base(proc, moverType, upperLayer)
        {
            modifiedGlobalVars = new HashSet<Variable>(proc.Modifies.Select(ie => ie.Decl));
        }
    }

    public class ActionProc : YieldingProc
    {
        public AtomicAction refinedAction;
        public HashSet<Variable> hiddenFormals;
        
        public ActionProc(Procedure proc, AtomicAction refinedAction, int upperLayer)
            : base(proc, refinedAction.moverType, upperLayer)
        {
            this.refinedAction = refinedAction;
            hiddenFormals = new HashSet<Variable>(proc.InParams.Concat(proc.OutParams).Where(x => x.HasAttribute(CivlAttributes.HIDE)));
        }

        public AtomicAction RefinedActionAtLayer(int layer)
        {
            if (layer <= upperLayer) return null;
            var action = refinedAction;
            while (action != null)
            {
                if (layer <= action.layerRange.upperLayerNum)
                    return action;
                action = action.refinedAction;
            }
            return null;
        }
    }

    public class LemmaProc
    {
        public Procedure proc;

        public LemmaProc(Procedure proc)
        {
            this.proc = proc;
        }
    }

    /// <summary>
    /// Creates first/second copies of atomic actions used in commutativity checks
    /// (i.e., all non-global variables are prefixed with first_ resp. second_).
    /// Note that we also rename bound variables.
    /// </summary>
    class AtomicActionDuplicator : Duplicator
    {
        private readonly string prefix;
        private Dictionary<Variable, Expr> subst;
        private Dictionary<Variable, Expr> bound;
        private List<Variable> inParamsCopy;
        private List<Variable> outParamsCopy;
        private List<Variable> localsCopy;

        public static void SetupCopy(AtomicAction action, ref List<AssertCmd> gateCopy, ref Implementation implCopy, string prefix)
        {
            var aad = new AtomicActionDuplicator(prefix, action);

            gateCopy = new List<AssertCmd>();
            foreach (AssertCmd assertCmd in action.gate)
            {
                gateCopy.Add((AssertCmd)aad.Visit(assertCmd));
            }

            implCopy = aad.VisitImplementation(action.impl);
        }

        private AtomicActionDuplicator(string prefix, AtomicAction action)
        {
            this.prefix = prefix;
            subst = new Dictionary<Variable, Expr>();
            bound = new Dictionary<Variable, Expr>();

            inParamsCopy = new List<Variable>();
            outParamsCopy = new List<Variable>();
            localsCopy = new List<Variable>();


            foreach (Variable x in action.impl.InParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), true, x.Attributes);
                inParamsCopy.Add(xCopy);
                subst[x] = Expr.Ident(xCopy);
            }
            foreach (Variable x in action.impl.OutParams)
            {
                Variable xCopy = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), false, x.Attributes);
                outParamsCopy.Add(xCopy);
                subst[x] = Expr.Ident(xCopy);
            }

            foreach (Variable x in action.impl.LocVars)
            {
                Variable xCopy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type));
                subst[x] = Expr.Ident(xCopy);
                localsCopy.Add(xCopy);
            }
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            node = base.VisitImplementation(node);
            node.InParams = inParamsCopy;
            node.OutParams = outParamsCopy;
            node.LocVars = localsCopy;
            return node;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (subst.ContainsKey(node.Decl))
            {
                return subst[node.Decl];
            }
            else if (bound.ContainsKey(node.Decl))
            {
                return bound[node.Decl];
            }
            return base.VisitIdentifierExpr(node);
        }

        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            var oldToNew = node.Dummies.ToDictionary(x => x, x => new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, prefix + x.Name, x.TypedIdent.Type), x.Attributes));

            foreach (var x in node.Dummies)
            {
                bound.Add(x, Expr.Ident(oldToNew[x]));
            }

            BinderExpr expr = base.VisitBinderExpr(node);
            expr.Dummies = node.Dummies.Select(x => oldToNew[x]).ToList<Variable>();

            // We process triggers of quantifier expressions here, because otherwise the
            // substitutions for bound variables have to be leaked outside this procedure.
            if (node is QuantifierExpr quantifierExpr)
            {
                if (quantifierExpr.Triggers != null)
                {
                    ((QuantifierExpr)expr).Triggers = this.VisitTrigger(quantifierExpr.Triggers);
                }
            }

            foreach (var x in node.Dummies)
            {
                bound.Remove(x);
            }

            return expr;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            // Don't remove this implementation! Triggers should be duplicated in VisitBinderExpr.
            return (QuantifierExpr)this.VisitBinderExpr(node);
        }
    }
}

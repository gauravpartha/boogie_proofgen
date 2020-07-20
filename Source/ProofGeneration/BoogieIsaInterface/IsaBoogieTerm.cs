using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.Isa;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public static class IsaBoogieTerm
    {

        private readonly static TermIdent redCfgMultiId = IsaCommonTerms.TermIdentFromName("red_cfg_multi");
        private readonly static TermIdent redCmdListId = IsaCommonTerms.TermIdentFromName("red_cmd_list");
        private readonly static TermIdent redExprId = IsaCommonTerms.TermIdentFromName("red_expr");
        private readonly static TermIdent normalStateId = IsaCommonTerms.TermIdentFromName("Normal");
        private readonly static TermIdent magicStateId = IsaCommonTerms.TermIdentFromName("Magic");
        private readonly static TermIdent failureStateId = IsaCommonTerms.TermIdentFromName("Failure");
        private readonly static TermIdent convertValToBoolId = IsaCommonTerms.TermIdentFromName("convert_val_to_bool");
        private readonly static TermIdent convertValToIntId = IsaCommonTerms.TermIdentFromName("convert_val_to_int");
        private readonly static TermIdent funInterpWfId = IsaCommonTerms.TermIdentFromName("fun_interp_wf");
        private readonly static TermIdent funInterpSingleWfId = IsaCommonTerms.TermIdentFromName("fun_interp_single_wf");
        private readonly static TermIdent stateWfId = IsaCommonTerms.TermIdentFromName("state_typ_wf");
 
        private static TypeIsaVisitor typeIsaVisitor = new TypeIsaVisitor();

        //TODO initialize all the default constructors, so that they only need to be allocated once (Val, Var, etc...)

        public static Term ExprFromVal(Term val)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Val"), new List<Term>() { val });
        }

        public static Term Var(string v)
        {
            Term stringConst = new StringConst(v);
            return new TermApp(IsaCommonTerms.TermIdentFromName("Var"), new List<Term>() { stringConst });
        }

        public static Term BVar(int i)
        {
            Contract.Requires(i >= 0);
            Term natConst = new NatConst(i);
            return new TermApp(IsaCommonTerms.TermIdentFromName("BVar"), new List<Term>() { natConst });
        }

        public static Term ValFromLiteral(LiteralExpr node)
        {
            if (node.Type.IsBool)
            {
               return BoolVal(node.asBool);
            }
            else if (node.Type.IsInt)
            {
                return IntVal(node.asBigNum);
            } else
            {
                throw new NotImplementedException();
            }
        }

        public static Term IntVal(Microsoft.Basetypes.BigNum num)
        {
            Term intConst = new IntConst(num);
            return IntVal(intConst);
        }

        public static Term IntVal(Term i)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("IntV"), new List<Term>() { i });
        }

        public static Term BoolVal(bool b)
        {
            Term boolConst = new BoolConst(b);
            return BoolVal(boolConst);
        }

        public static Term BoolVal(Term b)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("BoolV"), new List<Term>() { b });
        }

        public static Term Assert(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assert"), new List<Term>() { arg });
        }

        public static Term Assume(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assume"), new List<Term>() { arg });
        }

        public static Term Assign(IList<Term> lhsTerms, IList<Term> rhsTerms)
        {
            if ((lhsTerms.Count !=rhsTerms.Count))
            {
                throw new ProofGenUnexpectedStateException(typeof(BasicCmdIsaVisitor), "different number of lhs and rhs");
            }

            IList<Term> results = new List<Term>();
            lhsTerms.ZipDo(rhsTerms, (lhs, rhs) => results.Add(new TermTuple(new List<Term>() { lhs, rhs })));

            return new TermApp(IsaCommonTerms.TermIdentFromName("Assign"), new List<Term> { new TermList(results) });
        }

        public static Term Havoc(Term var)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Havoc"), new List<Term>() { var });
        }

        public static Term Binop(BinaryOperator.Opcode opcode, Term arg1, Term arg2)
        {
            string bopIsa;

            switch(opcode)
            {
                case BinaryOperator.Opcode.Eq:
                    bopIsa = "Eq";
                    break;
                case BinaryOperator.Opcode.Neq:
                    bopIsa = "Neq";
                    break;                
                case BinaryOperator.Opcode.Add:
                    bopIsa = "Add";
                    break;
                case BinaryOperator.Opcode.Sub:
                    bopIsa = "Sub";
                    break;
                case BinaryOperator.Opcode.Mul:
                    bopIsa = "Mul";
                    break;
                case BinaryOperator.Opcode.Lt:
                    bopIsa = "Lt";
                    break;
                case BinaryOperator.Opcode.Le:
                    bopIsa = "Le";
                    break;
                case BinaryOperator.Opcode.Gt:
                    bopIsa = "Gt";
                    break;
                case BinaryOperator.Opcode.Ge:
                    bopIsa = "Ge";
                    break;
                case BinaryOperator.Opcode.And:
                    bopIsa = "And";
                    break;
                case BinaryOperator.Opcode.Or:
                    bopIsa = "Or";
                    break;
                case BinaryOperator.Opcode.Imp:
                    bopIsa = "Imp";
                    break;
                default:
                    throw new NotImplementedException();
            }

            var list = new List<Term>() { arg1, IsaCommonTerms.TermIdentFromName(bopIsa), arg2 };
            return new TermApp(IsaCommonTerms.TermIdentFromName("BinOp"), list);
        }

        public static Term Unop(UnaryOperator.Opcode opcode, Term arg)
        {
            string uopIsa;

            switch (opcode)
            {
                case UnaryOperator.Opcode.Not:
                    uopIsa = "Not";
                    break;
                case UnaryOperator.Opcode.Neg:
                    uopIsa = "UMinus";
                    break;
                default:
                    throw new NotImplementedException();
            }

            var list = new List<Term>() { IsaCommonTerms.TermIdentFromName(uopIsa), arg };
            return new TermApp(IsaCommonTerms.TermIdentFromName("UnOp"), list);
        }

        /*
         * if isForall is false, then it must be an existential quantifier
         * */
        public static Term Quantifier(bool isForall, Term boundVarType, Term body)
        {
            return isForall ? Forall(boundVarType, body) : Exists(boundVarType, body);
        }

        public static Term Forall(Term boundVarType, Term body)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Forall"), new List<Term> { boundVarType, body });
        }

        public static Term Exists(Term boundVarType, Term body)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Exists"), new List<Term> { boundVarType, body });
        }

        public static Term FunCall(string fname, IList<Term> args)
        {
            var wrapArgs = new TermList(args);
            var fnameAndArgs = new List<Term>() { new StringConst(fname), wrapArgs };

            return new TermApp(IsaCommonTerms.TermIdentFromName("FunExp"), fnameAndArgs);
        }

        public static Term MethodCFGBody(Term entryNode, Term nodeSet, Term outEdges, Term nodeToBlock)
        {
            var mapping =
                new List<Tuple<string, Term>>()
                {
                    new Tuple<string, Term>("entry", entryNode),
                    new Tuple<string, Term>("nodes", nodeSet),
                    new Tuple<string, Term>("out_edges", outEdges),
                    new Tuple<string, Term>("node_to_block", nodeToBlock)
                };

            return new TermRecord(mapping);
        }

        public static Term Method(string methodName, Term parameters, Term localVars, Term methodCFGBody)
        {
            var elements =
                new List<Term>()
                {
                    new StringConst(methodName),
                    parameters,
                    localVars,
                    methodCFGBody
                };

            return new TermTuple(elements);                            
        }

        public static Term Program(Term fdecls, Term constantDecls, Term globalDecls, Term axioms, List<Term> mdecls)
        {
            Term mdeclsTerm = new TermList(mdecls);

            return new TermApp(IsaCommonTerms.TermIdentFromName("Program"), 
                new List<Term>() { fdecls, constantDecls, globalDecls, axioms, mdeclsTerm });
        }

        public static Term Normal(Term n_s)
        {
            return new TermApp(normalStateId, new List<Term>() { n_s });
        }

        public static Term Magic()
        {
            return magicStateId;
        }

        public static Term Failure()
        {
            return failureStateId;
        }

        public static Term RedCmdList(Term varContext, Term funContext, Term cmdList, Term initState, Term finalState)
        {
            return
                new TermApp(redCmdListId,
                new List<Term>()
                {
                    varContext,
                    funContext,
                    cmdList,
                    initState,
                    finalState
                }
                );
        }

        public static Term RedCFGMulti(Term varContext, Term funContext, Term cfg, Term initCFGConfig, Term finalCFGConfig)
        {
            return
                new TermApp(redCfgMultiId,
                new List<Term>()
                {
                    varContext,
                    funContext,
                    cfg,
                    initCFGConfig,
                    finalCFGConfig
                }
                );
        }

        public static Term CFGConfigNode(Term node, Term state)
        {
            return CFGConfig(IsaCommonTerms.Inl(node), state);
        }

        public static Term CFGConfigDone(Term state)
        {
            return CFGConfig(IsaCommonTerms.Inr(IsaCommonTerms.Unit()), state);
        }

        public static Term CFGConfig(Term nodeOrDone, Term state)
        {
            return new TermTuple(new List<Term> { nodeOrDone, state });
        }

        public static Term RedExpr(Term funContext, Term expr, Term state, Term resultValue)
        {
            return
                new TermApp(redExprId,
                new List<Term>()
                {
                    funContext,
                    expr,
                    state,
                    resultValue
                });
        }

        public static Term FunDecl(Function f, bool includeName=true)
        {
            Term fname = new StringConst(f.Name);
            var argTypes = new TermList(f.InParams.Select(v => typeIsaVisitor.Translate(v.TypedIdent.Type)).ToList());
            var retType = typeIsaVisitor.Translate(f.OutParams.First().TypedIdent.Type);
            if(includeName)
            {
                return new TermTuple(new List<Term> { fname, argTypes, retType });
            } else
            {
                return new TermTuple(new List<Term> { argTypes, retType });
            }
        }

        public static Term VarDecl(Variable v, bool includeName=true)
        {
            Term vName = new StringConst(v.Name);
            Term vType = typeIsaVisitor.Translate(v.TypedIdent.Type);
            if(includeName)
            {
                return new TermTuple(new List<Term> { vName, vType });
            } else
            {
                return new TermTuple(new List<Term> { vType });
            }
        }

        public static Term ConvertValToBool(Term val)
        {
            return new TermApp(convertValToBoolId, val);
        }

        public static Term ConvertValToInt(Term val)
        {
            return new TermApp(convertValToIntId, val);
        }

        public static Term FunInterpWf(Term fdecls, Term finterp)
        {
            return new TermApp(funInterpWfId, new List<Term> { fdecls, finterp });
        }

        public static Term FunInterpSingleWf(Function f, Term fTerm)
        {
            return FunInterpSingleWf(FunDecl(f, false), fTerm);
        }

        public static Term FunInterpSingleWf(Term fdecl, Term fun)
        {
            return new TermApp(funInterpSingleWfId, new List<Term> { fdecl, fun });
        }

        public static Term StateWf(Term vdecls, Term state)
        {
            return new TermApp(stateWfId, new List<Term> { state, vdecls });
        }

    }
}

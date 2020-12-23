using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.BoogieIsaInterface;
using ProofGeneration.BoogieIsaInterface.VariableTranslation;
using ProofGeneration.Isa;
using ProofGeneration.ProgramToVCProof;
using ProofGeneration.Util;

namespace ProofGeneration
{
    public static class IsaBoogieTerm
    {

        private readonly static TermIdent intVId = IsaCommonTerms.TermIdentFromName("IntV");
        private readonly static TermIdent boolVId = IsaCommonTerms.TermIdentFromName("BoolV");
        private readonly static TermIdent intLitId = IsaCommonTerms.TermIdentFromName("LInt");
        private readonly static TermIdent boolLitId = IsaCommonTerms.TermIdentFromName("LBool");
        
        private readonly static TermIdent varId = IsaCommonTerms.TermIdentFromName("Var");
        private readonly static TermIdent bvarId = IsaCommonTerms.TermIdentFromName("BVar");
        
        private readonly static TermIdent lookupVarId = IsaCommonTerms.TermIdentFromName("lookup_var");
        private readonly static TermIdent lookupVarTyId = IsaCommonTerms.TermIdentFromName("lookup_var_ty");
        private readonly static TermIdent localStateId = IsaCommonTerms.TermIdentFromName("local_state");
        private readonly static TermIdent globalStateId = IsaCommonTerms.TermIdentFromName("global_state");
        private readonly static TermIdent binderStateId = IsaCommonTerms.TermIdentFromName("binder_state");

        private readonly static TermIdent redCfgMultiId = IsaCommonTerms.TermIdentFromName("red_cfg_multi");
        private readonly static TermIdent redCmdListId = IsaCommonTerms.TermIdentFromName("red_cmd_list");
        private readonly static TermIdent redExprId = IsaCommonTerms.TermIdentFromName("red_expr");
        private readonly static TermIdent normalStateId = IsaCommonTerms.TermIdentFromName("Normal");
        private readonly static TermIdent magicStateId = IsaCommonTerms.TermIdentFromName("Magic");
        private readonly static TermIdent failureStateId = IsaCommonTerms.TermIdentFromName("Failure");

        private readonly static TermIdent outEdgesId = IsaCommonTerms.TermIdentFromName("out_edges");
        private readonly static TermIdent nodeToBlockId = IsaCommonTerms.TermIdentFromName("node_to_block");
        
        public static TermIdent ConvertValToBoolId { get; }= IsaCommonTerms.TermIdentFromName("convert_val_to_bool");
        public static TermIdent ConvertValToIntId { get;  }= IsaCommonTerms.TermIdentFromName("convert_val_to_int");
        private readonly static TermIdent funInterpWfId = IsaCommonTerms.TermIdentFromName("fun_interp_wf");
        private readonly static TermIdent funInterpSingleWfId = IsaCommonTerms.TermIdentFromName("fun_interp_single_wf");
        private readonly static TermIdent stateWfId = IsaCommonTerms.TermIdentFromName("state_typ_wf");
        private readonly static TermIdent axiomsSatId = IsaCommonTerms.TermIdentFromName("axioms_sat");

        private readonly static TermIdent typeOfValId = IsaCommonTerms.TermIdentFromName("type_of_val");

        private readonly static TermIdent forallId = IsaCommonTerms.TermIdentFromName("Forall");
        private readonly static TermIdent existsId = IsaCommonTerms.TermIdentFromName("Exists");
        private readonly static TermIdent forallTypeId = IsaCommonTerms.TermIdentFromName("ForallT");
        private readonly static TermIdent existsTypeId = IsaCommonTerms.TermIdentFromName("ExistsT");

        private readonly static TermIdent closedTypeId = IsaCommonTerms.TermIdentFromName("closed");
        private readonly static TermIdent instTypeId = IsaCommonTerms.TermIdentFromName("instantiate");

        private readonly static TermIdent axiomAssmId = IsaCommonTerms.TermIdentFromName("axiom_assm");

        //TODO initialize all the default constructors, so that they only need to be allocated once (Val, Var, etc...)

        public static Term ExprFromLiteral(Term lit)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Lit"), new List<Term>() { lit });
        }

        public static Term Var(string v)
        {
            Term stringConst = new StringConst(v);
            return new TermApp(IsaCommonTerms.TermIdentFromName("Var"), new List<Term>() { stringConst });
        }

        public static Term VariableConstr(int i, bool isBoundVar)
        {
            Contract.Requires(i >= 0);
            Term natConst = new NatConst(i);
            if(!isBoundVar)
                return new TermApp(varId, new List<Term>() { natConst });
                
            return new TermApp(bvarId, new List<Term>() { natConst });
        }

        public static Term BVar(int i)
        {
            Contract.Requires(i >= 0);
            Term natConst = new NatConst(i);
            return new TermApp(IsaCommonTerms.TermIdentFromName("BVar"), new List<Term>() { natConst });
        }

        public static Term Literal(LiteralExpr node)
        {
            if (node.Type.IsBool)
            {
               return BoolLiteral(node.asBool);
            }
            else if (node.Type.IsInt)
            {
                return IntLiteral(node.asBigNum);
            } else
            {
                throw new NotImplementedException();
            }
        }

        public static Term IntLiteral(Microsoft.BaseTypes.BigNum num)
        {
            return new TermApp(intLitId, new IntConst(num));
        }

        public static Term IntValConstr()
        {
            return intVId;
        }

        public static Term IntVal(Microsoft.BaseTypes.BigNum num)
        {
            Term intConst = new IntConst(num);
            return IntVal(intConst);
        }

        public static Term IntVal(Term i)
        {
            return new TermApp(intVId, new List<Term>() { i });
        }

        public static Term BoolLiteral(bool b)
        {
            return new TermApp(boolLitId, new BoolConst(b));
        }
        
        public static Term BoolValConstr()
        {
            return boolVId;
        }

        public static Term BoolVal(bool b)
        {
            Term boolConst = new BoolConst(b);
            return BoolVal(boolConst);
        }

        public static Term BoolVal(Term b)
        {
            return new TermApp(boolVId, b );
        }

        public static Term LookupVar(Term varContext, Term normalState, Term var)
        {
            return new TermApp(lookupVarId, new List<Term> {varContext, normalState, var});
        }
        
        public static Term LookupVarTy(Term varContext, Term var)
        {
            return new TermApp(lookupVarTyId, new List<Term> {varContext, var});
        }
        
        public static Term LocalState(Term normalState)
        {
            return new TermApp(localStateId, normalState);
        }

        public static Term GlobalState(Term normalState)
        {
            return new TermApp(globalStateId, normalState);
        }
        
        public static Term BinderState(Term normalState)
        {
            return new TermApp(binderStateId, normalState);
        }
        
        public static Term Assert(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assert"), new List<Term>() { arg });
        }

        public static Term Assume(Term arg)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assume"), new List<Term>() { arg });
        }


        public static Term Assign(Term lhsTerm, Term rhsTerm)
        {
            return new TermApp(IsaCommonTerms.TermIdentFromName("Assign"), new List<Term> { lhsTerm, rhsTerm });
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

        //value quantification

        /*
         * if isForall is false, then it must be an existential quantifier
         * */
        public static Term Quantifier(bool isForall, Term boundVarType, Term body)
        {
            return isForall ? Forall(boundVarType, body) : Exists(boundVarType, body);
        }

        public static Term Forall(Term boundVarType, Term body)
        {
            return new TermApp(forallId, new List<Term> { boundVarType, body });
        }

        public static Term Exists(Term boundVarType, Term body)
        {
            return new TermApp(existsId, new List<Term> { boundVarType, body });
        }

        //type quantification

        public static Term TypeQuantifier(bool isForall, Term body)
        {
            return isForall ? ForallType(body) : ExistsType(body);
        }

        public static Term ForallType(Term body)
        {
            return new TermApp(forallTypeId, new List<Term> { body });
        }

        public static Term ExistsType(Term body)
        {
            return new TermApp(existsTypeId, new List<Term> { body });
        }

        public static Term FunCall(string fname, IList<Term> typeArgs, IList<Term> args)
        {
            var wrapTypeArgs = new TermList(typeArgs);
            var wrapArgs = new TermList(args);
            var fnameAndArgs = new List<Term>() { new StringConst(fname), wrapTypeArgs, wrapArgs };

            return new TermApp(IsaCommonTerms.TermIdentFromName("FunExp"), fnameAndArgs);
        }

        public static Term MethodCFGBody(Term entryNode, Term outEdges, Term nodeToBlock)
        {
            var mapping =
                new List<Tuple<string, Term>>()
                {
                    new Tuple<string, Term>("entry", entryNode),
                    new Tuple<string, Term>("out_edges", outEdges),
                    new Tuple<string, Term>("node_to_block", nodeToBlock)
                };

            return new TermRecord(mapping);
        }

        public static Term OutEdges(Term cfg, int idx)
        {
            return IsaCommonTerms.ListLookup(new TermApp(outEdgesId, cfg), idx);
        }

        public static Term NodeToBlock(Term cfg, int idx)
        {
            return IsaCommonTerms.ListLookup(new TermApp(nodeToBlockId, cfg), idx);
        }
        
        public static Term Method(string methodName, 
            int numTypeParams, 
            Term parameters, 
            Term localVars, 
            Term modifiedVariables, 
            Term pres, 
            Term posts, 
            Term methodCFGBody)
        {
            var elements =
                new List<Term>()
                {
                    new StringConst(methodName),
                    new NatConst(numTypeParams),
                    parameters,
                    localVars,
                    modifiedVariables,
                    new TermTuple(new List<Term>() {pres, posts}),
                    methodCFGBody
                };

            return new TermTuple(elements);                            
        }

        public static Term Program(Term fdecls, Term constantDecls, Term globalDecls, Term axioms, List<Term> mdecls)
        {
            Term mdeclsTerm = new TermList(mdecls);

            return new TermApp(IsaCommonTerms.TermIdentFromName("Program"), 
                new List<Term>() { new TermList(new List<Term>()), fdecls, constantDecls, globalDecls, axioms, mdeclsTerm });
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

        public static Term RedCmdList(BoogieContextIsa boogieContext, Term cmdList, Term initState, Term finalState)
        {
            return
                new TermApp(redCmdListId,
                new List<Term>()
                {
                    boogieContext.absValTyMap,
                    boogieContext.methodContext,
                    boogieContext.varContext,
                    boogieContext.funContext,
                    boogieContext.rtypeEnv,
                    cmdList,
                    initState,
                    finalState
                }
                );
        }

        public static Term RedCFGMulti(BoogieContextIsa boogieContext, Term cfg, Term initCFGConfig, Term finalCFGConfig)
        {
            return
                new TermApp(redCfgMultiId,
                new List<Term>()
                {
                    boogieContext.absValTyMap,
                    boogieContext.methodContext,
                    boogieContext.varContext,
                    boogieContext.funContext,
                    boogieContext.rtypeEnv,
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

        public static Term RedExpr(BoogieContextIsa boogieContext, Term expr, Term state, Term resultValue)
        {
            return
                new TermApp(redExprId,
                new List<Term>()
                {
                    boogieContext.absValTyMap,
                    boogieContext.funContext,
                    boogieContext.rtypeEnv,
                    expr,
                    state,
                    resultValue
                });
        }

        public static Term FunDecl(Function f, IVariableTranslationFactory varTranslationFactory, bool includeName=true)
        {
            var typeIsaVisitor = LemmaHelper.FunTypeIsaVisitor(f, varTranslationFactory);

            Term fname = new StringConst(f.Name);
            Term numTypeParams = new NatConst(f.TypeParameters.Count);
            var argTypes = new TermList(f.InParams.Select(v => typeIsaVisitor.Translate(v.TypedIdent.Type)).ToList());
            var retType = typeIsaVisitor.Translate(f.OutParams.First().TypedIdent.Type);
            if(includeName)
            {
                return new TermTuple(new List<Term> { fname, numTypeParams, argTypes, retType });
            } else
            {
                return new TermTuple(new List<Term> { numTypeParams, argTypes, retType });
            }
        }

        public static Term VarDecl(Variable v, TypeIsaVisitor typeIsaVisitor, bool includeName=true)
        {
            Term vName = new StringConst(v.Name);
            Term vType = typeIsaVisitor.Translate(v.TypedIdent.Type);
            if(includeName)
            {
                return new TermTuple(new List<Term> { vName, vType });
            } else
            {
                return vType;
            }
        }

        public static Term ConvertValToBool(Term val)
        {
            return new TermApp(ConvertValToBoolId, val);
        }

        public static Term ConvertValToInt(Term val)
        {
            return new TermApp(ConvertValToIntId, val);
        }

        public static Term TypeToVal(Term absValTyMap, Term value)
        {
            return new TermApp(new TermApp(typeOfValId, absValTyMap), value);
        }

        public static Term FunInterpWf(Term absValTyMap, Term fdecls, Term finterp)
        {
            return new TermApp(funInterpWfId, new List<Term> { absValTyMap, fdecls, finterp });
        }

        public static Term FunInterpSingleWf(Function f, Term absValTyMap, Term fTerm, IVariableTranslationFactory factory)
        {
            return FunInterpSingleWf(absValTyMap, FunDecl(f, factory), fTerm);
        }

        public static Term FunInterpSingleWf(Term absValTyMap, Term fdecl, Term fun)
        {
            return new TermApp(funInterpSingleWfId, new List<Term> { absValTyMap, fdecl, fun });
        }

        public static Term StateWf(Term absValTyMap, Term typeEnv, Term vdecls, Term normalState)
        {
            return new TermApp(stateWfId, new List<Term> { absValTyMap, typeEnv, normalState, vdecls });
        }

        public static Term AxiomSat(Term absValTyMap, Term varContext, Term funContext, Term axioms, Term normalState)
        {
            return new TermApp(axiomsSatId, new List<Term> { absValTyMap, varContext, funContext, normalState, axioms });
        }

        public static Term AxiomAssm(Term absValTyMap, Term funContext, Term consts, Term normalState, Term axioms)
        {
            return new TermApp(axiomAssmId, absValTyMap, funContext, consts, normalState, axioms);
        }

        public static Term IsClosedType(Term ty)
        {
            return new TermApp(closedTypeId, ty);
        }

        public static Term InstantiateType(Term rtypeEnv, Term ty)
        {
            return new TermApp(instTypeId, rtypeEnv, ty);
        }
    }
}

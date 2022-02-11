using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration
{

    /// <summary>
    /// Rewrites maps in AST. Type checking must already have happened, otherwise type won't be present.
    /// </summary>
    internal class MapDesugaringVisitor : StandardVisitor
    {
        /*
        private IDictionary<MapType, AbstractMapTypeData> mapTypeConstructorDict;
        private IDictionary<TypeCtorDecl, MapType> mapTypeConstructorReverseDict;
        */

        //TODO: name clash with existing types
        private readonly string baseName = "MapType";
        private int index = 0;
        
        private FrontendMapAbstractionBuilder _mapAbstractionBuilder;
        
        public Program Desugar(Program p, FrontendMapAbstractionBuilder mapAbstractionBuilder)
        {
            _mapAbstractionBuilder = mapAbstractionBuilder;
            var desugaredProg = VisitProgram(p);

            foreach (var decl in _mapAbstractionBuilder.AllAbstractions())
            {
                p.AddTopLevelDeclaration(decl);
            }
            
            foreach (var f in _mapAbstractionBuilder.AllSelectAndStoreFunctions())
            {
                p.AddTopLevelDeclaration(f);
            }
            
            int tcErrorCount = desugaredProg.Typecheck();
            if (tcErrorCount != 0)
            {
                throw new Exception("Type check failed after desugaring program");
            }
            
            return desugaredProg;
        }

        /// <summary>
        /// Instantiate function call with identifier instead of function itself, which forces any subsequent resolution
        /// to be executed again.
        /// </summary>
        private static FunctionCall FunCallWithId(Function f)
        {
            return new FunctionCall(new IdentifierExpr(Token.NoToken, f.Name));
        }

        
        //if we don't override this, then VisitMapType will be invoked which must return a MapType
        public override Absy Visit(Absy node)
        {
            if (node is MapType mapType)
            {
                return _mapAbstractionBuilder.AbstractMapType(mapType);
            }
            

            return base.Visit(node);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl != null)
            {
                node.Decl = this.VisitVariable(node.Decl);
                /* need to update type (otherwise subsequent type check will fail, since IdentifierExpr and Decl are not 
                   in-sync */
                node.Type = node.Decl.TypedIdent.Type;
            }
            
            return node;
        }

        public override MapType VisitMapType(MapType node)
        {
            throw new cce.UnreachableException();
        }
        
        /// <summary>
        /// input type should be a map type or a constructor type that was generated for a map
        /// </summary>
        private MapType TranslateToMapType(Type type)
        {
            if(type.IsMap) {
                return type.AsMap;
            }
            if(type.IsCtor)
            {
                CtorType ctorType = type.AsCtor;
                return _mapAbstractionBuilder.RawType(ctorType.Decl);
            } 
            
            throw new cce.UnreachableException();
        }
        
        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            if(node.Lhss.Count > 1)
                throw new NotImplementedException("Do not support multiple left hand sides");


            if (node.Lhss.First() is MapAssignLhs mapAssignLhs)
            {
                Expr storedExpr = VisitExpr(node.Rhss.First());

                if(!(mapAssignLhs.Map is SimpleAssignLhs))
                    throw new NotImplementedException("Do not support non-simple lhs within a MapAssignLhs");

                var map = VisitSimpleAssignLhs(mapAssignLhs.Map as SimpleAssignLhs);
                node.Lhss = new List<AssignLhs> { map };

                var storeFunArgs = new List<Expr> { map.AsExpr };
                
                foreach (var t in mapAssignLhs.Indexes)
                    storeFunArgs.Add(this.VisitExpr(t));
                
                storeFunArgs.Add(storedExpr);

                node.Rhss = new List<Expr>
                {
                    new NAryExpr(
                        Token.NoToken,
                        new FunctionCall(_mapAbstractionBuilder.Store(TranslateToMapType(mapAssignLhs.Map.Type))),
                        storeFunArgs
                        )
                };
                
                return node;
            }
                
            return base.VisitAssignCmd(node);
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            node.Args = VisitExprSeq(node.Args);
            if (node.Fun is MapSelect || node.Fun is MapStore)
            {
                var mapType = TranslateToMapType(node.Args[0].Type);
                var newFun = node.Fun is MapSelect
                    ? _mapAbstractionBuilder.Select(mapType)
                    : _mapAbstractionBuilder.Store(mapType); 
                node.Fun = new FunctionCall(newFun);
            } else if (node.Fun is TypeCoercion coercion)
            {
                coercion.Type = (Type) Visit(coercion.Type);
            }
            
            //we delete the type parameters, since they might have changed (this forces the subsequent type checking phase to fill in the holes)
            node.TypeParameters = null;

            return node;
        }

    }
}
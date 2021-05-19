using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.TypeErasure;
using Type = Microsoft.Boogie.Type;

namespace ProofGeneration
{
    /// <summary>
    /// Provides interface to abstract map types with type constructors. Many parts of this class are duplicated from
    /// <see cref="MapTypeAbstractionBuilder"/>.
    /// </summary>
    // TODO: Try to merge with MapTypeAbstractionBuilder
    public class FrontendMapAbstractionBuilder
    {
        private readonly IList<TypeVariable> abstractionVariables = new List<TypeVariable>();
        private readonly IDictionary<MapType, MapTypeClassRepresentation> classRepresentations = new Dictionary<MapType, MapTypeClassRepresentation>();
        private readonly IDictionary<MapType, Tuple<MapType, CtorType> > rawToAbstractType = new Dictionary<MapType, Tuple<MapType, CtorType> >();
        private readonly IDictionary<TypeCtorDecl, MapType> reprToRawType  = new Dictionary<TypeCtorDecl, MapType>();
        
        private readonly Predicate<MapType> useUniqueType;

        /// <summary>
        /// Initializes a new instance of the <see cref="FrontendMapAbstractionBuilder"/> class.
        /// </summary>
        /// <param name="useUniqueType">Use to indicate whether a maptype ocurring in the original program should be represented by a unique type constructor that
        /// is not shared with other map types that are comparable. It must hold that the predicate is true only if the input has no free type variables and when
        /// there is no other map type in the program that is comparable.
        /// </param>
        protected FrontendMapAbstractionBuilder(Predicate<MapType> useUniqueType)
        {
            this.useUniqueType = useUniqueType;
        }

        public FrontendMapAbstractionBuilder()
        {
            this.useUniqueType = mapType => false;
        }
          
        /// <summary>
        /// Creates a new instance of the <see cref="FrontendMapAbstractionBuilder"/> class, where "unique" map types are
        /// represented by separate type constructors.
        /// A unique map type is a map type that has been recorded in the existing instance and for which no comparable
        /// map type has been recorded.
        /// The resulting instance should only be used if the existing map type has recorded all map types.
        /// </summary>
        public FrontendMapAbstractionBuilder UniqueAbstractionBuilder()
        {
            var numOfMapTypes =
                new Dictionary<MapType, int>();
            foreach (var kv in rawToAbstractType)
            {
                if (numOfMapTypes.TryGetValue(kv.Value.Item1, out int counter))
                {
                    numOfMapTypes[kv.Value.Item1] = counter + 1;
                }
                else
                {
                    numOfMapTypes[kv.Value.Item1] = 1;
                }
            }

            var set = new HashSet<MapType>();

            foreach (var kv in rawToAbstractType)
            {
              if (numOfMapTypes[kv.Value.Item1] == 1 && !kv.Key.FreeVariables.Any())
              {
                set.Add(kv.Key);
              }
            }

            return new FrontendMapAbstractionBuilder(set.Contains);
        }

        public IEnumerable<Function> AllSelectAndStoreFunctions()
        {
          var result = new List<Function>();

          foreach (var repr in classRepresentations.Values)
          {
            result.Add(repr.Select);
            result.Add(repr.Store);
          }

          return result;
        }

        public IEnumerable<TypeCtorDecl> AllAbstractions()
        {
          var result = new HashSet<TypeCtorDecl>();
          foreach (var repr in classRepresentations.Values)
          {
            result.Add(repr.RepresentingType);
          }
          return result;
        }

        private Function SelectFun(MapType m, TypeCtorDecl ctorDecl)
        {
          var ctorTypeParams = m.FreeVariables.Select(tv => (Type) tv).ToList();
          var ctorType = new CtorType(Token.NoToken, ctorDecl, ctorTypeParams);
          var valueTypes = new List<Type> { ctorType };
          valueTypes.AddRange(m.Arguments);
          valueTypes.Add(m.Result);

          List<TypeVariable> typeParams = new List<TypeVariable> (m.TypeParameters);
          typeParams.AddRange(m.FreeVariables);
          return HelperFuns.BoogieFunction("select_" + ctorDecl.Name, typeParams, valueTypes.ToArray());
        }
        
        private Function StoreFun(MapType m, TypeCtorDecl ctorDecl)
        {
          var ctorTypeParams = m.FreeVariables.Select(tv => (Type) tv).ToList();
          var ctorType = new CtorType(Token.NoToken, ctorDecl, ctorTypeParams);
          var valueTypes = new List<Type> { ctorType };
          valueTypes.AddRange(m.Arguments);
          valueTypes.Add(m.Result);
          valueTypes.Add(ctorType);
          
          List<TypeVariable> typeParams = new List<TypeVariable> (m.TypeParameters);
          typeParams.AddRange(m.FreeVariables);
          
          return HelperFuns.BoogieFunction("store_" + ctorDecl.Name, typeParams, valueTypes.ToArray());
        }
    
        private TypeVariable AbstractionVariable(int num)
        {
          while (abstractionVariables.Count <= num)
            abstractionVariables.Add(new TypeVariable(Token.NoToken,
              "aVar" + abstractionVariables.Count));
          return abstractionVariables[num];
        }
        
        ///////////////////////////////////////////////////////////////////////////
        // The untyped representation of a class of map types, i.e., of a map type
        // <a0, a1, ...>[A0, A1, ...] R, where the argument types and the result type
        // possibly contain free type variables. For each such class, a separate type
        // constructor and separate select/store functions are introduced.
        protected readonly struct MapTypeClassRepresentation
        {
          public readonly TypeCtorDecl RepresentingType;
    
          public readonly Function Select;
    
          public readonly Function Store;
    
          public MapTypeClassRepresentation(TypeCtorDecl representingType, Function select, Function store)
          {
            RepresentingType = representingType;
            Select = select;
            Store = store;
          }
        }
    
        protected MapTypeClassRepresentation GetClassRepresentation(MapType abstractedType, MapType rawType)
        {
          MapTypeClassRepresentation res;
          if (!classRepresentations.TryGetValue(abstractedType, out res))
          {
            int num = classRepresentations.Count;
            TypeCtorDecl /*!*/
              synonym =
                new TypeCtorDecl(Token.NoToken, "MapType" + num, abstractedType.FreeVariables.Count);
    
            Function select, store;
            GenSelectStoreFunctions(abstractedType, synonym, out select, out store);
    
            res = new MapTypeClassRepresentation(synonym, select, store);
            classRepresentations.Add(abstractedType, res);
            reprToRawType.Add(synonym, rawType);
          }
    
          return res;
        }

        MapTypeClassRepresentation GetRepresentation(MapType rawType, out CtorType ctorType)
        {
          if (!rawToAbstractType.TryGetValue(rawType, out Tuple<MapType, CtorType> res))
          {
            MapType abstraction = rawType;
            List<Type> instantiation = new List<Type>();
            if (!useUniqueType(rawType))
            {
                abstraction = ThinOutMapType(rawType, out instantiation);
            }
            else
            {
                /* do not create any holes if a unique abstraction should be used for the raw type: abstraction is just
                 the maptype where inputs/outputs are abstracted*/
                abstraction = ThinOutMapType(rawType, out _, false);
            }

            var repr = GetClassRepresentation(abstraction, rawType);

            //need to make sure each the maps contained in the instantiation are desugared
            var instantiationDesugared = instantiation.Select(inst => 
            ThinOutType(inst, new List<TypeVariable>(), new List<Type>(), false)).ToList();
            ctorType = new CtorType(Token.NoToken, repr.RepresentingType, instantiationDesugared);

            rawToAbstractType.Add(rawType, Tuple.Create(abstraction, ctorType));
            return repr;
          }

          ctorType = res.Item2;
          return GetClassRepresentation(res.Item1, rawType);
        }

        private void GenSelectStoreFunctions(MapType abstractedType, TypeCtorDecl synonym, out Function select, out Function store)
        {
            select = SelectFun(abstractedType, synonym);
            store = StoreFun(abstractedType, synonym);
        }

        public MapType RawType(TypeCtorDecl decl)
        {
          return reprToRawType[decl];
        }
        
        public Function Select(MapType rawType)
        { 
          return GetRepresentation(rawType, out _).Select;
        }

        public Function Store(MapType rawType)
        {
          return GetRepresentation(rawType, out _).Store;
        }
        
        public CtorType AbstractMapType(MapType rawType)
        { 
          GetRepresentation(rawType, out CtorType result);
          return result;
        }

        protected MapType ThinOutMapType(MapType rawType, out List<Type> instantiation, bool thin=true)
        {
            instantiation = new List<Type>();
            return ThinOutMapType(rawType, instantiation, thin);
        }
    
        protected MapType ThinOutMapType(MapType rawType, List<Type> instantiations, bool thin=true)
        {
          List<Type> /*!*/
            newArguments = new List<Type>();
          foreach (Type /*!*/ subtype in rawType.Arguments.ToList())
          {
            newArguments.Add(ThinOutType(subtype, rawType.TypeParameters,
              instantiations, thin));
          }
    
          Type /*!*/
            newResult = ThinOutType(rawType.Result, rawType.TypeParameters,
              instantiations, thin);
          return new MapType(Token.NoToken, rawType.TypeParameters, newArguments, newResult);
        }

        /// <summary>
        /// Returns a version of <paramref name="rawType"/> that abstracts away the maps.
        /// If <paramref name="thin"/> is true, then it does so by returning the most general template of <paramref name="rawType"/>,
        /// which may contain fresh type variables (for the "holes")
        /// A template is a type for which the free variables can be substituted to get <paramref name="rawType"/>.
        /// A template is most general, if it is a template for any other template of <paramref name="rawType"/>.
        /// Moreover, expresses all map types in the template directly via their abstractions.
        /// In this case, <paramref name="instantiations"/> returns the substitution to obtain <paramref name="rawType"/>
        /// from the template.
        ///
        /// If <paramref name="thin"/> is false, then the concrete desugared translation, where all maps in
        /// <paramref name="rawType"/> are desugared, is returned.
        /// </summary>
        private Type /*!*/ ThinOutType(Type rawType, List<TypeVariable> boundTypeParams, List<Type> instantiations, bool thin=true)
        {
          if (rawType.FreeVariables.All(var => !boundTypeParams.Contains(var)))
          {
            if (thin)
            {
              // Bingo!
              // if the type does not contain any bound variables, we can simply
              // replace it with a type variable
              TypeVariable /*!*/
                abstractionVar = AbstractionVariable(instantiations.Count);
              instantiations.Add(rawType);
              return abstractionVar;
            }
          } 
    
          if (rawType.IsVariable)
          {
            //
            // then the variable has to be bound, we cannot do anything
            TypeVariable /*!*/
              rawVar = rawType.AsVariable;
            return rawVar;
            //
          }
          else if (rawType.IsMap)
          {
            //
            // recursively abstract this map type and continue abstracting
            CtorType /*!*/
              abstraction = AbstractMapType(rawType.AsMap);
            return ThinOutType(abstraction, boundTypeParams, instantiations, thin);
            //
          }
          else if (rawType.IsCtor)
          {
            //
            // traverse the subtypes
            CtorType /*!*/
              rawCtorType = rawType.AsCtor;
            List<Type> /*!*/
              newArguments = new List<Type>();
            foreach (Type /*!*/ subtype in rawCtorType.Arguments.ToList())
            {
              newArguments.Add(ThinOutType(subtype, boundTypeParams,
                instantiations, thin));
            }
    
            return new CtorType(Token.NoToken, rawCtorType.Decl, newArguments);
            //
          }
          else if (!thin)
          {
            //can reach this case, since types are not abstracted away
            return rawType;
          }
          else
          {
            System.Diagnostics.Debug.Fail("Don't know how to handle this type: " + rawType);
            return rawType; // compiler appeasement policy
          }
        }
    }
}
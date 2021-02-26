using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using ProofGeneration.Isa;

namespace ProofGeneration.VCProofGen
{
    //instantiates vc definitions correctly
    public class VCInstantiation<T>
    {
        private readonly string localeName;

        //objects are only parameterized by those declarations which appear in them
        private readonly IDictionary<T, IList<NamedDeclaration>> objToDecls;

        private readonly IDictionary<T, DefDecl> objToDef;

        public VCInstantiation(
            IDictionary<T, DefDecl> objToDef,
            IDictionary<T, IList<NamedDeclaration>> objToDecls) : this(objToDef, objToDecls, "")
        {
        }

        public VCInstantiation(
            IDictionary<T, DefDecl> objToDef,
            IDictionary<T, IList<NamedDeclaration>> objToDecls,
            string localeName)
        {
            Contract.Requires(objToDef != null);
            Contract.Requires(objToDecls != null);
            Contract.Requires(localeName != null);

            this.objToDef = objToDef;
            this.objToDecls = objToDecls;
            this.localeName = localeName;
        }

        public IEnumerable<T> Keys => objToDef.Keys;

        public Term GetVCObjInstantiation(T obj, IDictionary<NamedDeclaration, Term> declToVC)
        {
            return GetVCObjInstantiation(obj, decl => declToVC[decl]);
        }

        public Term GetVCObjInstantiation(T obj, Func<NamedDeclaration, Term> declToVC)
        {
            if (!objToDef.ContainsKey(obj))
            {
                throw new ProofGenUnexpectedStateException(GetType(), "block unknown by vc");
            }

            var activeDecls = objToDecls[obj];

            IList<Term> args = new List<Term>();
            foreach (var decl in activeDecls)
            {
                args.Add(declToVC(decl));
            }

            return new TermApp(GetVCObjRef(obj), args);
        }

        public IList<NamedDeclaration> GetVCObjParameters(T obj)
        {
            if (!objToDecls.ContainsKey(obj))
            {
                throw new ProofGenUnexpectedStateException(GetType(), "block unknown by vc");
            }

            return objToDecls[obj];
        }

        public Term GetVCObjRef(T block, bool qualified = true)
        {
            Contract.Requires(block != null);
            Contract.Requires(objToDef.ContainsKey(block));

            return IsaCommonTerms.TermIdentFromName(GetVCObjNameRef(block, qualified));
        }

        public string GetVCObjNameRef(T block, bool qualified = true)
        {
            Contract.Requires(block != null);
            Contract.Requires(objToDef.ContainsKey(block));

            var prefix = qualified && localeName.Count() > 0 ? localeName + "." : "";

            return prefix + objToDef[block].name;
        }
    }
}
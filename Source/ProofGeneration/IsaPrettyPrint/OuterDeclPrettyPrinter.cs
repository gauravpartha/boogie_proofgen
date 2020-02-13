﻿using ProofGeneration.Isa;
using System;
using System.Text;

namespace ProofGeneration.IsaPrettyPrint
{
    //return value is ignored
    public class OuterDeclPrettyPrinter : OuterDeclVisitor<int>
    {
        StringBuilder _sb
        {
            get;
        }

        TermPrettyPrinter _termPrinter
        {
            get;
        }

        TypeIsaPrettyPrinter _typeIsaPrinter
        {
            get;
        }

        public OuterDeclPrettyPrinter(StringBuilder sb, TermPrettyPrinter termPrinter, TypeIsaPrettyPrinter typeIsaPrinter)
        {
            _sb = sb;
            _termPrinter = termPrinter;
            _typeIsaPrinter = typeIsaPrinter;
        }

        public override int VisitDefDecl(DefDecl d)
        {
            _sb.Append("definition ").Append(d.name);
            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(1)).Append("where");
            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(2));

            string args = IsaPrettyPrinterHelper.SpaceAggregate(_termPrinter.VisitList(d.equation.Item1));

            AppendInner(
               () => _sb.Append(d.name).Append(" ").Append(args).Append(" = ").Append(_termPrinter.Visit(d.equation.Item2))
            );

            return 0;
        }

        public override int VisitFunDecl(FunDecl d)
        {
            _sb.Append("fun ").Append(d.name);
            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(1)).Append("where");

            bool first = true;
            foreach (var tuple in d.equations)
            {
                _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(2));

                if (first)
                {
                    first = !first;
                }
                else
                {
                    _sb.Append("|");
                }

                string args = IsaPrettyPrinterHelper.SpaceAggregate(_termPrinter.VisitList(tuple.Item1));

                AppendInner( () =>
                    _sb.Append(d.name).Append(" ").Append(args).Append(" = ").Append(_termPrinter.Visit(tuple.Item2))
                );
            }
            return 0;
        }

        public override int VisitLemmaDecl(LemmaDecl d)
        {
            _sb.Append("lemma ").Append(d.name).Append(":");
            _sb.AppendLine();

            PrintContextElem(d.contextElem);

            _sb.AppendLine();

            _sb.Append("shows ");
            AppendInner(_termPrinter.Visit(d.statement));

            _sb.AppendLine();
            PrintProof(d.proof);

            return 0;
        }

        public override int VisitLocaleDecl(LocaleDecl d)
        {            
            _sb.Append("locale ").Append(d.name).Append(" = ");
            _sb.AppendLine();

            PrintContextElem(d.contextElem);

            _sb.AppendLine();
            _sb.Append("begin");
            _sb.AppendLine(); _sb.AppendLine();

            foreach (DefDecl def in d.body)
            {
                def.Dispatch(this);
                _sb.AppendLine();
            }

            _sb.AppendLine();            

            _sb.AppendLine("end");

            return 0;
        }

        public int PrintContextElem(ContextElem c)
        {
            if (c.fixedVariables.Count > 0)
            {
                _sb.Append("fixes ");
                bool first = true;
                foreach (Tuple<TermIdent, TypeIsa> fix in c.fixedVariables)
                {
                    if (first)
                        first = false;
                    else
                        _sb.Append(" and ");

                    _sb.Append(fix.Item1.Dispatch(_termPrinter));
                    _sb.Append(" :: ");
                    AppendInner(fix.Item2.Dispatch(_typeIsaPrinter));
                }
            }

            if (c.assumptions.Count > 0)
            {
                _sb.AppendLine("assumes ");
                bool first = true;

                foreach (Term t in c.assumptions)
                {
                    if (first)
                        first = false;
                    else
                    {                        
                        _sb.Append(" and ");
                        _sb.AppendLine();
                    }


                    AppendInner(t.Dispatch(_termPrinter));
                }
            }

            return 0;
        }

        public void AppendInner(string s)
        {
            _sb.Append("\"");
            _sb.Append(s);
            _sb.Append("\"");
        }

        public void AppendInner(Action action)
        {
            _sb.Append("\"");
            action.Invoke();
            _sb.Append("\"");
        }

        public void PrintProof(Proof p)
        {
            foreach(var m in p.methods) {
                _sb.AppendLine(m);
            }
        }
    }
}

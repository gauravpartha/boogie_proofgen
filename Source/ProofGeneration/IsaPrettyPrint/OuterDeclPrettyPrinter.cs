using System;
using System.Collections.Generic;
using System.Text;
using ProofGeneration.Isa;

namespace ProofGeneration.IsaPrettyPrint
{
    //return value is ignored
    public class OuterDeclPrettyPrinter : OuterDeclVisitor<int>
    {
        public OuterDeclPrettyPrinter(StringBuilder sb, TermPrettyPrinter termPrinter,
            TypeIsaPrettyPrinter typeIsaPrinter)
        {
            _sb = sb;
            _termPrinter = termPrinter;
            _typeIsaPrinter = typeIsaPrinter;
        }

        private StringBuilder _sb { get; }

        private TermPrettyPrinter _termPrinter { get; }

        private TypeIsaPrettyPrinter _typeIsaPrinter { get; }

        public override int VisitDefDecl(DefDecl d)
        {
            return HandleAbbrevOrDef(d, "definition", d.type, "=", d.equation);
        }

        public override int VisitAbbreviationDecl(AbbreviationDecl d)
        {
            return HandleAbbrevOrDef(d, "abbreviation", d.type, "\\<equiv>", d.equation);
        }

        private int HandleAbbrevOrDef(OuterDecl d, string topLevel, TypeIsa type, string equality,
            Tuple<IList<Term>, Term> equation)
        {
            _sb.Append(topLevel + " ").Append(d.name);
            if (type != null)
            {
                _sb.Append(" :: ");
                AppendInner(_typeIsaPrinter.Visit(type));
            }

            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(1)).Append("where");
            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(2));

            var args = _termPrinter.VisitList(equation.Item1).SpaceAggregate();

            AppendInner(
                () => _sb.Append(d.name).Append(" ").Append(args).Append(" " + equality + " ")
                    .Append(_termPrinter.Visit(equation.Item2))
            );

            return 0;
        }

        public override int VisitFunDecl(FunDecl d)
        {
            _sb.Append("fun ");
            _sb.Append(d.name);
            if (d.type != null)
            {
                _sb.Append(" :: ");
                AppendInner(_typeIsaPrinter.Visit(d.type));
            }

            _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(1)).Append("where");

            var first = true;
            foreach (var tuple in d.equations)
            {
                _sb.AppendLine().Append(IsaPrettyPrinterHelper.Indent(2));

                if (first)
                    first = !first;
                else
                    _sb.Append("|");

                var args = _termPrinter.VisitList(tuple.Item1).SpaceAggregate();

                AppendInner(() =>
                    _sb.Append(d.name).Append(" ").Append(args).Append(" = ").Append(_termPrinter.Visit(tuple.Item2))
                );
            }

            return 0;
        }

        public override int VisitLemmaDecl(LemmaDecl d)
        {
            _sb.Append("lemma ").Append(d.name).Append(":");
            if (!d.contextElem.IsEmpty())
            {
                _sb.AppendLine();
                PrintContextElem(d.contextElem);
            }

            _sb.AppendLine();

            _sb.Append("shows ");
            AppendInner(_termPrinter.Visit(d.statement));

            _sb.AppendLine();
            PrintProof(d.proof);

            return 0;
        }

        public override int VisitLemmasDecl(LemmasDecl d)
        {
            _sb.Append("lemmas ").Append(d.name).Append(" = ");
            _sb.Append(d.thmNames.SpaceAggregate());

            return 0;
        }

        public override int VisitLocaleDecl(LocaleDecl d)
        {
            _sb.Append("locale ").Append(d.name);

            if (d.contextElem.fixedVariables.Count > 0 || d.contextElem.assumptions.Count > 0)
            {
                _sb.Append(" = ");
                _sb.AppendLine();
            }

            PrintContextElem(d.contextElem);

            _sb.AppendLine();
            _sb.Append("begin");
            _sb.AppendLine();
            _sb.AppendLine();

            foreach (var decl in d.body)
            {
                decl.Dispatch(this);
                _sb.AppendLine();
            }

            _sb.AppendLine();

            _sb.AppendLine("end");

            return 0;
        }

        public override int VisitDeclareDecl(DeclareDecl d)
        {
            _sb.AppendLine("declare " + d.declaration);
            return 0;
        }

        public override int VisitMLDecl(MLDecl d)
        {
            _sb.Append(d.GetDeclId());
            _sb.Append("\\<open>");
            _sb.AppendLine();
            _sb.Append(d.code);
            _sb.AppendLine();
            _sb.Append("\\<close>");

            return 0;
        }

        public int PrintContextElem(ContextElem c)
        {
            if (c.fixedVariables.Count > 0)
            {
                _sb.Append("fixes ");
                var first = true;
                foreach (var fix in c.fixedVariables)
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
                var useAssmLabels = c.assmLabels.Count == c.assumptions.Count;

                var assmLabelEnumerator = c.assmLabels.GetEnumerator();
                assmLabelEnumerator.MoveNext();

                if (c.fixedVariables.Count > 0)
                    _sb.AppendLine();

                _sb.AppendLine("assumes ");
                var first = true;

                foreach (var t in c.assumptions)
                {
                    if (first)
                    {
                        first = false;
                    }
                    else
                    {
                        _sb.Append(" and ");
                        _sb.AppendLine();
                    }

                    if (useAssmLabels)
                    {
                        _sb.Append(assmLabelEnumerator.Current);
                        _sb.Append(": ");
                        assmLabelEnumerator.MoveNext();
                    }

                    AppendInner(t.Dispatch(_termPrinter));
                }
            }

            return 0;
        }

        public void AppendInner(string s)
        {
            _sb.AppendInner(s);
        }

        public void AppendInner(Action action)
        {
            _sb.AppendInner(action);
        }

        public void PrintProof(Proof p)
        {
            foreach (var m in p.methods) _sb.AppendLine(m);
        }
    }
}
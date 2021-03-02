using System.Text;
using Isabelle.Ast;

namespace Isabelle.IsaPrettyPrint
{
    public static class IsaPrettyPrinter
    {
        public static string PrintTheory(Theory thy)
        {
            var sb = new StringBuilder();

            sb.Append("theory ").Append(thy.TheoryName);
            sb.AppendLine().Append("imports ").Append(thy.ImportTheories.SpaceAggregate());
            sb.AppendLine().Append("begin");
            sb.AppendLine();

            var termPrinter = new TermPrettyPrinter();
            var typeIsaPrinter = new TypeIsaPrettyPrinter();
            var outerDeclPrinter = new OuterDeclPrettyPrinter(sb, termPrinter, typeIsaPrinter);

            foreach (var outerDecl in thy.Decls)
            {
                outerDeclPrinter.Visit(outerDecl);
                sb.AppendLine();
            }

            sb.AppendLine().Append("end");

            return sb.ToString();
        }
    }
}
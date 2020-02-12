using ProofGeneration.Isa;
using System.Text;

namespace ProofGeneration.IsaPrettyPrint
{

    public class IsaPrettyPrinter
    {
        public static string PrintTheory(Theory thy)
        {
            var sb = new StringBuilder();

            sb.Append("theory ").Append(thy.theoryName);
            sb.AppendLine().Append("imports ").Append(IsaPrettyPrinterHelper.SpaceAggregate(thy.importTheories));
            sb.AppendLine().Append("begin");
            sb.AppendLine();

            var termPrinter = new TermPrettyPrinter();
            var typeIsaPrinter = new TypeIsaPrettyPrinter();
            var outerDeclPrinter = new OuterDeclPrettyPrinter(sb, termPrinter, typeIsaPrinter);

            foreach (OuterDecl outerDecl in thy.decls)
            {
                outerDeclPrinter.Visit(outerDecl);
                sb.AppendLine();
            }

            sb.AppendLine().Append("end");

            return sb.ToString();
        }
    }
}

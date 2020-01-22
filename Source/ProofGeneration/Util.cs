using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ProofGeneration
{
    class Util
    {

        static public void Add<T, R>(T key, R val, IDictionary<T, IList<R>> dict)
        {
            IList<R> list;

            bool success = dict.TryGetValue(key, out list);
            if (!success)
            {
                list = new List<R>();
            }

            list.Add(val);
        }

        static public void AddEquation<T>(T lhs, T rhs, IList<Tuple<IList<T>, T>> equations)
        {
            equations.Add(new Tuple<IList<T>, T>(new List<T>() { lhs }, rhs));
        }

    }
}

using System;
using System.Collections.Generic;

namespace ProofGeneration.Util
{
    public static class BasicUtil
    {

        public static void Add<T, R>(T key, R val, IDictionary<T, IList<R>> dict)
        {
            bool success = dict.TryGetValue(key, out IList<R> list);
            if (!success)
            {
                list = new List<R>();
            }

            list.Add(val);
        }

        public static void AddEquation<T>(T lhs, T rhs, IList<Tuple<IList<T>, T>> equations)
        {
            equations.Add(new Tuple<IList<T>, T>(new List<T>() { lhs }, rhs));
        }

        //Taken from https://stackoverflow.com/a/18396163
        public static void ZipDo<T1, T2>(this IEnumerable<T1> first, IEnumerable<T2> second, Action<T1, T2> action)
        {
            using (var e1 = first.GetEnumerator())
            using (var e2 = second.GetEnumerator())
            {
                while (e1.MoveNext() && e2.MoveNext())
                {
                    action(e1.Current, e2.Current);
                }
            }
        }

    }
}

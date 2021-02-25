using System;
using System.Collections.Generic;
using System.Linq;

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

        //Taken from https://stackoverflow.com/a/33104162
        public static void AddRange<T>(this IList<T> list, IEnumerable<T> items)
        {
            if (list == null) throw new ArgumentNullException(nameof(list));
            if (items == null) throw new ArgumentNullException(nameof(items));

            if (list is List<T> asList)
            {
                asList.AddRange(items);
            }
            else
            {
                foreach (var item in items)
                {
                    list.Add(item);
                }
            }
        }

        public static IDictionary<T1,T2> ApplyFunDict<T1,T2>(IEnumerable<T1> items, Func<T1,T2> f)
        {
            var dict = new Dictionary<T1, T2>();
            foreach(var item in items)
            {
                dict.Add(item, f(item));
            }
            return dict;
        }

        public static IDictionary<T2, T1> InverseDict<T1, T2>(this IDictionary<T1, T2> dict)
        {
            return dict.ToDictionary(d => d.Value, d => d.Key);
        }

    }
}

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    class CounterModel
    {
        // 一个比较悲哀的事实是，由于 SMT solver 对 array 的处理方式是将其看做是一个特殊的
        // uninterpreted function，所以在其 model 中可能会是一个比较复杂的表达式。
        // 因此，这里我们没有办法比较好地处理 assign，只能将其都转为字符串。作为一个只是能打印
        // 出来（或许对同学们来说还是非常难以理解的……）的字符串。
        Dictionary<string, string> assignments = default!;

        public CounterModel(Dictionary<string, string> assignments)
        {
            this.assignments = assignments;
        }

        /// <summary> 将这个反例模型打印出来。 </summary>
        /// <remarks> 打印的头尾信息是尽量和 Boogie 保持一致的。 </remarks>
        public void Print(TextWriter writer)
        {
            writer.WriteLine("*** COUNTER MODEL");
            foreach ((string name, string assignment) in assignments)
            {
                writer.WriteLine($"{name} = {assignment}");
            }
            writer.WriteLine("*** END COUNTER MODEL");
        }
    }
}
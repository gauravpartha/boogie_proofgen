using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using System.IO;
using Microsoft.BaseTypes;
using Microsoft.Boogie.ProofGen;
using Microsoft.Boogie.VCExprAST;
using ProofGeneration;
using ProofGeneration.VCProofGen;

namespace VC
{
  using Bpl = Microsoft.Boogie;
  using System.Threading.Tasks;

  public class Split
  {
      public int? RandomSeed => Implementation.RandomSeed ?? CommandLineOptions.Clo.RandomSeed;
    
      class BlockStats
      {
        public bool bigBlock;
        public int id;
        public double assertionCost;
        public double assumptionCost; // before multiplier
        public double incomingPaths;

        public List<Block> /*!>!*/
          virtualSuccessors = new List<Block>();

        public List<Block> /*!>!*/
          virtualPredecessors = new List<Block>();

        public HashSet<Block> reachableBlocks;
        public readonly Block block;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
          Contract.Invariant(cce.NonNullElements(virtualSuccessors));
          Contract.Invariant(cce.NonNullElements(virtualPredecessors));
          Contract.Invariant(block != null);
        }


        public BlockStats(Block b, int i)
        {
          Contract.Requires(b != null);
          block = b;
          assertionCost = -1;
          id = i;
        }
      }

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(cce.NonNullElements(blocks));
        Contract.Invariant(cce.NonNullElements(bigBlocks));
        Contract.Invariant(cce.NonNullDictionaryAndValues(stats));
        Contract.Invariant(cce.NonNullElements(assumizedBranches));
        Contract.Invariant(gotoCmdOrigins != null);
        Contract.Invariant(parent != null);
        Contract.Invariant(Implementation != null);
        Contract.Invariant(copies != null);
        Contract.Invariant(cce.NonNull(protectedFromAssertToAssume));
        Contract.Invariant(cce.NonNull(keepAtAll));
      }


      private readonly List<Block> blocks;
      public readonly IReadOnlyList<Declaration> TopLevelDeclarations;
      readonly List<Block> bigBlocks = new();

      readonly Dictionary<Block /*!*/, BlockStats /*!*/> /*!*/
        stats = new Dictionary<Block /*!*/, BlockStats /*!*/>();

      static int currentId = -1;
      Block splitBlock;
      bool assertToAssume;

      List<Block /*!*/> /*!*/
        assumizedBranches = new List<Block /*!*/>();

      double score;
      bool scoreComputed;
      double totalCost;
      int assertionCount;
      double assertionCost; // without multiplication by paths

      Dictionary<TransferCmd, ReturnCmd> /*!*/
        gotoCmdOrigins;

      readonly public VCGen /*!*/
        parent;

      public Implementation /*!*/ Implementation { get; private set; }

      Dictionary<Block /*!*/, Block /*!*/> /*!*/
        copies = new Dictionary<Block /*!*/, Block /*!*/>();

      bool doingSlice;
      double sliceInitialLimit;
      double sliceLimit;
      bool slicePos;

      HashSet<Block /*!*/> /*!*/
        protectedFromAssertToAssume = new HashSet<Block /*!*/>();

      HashSet<Block /*!*/> /*!*/
        keepAtAll = new HashSet<Block /*!*/>();

      // async interface
      private Checker checker;
      private int splitNum;
      internal VCGen.ErrorReporter reporter;

      public Split(List<Block /*!*/> /*!*/ blocks, Dictionary<TransferCmd, ReturnCmd> /*!*/ gotoCmdOrigins,
        VCGen /*!*/ par, Implementation /*!*/ implementation)
      {
        Contract.Requires(cce.NonNullElements(blocks));
        Contract.Requires(gotoCmdOrigins != null);
        Contract.Requires(par != null);
        Contract.Requires(implementation != null);
        this.blocks = blocks;
        this.gotoCmdOrigins = gotoCmdOrigins;
        this.parent = par;
        this.Implementation = implementation;
        Interlocked.Increment(ref currentId);

        TopLevelDeclarations = par.program.TopLevelDeclarations;
        PrintTopLevelDeclarationsForPruning(par.program, implementation, "before");        
        TopLevelDeclarations = Prune.GetLiveDeclarations(par.program, blocks).ToList();
        PrintTopLevelDeclarationsForPruning(par.program, implementation, "after");
      }

      private void PrintTopLevelDeclarationsForPruning(Program program, Implementation implementation, string suffix)
      {
        if (!CommandLineOptions.Clo.Prune || CommandLineOptions.Clo.PrintPrunedFile == null)
        {
          return;
        }

        using var writer = new TokenTextWriter(
          $"{CommandLineOptions.Clo.PrintPrunedFile}-{suffix}-{Util.EscapeFilename(implementation.Name)}", false,
          CommandLineOptions.Clo.PrettyPrint);
        foreach (var declaration in TopLevelDeclarations ?? program.TopLevelDeclarations) {
          declaration.Emit(writer, 0);
        }

        writer.Close();
      }

      public double Cost
      {
        get
        {
          ComputeBestSplit();
          return totalCost;
        }
      }

      public bool LastChance
      {
        get
        {
          ComputeBestSplit();
          return assertionCount == 1 && score < 0;
        }
      }

      public string Stats
      {
        get
        {
          ComputeBestSplit();
          return $"(cost:{totalCost:0}/{assertionCost:0}{(LastChance ? " last" : "")})";
        }
      }

      public void DumpDot(int splitNum)
      {
        using (System.IO.StreamWriter sw = System.IO.File.CreateText($"{Implementation.Name}.split.{splitNum}.dot"))
        {
          sw.WriteLine("digraph G {");

          ComputeBestSplit();
          List<Block> saved = assumizedBranches;
          Contract.Assert(saved != null);
          assumizedBranches = new List<Block>();
          DoComputeScore(false);
          assumizedBranches = saved;

          foreach (Block b in bigBlocks)
          {
            Contract.Assert(b != null);
            BlockStats s = GetBlockStats(b);
            foreach (Block t in s.virtualSuccessors)
            {
              Contract.Assert(t != null);
              sw.WriteLine("n{0} -> n{1};", s.id, GetBlockStats(t).id);
            }

            sw.WriteLine("n{0} [label=\"{1}:\\n({2:0.0}+{3:0.0})*{4:0.0}\"{5}];",
              s.id, b.Label,
              s.assertionCost, s.assumptionCost, s.incomingPaths,
              s.assertionCost > 0 ? ",shape=box" : "");
          }

          sw.WriteLine("}");
          sw.Close();
        }

        string filename = string.Format("{0}.split.{1}.bpl", Implementation.Name, splitNum);
        using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename))
        {
          int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
          CommandLineOptions.Clo.PrintUnstructured = 2; // print only the unstructured program
          bool oldPrintDesugaringSetting = CommandLineOptions.Clo.PrintDesugarings;
          CommandLineOptions.Clo.PrintDesugarings = false;
          List<Block> backup = Implementation.Blocks;
          Contract.Assert(backup != null);
          Implementation.Blocks = blocks;
          Implementation.Emit(new TokenTextWriter(filename, sw, /*setTokens=*/ false, /*pretty=*/ false), 0);
          Implementation.Blocks = backup;
          CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaringSetting;
          CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }
      }

      int bsid;

      BlockStats GetBlockStats(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<BlockStats>() != null);

        if (!stats.TryGetValue(b, out var s))
        {
          s = new BlockStats(b, bsid++);
          stats[b] = s;
        }

        return cce.NonNull(s);
      }

      double AssertionCost(PredicateCmd c)
      {
        return 1.0;
      }

      void CountAssertions(Block b)
      {
        Contract.Requires(b != null);
        BlockStats s = GetBlockStats(b);
        if (s.assertionCost >= 0)
        {
          return; // already done
        }

        s.bigBlock = true;
        s.assertionCost = 0;
        s.assumptionCost = 0;
        foreach (Cmd c in b.Cmds)
        {
          if (c is AssertCmd)
          {
            double cost = AssertionCost((AssertCmd) c);
            s.assertionCost += cost;
            assertionCount++;
            assertionCost += cost;
          }
          else if (c is AssumeCmd)
          {
            s.assumptionCost += AssertionCost((AssumeCmd) c);
          }
        }

        foreach (Block c in b.Exits())
        {
          Contract.Assert(c != null);
          s.virtualSuccessors.Add(c);
        }

        if (s.virtualSuccessors.Count == 1)
        {
          Block next = s.virtualSuccessors[0];
          BlockStats se = GetBlockStats(next);
          CountAssertions(next);
          if (next.Predecessors.Count > 1 || se.virtualSuccessors.Count != 1)
          {
            return;
          }

          s.virtualSuccessors[0] = se.virtualSuccessors[0];
          s.assertionCost += se.assertionCost;
          s.assumptionCost += se.assumptionCost;
          se.bigBlock = false;
        }
      }

      HashSet<Block /*!*/> /*!*/ ComputeReachableNodes(Block /*!*/ b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(cce.NonNull(Contract.Result<HashSet<Block /*!*/>>()));
        BlockStats s = GetBlockStats(b);
        if (s.reachableBlocks != null)
        {
          return s.reachableBlocks;
        }

        HashSet<Block /*!*/> blocks = new HashSet<Block /*!*/>();
        s.reachableBlocks = blocks;
        blocks.Add(b);
        foreach (Block /*!*/ succ in b.Exits())
        {
          Contract.Assert(succ != null);
          foreach (Block r in ComputeReachableNodes(succ))
          {
            Contract.Assert(r != null);
            blocks.Add(r);
          }
        }

        return blocks;
      }

      double ProverCost(double vcCost)
      {
        return vcCost * vcCost;
      }

      void ComputeBestSplit()
      {
        if (scoreComputed)
        {
          return;
        }

        scoreComputed = true;

        assertionCount = 0;

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          CountAssertions(b);
        }

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          BlockStats bs = GetBlockStats(b);
          if (bs.bigBlock)
          {
            bigBlocks.Add(b);
            foreach (Block ch in bs.virtualSuccessors)
            {
              Contract.Assert(ch != null);
              BlockStats chs = GetBlockStats(ch);
              if (!chs.bigBlock)
              {
                Console.WriteLine("non-big {0} accessed from {1}", ch, b);
                DumpDot(-1);
                Contract.Assert(false);
                throw new cce.UnreachableException();
              }

              chs.virtualPredecessors.Add(b);
            }
          }
        }

        assumizedBranches.Clear();
        totalCost = ProverCost(DoComputeScore(false));

        score = double.PositiveInfinity;
        Block bestSplit = null;
        List<Block> savedBranches = new List<Block>();

        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          GotoCmd gt = b.TransferCmd as GotoCmd;
          if (gt == null)
          {
            continue;
          }

          List<Block> targ = cce.NonNull(gt.labelTargets);
          if (targ.Count < 2)
          {
            continue;
          }
          // caution, we only consider two first exits

          double left0, right0, left1, right1;
          splitBlock = b;

          assumizedBranches.Clear();
          assumizedBranches.Add(cce.NonNull(targ[0]));
          left0 = DoComputeScore(true);
          right0 = DoComputeScore(false);

          assumizedBranches.Clear();
          for (int idx = 1; idx < targ.Count; idx++)
          {
            assumizedBranches.Add(cce.NonNull(targ[idx]));
          }

          left1 = DoComputeScore(true);
          right1 = DoComputeScore(false);

          double currentScore = ProverCost(left1) + ProverCost(right1);
          double otherScore = ProverCost(left0) + ProverCost(right0);

          if (otherScore < currentScore)
          {
            currentScore = otherScore;
            assumizedBranches.Clear();
            assumizedBranches.Add(cce.NonNull(targ[0]));
          }

          if (currentScore < score)
          {
            score = currentScore;
            bestSplit = splitBlock;
            savedBranches.Clear();
            savedBranches.AddRange(assumizedBranches);
          }
        }

        if (CommandLineOptions.Clo.VcsPathSplitMult * score > totalCost)
        {
          splitBlock = null;
          score = -1;
        }
        else
        {
          assumizedBranches = savedBranches;
          splitBlock = bestSplit;
        }
      }

      void UpdateIncommingPaths(BlockStats s)
      {
        Contract.Requires(s != null);
        if (s.incomingPaths < 0.0)
        {
          int count = 0;
          s.incomingPaths = 0.0;
          if (!keepAtAll.Contains(s.block))
          {
            return;
          }

          foreach (Block b in s.virtualPredecessors)
          {
            Contract.Assert(b != null);
            BlockStats ch = GetBlockStats(b);
            Contract.Assert(ch != null);
            UpdateIncommingPaths(ch);
            if (ch.incomingPaths > 0.0)
            {
              s.incomingPaths += ch.incomingPaths;
              count++;
            }
          }

          if (count > 1)
          {
            s.incomingPaths *= CommandLineOptions.Clo.VcsPathJoinMult;
          }
        }
      }

      void ComputeBlockSetsHelper(Block b, bool allowSmall)
      {
        Contract.Requires(b != null);
        if (keepAtAll.Contains(b))
        {
          return;
        }

        keepAtAll.Add(b);

        if (allowSmall)
        {
          foreach (Block ch in b.Exits())
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
            {
              continue;
            }

            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
        else
        {
          foreach (Block ch in GetBlockStats(b).virtualSuccessors)
          {
            Contract.Assert(ch != null);
            if (b == splitBlock && assumizedBranches.Contains(ch))
            {
              continue;
            }

            ComputeBlockSetsHelper(ch, allowSmall);
          }
        }
      }

      void ComputeBlockSets(bool allowSmall)
      {
        protectedFromAssertToAssume.Clear();
        keepAtAll.Clear();

        Debug.Assert(splitBlock == null || GetBlockStats(splitBlock).bigBlock);
        Debug.Assert(GetBlockStats(blocks[0]).bigBlock);

        if (assertToAssume)
        {
          foreach (Block b in allowSmall ? blocks : bigBlocks)
          {
            Contract.Assert(b != null);
            if (ComputeReachableNodes(b).Contains(cce.NonNull(splitBlock)))
            {
              keepAtAll.Add(b);
            }
          }

          foreach (Block b in assumizedBranches)
          {
            Contract.Assert(b != null);
            foreach (Block r in ComputeReachableNodes(b))
            {
              Contract.Assert(r != null);
              if (allowSmall || GetBlockStats(r).bigBlock)
              {
                keepAtAll.Add(r);
                protectedFromAssertToAssume.Add(r);
              }
            }
          }
        }
        else
        {
          ComputeBlockSetsHelper(blocks[0], allowSmall);
        }
      }

      bool ShouldAssumize(Block b)
      {
        Contract.Requires(b != null);
        return assertToAssume && !protectedFromAssertToAssume.Contains(b);
      }

      double DoComputeScore(bool aa)
      {
        assertToAssume = aa;
        ComputeBlockSets(false);

        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          GetBlockStats(b).incomingPaths = -1.0;
        }

        GetBlockStats(blocks[0]).incomingPaths = 1.0;

        double cost = 0.0;
        foreach (Block b in bigBlocks)
        {
          Contract.Assert(b != null);
          if (keepAtAll.Contains(b))
          {
            BlockStats s = GetBlockStats(b);
            UpdateIncommingPaths(s);
            double local = s.assertionCost;
            if (ShouldAssumize(b))
            {
              local = (s.assertionCost + s.assumptionCost) * CommandLineOptions.Clo.VcsAssumeMult;
            }
            else
            {
              local = s.assumptionCost * CommandLineOptions.Clo.VcsAssumeMult + s.assertionCost;
            }

            local = local + local * s.incomingPaths * CommandLineOptions.Clo.VcsPathCostMult;
            cost += local;
          }
        }

        return cost;
      }

      List<Cmd> SliceCmds(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);

        List<Cmd> seq = b.Cmds;
        Contract.Assert(seq != null);
        if (!doingSlice && !ShouldAssumize(b))
        {
          return seq;
        }

        List<Cmd> res = new List<Cmd>();
        foreach (Cmd c in seq)
        {
          Contract.Assert(c != null);
          AssertCmd a = c as AssertCmd;
          Cmd theNewCmd = c;
          bool swap = false;
          if (a != null)
          {
            if (doingSlice)
            {
              double cost = AssertionCost(a);
              bool first = (sliceLimit - cost) >= 0 || sliceInitialLimit == sliceLimit;
              sliceLimit -= cost;
              swap = slicePos == first;
            }
            else if (assertToAssume)
            {
              swap = true;
            }
            else
            {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }

            if (swap)
            {
              theNewCmd = VCGen.AssertTurnedIntoAssume(a);
            }
          }

          res.Add(theNewCmd);
        }

        return res;
      }

      Block CloneBlock(Block b)
      {
        Contract.Requires(b != null);
        Contract.Ensures(Contract.Result<Block>() != null);

        if (copies.TryGetValue(b, out var res))
        {
          return cce.NonNull(res);
        }

        res = new Block(b.tok, b.Label, SliceCmds(b), b.TransferCmd);
        GotoCmd gt = b.TransferCmd as GotoCmd;
        copies[b] = res;
        if (gt != null)
        {
          GotoCmd newGoto = new GotoCmd(gt.tok, new List<String>(), new List<Block>());
          res.TransferCmd = newGoto;
          int pos = 0;
          foreach (Block ch in cce.NonNull(gt.labelTargets))
          {
            Contract.Assert(ch != null);
            Contract.Assert(doingSlice ||
                            (assertToAssume || (keepAtAll.Contains(ch) || assumizedBranches.Contains(ch))));
            if (doingSlice ||
                ((b != splitBlock || assumizedBranches.Contains(ch) == assertToAssume) &&
                 keepAtAll.Contains(ch)))
            {
              newGoto.AddTarget(CloneBlock(ch));
            }

            pos++;
          }
        }

        return res;
      }

      Split DoSplit()
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        copies.Clear();
        CloneBlock(blocks[0]);
        List<Block> newBlocks = new List<Block>();
        Dictionary<TransferCmd, ReturnCmd> newGotoCmdOrigins = new Dictionary<TransferCmd, ReturnCmd>();
        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          if (copies.TryGetValue(b, out var tmp))
          {
            newBlocks.Add(cce.NonNull(tmp));
            if (gotoCmdOrigins.ContainsKey(b.TransferCmd))
            {
              newGotoCmdOrigins[tmp.TransferCmd] = gotoCmdOrigins[b.TransferCmd];
            }

            foreach (Block p in b.Predecessors)
            {
              Contract.Assert(p != null);
              if (copies.TryGetValue(p, out var tmp2))
              {
                tmp.Predecessors.Add(tmp2);
              }
            }
          }
        }

        return new Split(newBlocks, newGotoCmdOrigins, parent, Implementation);
      }

      Split SplitAt(int idx)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        assertToAssume = idx == 0;
        doingSlice = false;
        ComputeBlockSets(true);

        return DoSplit();
      }

      Split SliceAsserts(double limit, bool pos)
      {
        Contract.Ensures(Contract.Result<Split>() != null);

        slicePos = pos;
        sliceLimit = limit;
        sliceInitialLimit = limit;
        doingSlice = true;
        Split r = DoSplit();
        /*
        Console.WriteLine("split {0} / {1} -->", limit, pos);
        List<Block!> tmp = impl.Blocks;
        impl.Blocks = r.blocks;
        EmitImpl(impl, false);
        impl.Blocks = tmp;
        */

        return r;
      }

      void Print()
      {
        List<Block> tmp = Implementation.Blocks;
        Contract.Assert(tmp != null);
        Implementation.Blocks = blocks;
        ConditionGeneration.EmitImpl(Implementation, false);
        Implementation.Blocks = tmp;
      }

      public Counterexample ToCounterexample(ProverContext context)
      {
        Contract.Requires(context != null);
        Contract.Ensures(Contract.Result<Counterexample>() != null);

        List<Block> trace = new List<Block>();
        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          trace.Add(b);
        }

        foreach (Block b in blocks)
        {
          Contract.Assert(b != null);
          foreach (Cmd c in b.Cmds)
          {
            Contract.Assert(c != null);
            if (c is AssertCmd)
            {
              return VCGen.AssertCmdToCounterexample((AssertCmd) c, cce.NonNull(b.TransferCmd), trace, null, null, null, context);
            }
          }
        }

        Contract.Assume(false);
        throw new cce.UnreachableException();
      }

      private static void PrintSet<T> (HashSet<T> s) {
        foreach(T i in s)
        {
          Console.WriteLine(i);
        }
      }

      // Verify b with the last split in blockAssignments[b]
      private static Dictionary<Block, Block> PickBlocksToVerify (List<Block> blocks, Dictionary<Block, int> splitPoints)
      {
        var todo = new Stack<Block>();
        var blockAssignments = new Dictionary<Block, Block>();
        var immediateDominator = (Program.GraphFromBlocks(blocks)).ImmediateDominator();
        todo.Push(blocks[0]);
        while(todo.Count > 0)
        {
          var currentBlock = todo.Pop();
          if (blockAssignments.Keys.Contains(currentBlock))
          {
            continue;
          }
          else if (immediateDominator[currentBlock] == currentBlock) // if the currentBlock doesn't have a predecessor.
          {
            blockAssignments[currentBlock] = currentBlock;
          }
          else if (splitPoints.Keys.Contains(immediateDominator[currentBlock])) // if the currentBlock's dominator has a split then it will be associated with that split
          {
            blockAssignments[currentBlock] = immediateDominator[currentBlock];
          }
          else
          {
            Contract.Assert(blockAssignments.Keys.Contains(immediateDominator[currentBlock]));
            blockAssignments[currentBlock] = blockAssignments[immediateDominator[currentBlock]];
          }
          if (currentBlock.TransferCmd is GotoCmd exit)
          {
            exit.labelTargets.ForEach(blk => todo.Push(blk));
          }
        }
        return blockAssignments;
      }
      private static List<Block> DoPreAssignedManualSplit(List<Block> blocks, Dictionary<Block, Block> blockAssignments, int splitNumberWithinBlock,
        Block containingBlock, bool lastSplitInBlock, bool splitOnEveryAssert)
      {
        var newBlocks = new List<Block>(blocks.Count()); // Copies of the original blocks
        var duplicator = new Duplicator();
        var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count()); // Maps original blocks to their new copies in newBlocks
        foreach (var currentBlock in blocks)
        {
          var newBlock = (Block)duplicator.VisitBlock(currentBlock);
          oldToNewBlockMap[currentBlock] = newBlock;
          newBlocks.Add(newBlock);
          if (currentBlock == containingBlock)
          {
            var newCmds = new List<Cmd>();
            var splitCount = -1;
            var verify = splitCount == splitNumberWithinBlock;
            foreach (Cmd c in currentBlock.Cmds)
            {
              if (ShouldSplitHere(c, splitOnEveryAssert))
              {
                splitCount++;
                verify = splitCount == splitNumberWithinBlock;
              }
              newCmds.Add(verify ? c : Split.AssertIntoAssume(c));
            }
            newBlock.Cmds = newCmds;
          }
          else if (lastSplitInBlock && blockAssignments[currentBlock] == containingBlock)
          {
            var verify = true;
            var newCmds = new List<Cmd>();
            foreach(Cmd c in currentBlock.Cmds) {
              verify = ShouldSplitHere(c, splitOnEveryAssert) ? false : verify;
              newCmds.Add(verify ? c : Split.AssertIntoAssume(c));
            }
            newBlock.Cmds = newCmds;
          }
          else
          {
            newBlock.Cmds = currentBlock.Cmds.Select<Cmd, Cmd>(c => Split.AssertIntoAssume(c)).ToList();
          }
        }
        // Patch the edges between the new blocks
        foreach (var oldBlock in blocks)
        {
          if (oldBlock.TransferCmd is ReturnCmd)
          {
            continue;
          }

          var gotoCmd = (GotoCmd)oldBlock.TransferCmd;
          var newLabelTargets = new List<Block>(gotoCmd.labelTargets.Count());
          var newLabelNames = new List<string>(gotoCmd.labelTargets.Count());
          foreach (var target in gotoCmd.labelTargets)
          {
            newLabelTargets.Add(oldToNewBlockMap[target]);
            newLabelNames.Add(oldToNewBlockMap[target].Label);
          }

          oldToNewBlockMap[oldBlock].TransferCmd = new GotoCmd(gotoCmd.tok, newLabelNames, newLabelTargets);
        }
        return newBlocks;
      }

      private static List<Block> PostProcess(List<Block> blocks)
      {
        void DeleteFalseGotos (Block b)
        {
          bool isAssumeFalse (Cmd c) { return c is AssumeCmd ac && ac.Expr is LiteralExpr le && !le.asBool; }
          var firstFalseIdx = b.Cmds.FindIndex(c => isAssumeFalse(c));
          if (firstFalseIdx != -1)
          {
            b.Cmds = b.Cmds.Take(firstFalseIdx + 1).ToList();
            b.TransferCmd = (b.TransferCmd is GotoCmd) ? new ReturnCmd(b.tok) : b.TransferCmd;
          }
        }

        bool ContainsAssert(Block b)
        {
          bool isNonTrivialAssert (Cmd c) { return c is AssertCmd ac && !(ac.Expr is LiteralExpr le && le.asBool); }
          return b.Cmds.Exists(cmd => isNonTrivialAssert(cmd));
        }

        blocks.ForEach(b => DeleteFalseGotos(b)); // make blocks ending in assume false leaves of the CFG-DAG -- this is probably unnecessary, may have been done previously
        var todo = new Stack<Block>();
        var peeked = new HashSet<Block>();
        var interestingBlocks = new HashSet<Block>();
        todo.Push(blocks[0]);
        while(todo.Count() > 0)
        {
          var currentBlock = todo.Peek();
          var pop = peeked.Contains(currentBlock);
          peeked.Add(currentBlock);
          var interesting = false;
          var exit = currentBlock.TransferCmd as GotoCmd;
          if (exit != null && !pop) {
            exit.labelTargets.ForEach(b => todo.Push(b));
          } else if (exit != null) {
            Contract.Assert(pop);
            var gtc = new GotoCmd(exit.tok, exit.labelTargets.Where(l => interestingBlocks.Contains(l)).ToList());
            currentBlock.TransferCmd = gtc;
            interesting = interesting || gtc.labelTargets.Count() != 0;
          }
          if (pop)
          {
            interesting = interesting || ContainsAssert(currentBlock);
            if (interesting) {
              interestingBlocks.Add(currentBlock);
            }
            todo.Pop();
          }
        }
        interestingBlocks.Add(blocks[0]); // must not be empty
        return blocks.Where(b => interestingBlocks.Contains(b)).ToList(); // this is not the same as interestingBlocks.ToList() because the resulting lists will have different orders.
      }

      private static bool ShouldSplitHere(Cmd c, bool splitOnEveryAssert) {
        return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "split_here")
               || c is AssertCmd && splitOnEveryAssert;
      }
      
      public static List<Split /*!*/> FindManualSplits(Split s, bool splitOnEveryAssert)
      {
        Contract.Requires(s.Implementation != null);
        Contract.Ensures(Contract.Result<List<Split>>() == null || cce.NonNullElements(Contract.Result<List<Split>>()));

        var splitPoints = new Dictionary<Block, int>();
        foreach (var b in s.blocks)
        {
          foreach (Cmd c in b.Cmds)
          {
            var p = c as PredicateCmd;
            if (ShouldSplitHere(c, splitOnEveryAssert))
            {
              splitPoints.TryGetValue(b, out var count);
              splitPoints[b] = count + 1;
            }
          }
        }
        List<Split> splits = new List<Split>();
        if (splitPoints.Count() == 0)
        {
          splits.Add(s);
        }
        else
        {
          Block entryPoint = s.blocks[0];
          var blockAssignments = PickBlocksToVerify(s.blocks, splitPoints);
          var entryBlockHasSplit = splitPoints.Keys.Contains(entryPoint);
          var baseSplitBlocks = PostProcess(DoPreAssignedManualSplit(s.blocks, blockAssignments, -1, entryPoint, !entryBlockHasSplit, splitOnEveryAssert));
          splits.Add(new Split(baseSplitBlocks, s.gotoCmdOrigins, s.parent, s.Implementation));
          foreach (KeyValuePair<Block, int> pair in splitPoints)
          {
            for (int i = 0; i < pair.Value; i++)
            {
              bool lastSplitInBlock = i == pair.Value - 1;
              var newBlocks = DoPreAssignedManualSplit(s.blocks, blockAssignments, i, pair.Key, lastSplitInBlock, splitOnEveryAssert);
              splits.Add(new Split(PostProcess(newBlocks), s.gotoCmdOrigins, s.parent, s.Implementation)); // REVIEW: Does gotoCmdOrigins need to be changed at all?
            }
          }
        }
        return splits;
      }

      public static List<Split> FocusImpl(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VCGen par)
      {
        bool IsFocusCmd(Cmd c) {
          return c is PredicateCmd p && QKeyValue.FindBoolAttribute(p.Attributes, "focus");
        }

        List<Block> GetFocusBlocks(List<Block> blocks) {
          return blocks.Where(blk => blk.Cmds.Where(c => IsFocusCmd(c)).Any()).ToList();
        }

        var dag = Program.GraphFromImpl(impl);
        var topoSorted = dag.TopologicalSort().ToList();
        // By default, we process the foci in a top-down fashion, i.e., in the topological order.
        // If the user sets the RelaxFocus flag, we use the reverse (topological) order.
        var focusBlocks = GetFocusBlocks(topoSorted);
        if (CommandLineOptions.Clo.RelaxFocus) {
          focusBlocks.Reverse();
        }
        if (!focusBlocks.Any()) {
          var f = new List<Split>();
          f.Add(new Split(impl.Blocks, gotoCmdOrigins, par, impl));
          return f;
        }
        // finds all the blocks dominated by focusBlock in the subgraph
        // which only contains vertices of subgraph.
        HashSet<Block> DominatedBlocks(Block focusBlock, IEnumerable<Block> subgraph)
        {
          var dominators = new Dictionary<Block, HashSet<Block>>();
          var todo = new Queue<Block>();
          foreach (var b in topoSorted.Where(blk => subgraph.Contains(blk)))
          {
            var s = new HashSet<Block>();
            var pred = b.Predecessors.Where(blk => subgraph.Contains(blk)).ToList();
            if (pred.Count != 0)
            {
              s.UnionWith(dominators[pred[0]]);
              pred.ForEach(blk => s.IntersectWith(dominators[blk]));
            }
            s.Add(b);
            dominators[b] = s;
          }
          return subgraph.Where(blk => dominators[blk].Contains(focusBlock)).ToHashSet();
        }

        Cmd DisableSplits(Cmd c)
        {
          if (c is PredicateCmd pc)
          {
            for (var kv = pc.Attributes; kv != null; kv = kv.Next)
            {
              if (kv.Key == "split")
              {
                kv.AddParam(new LiteralExpr(Token.NoToken, false));
              }
            }
          }
          return c;
        }

        var Ancestors = new Dictionary<Block, HashSet<Block>>();
        var Descendants = new Dictionary<Block, HashSet<Block>>();
        focusBlocks.ForEach(fb => Ancestors[fb] = dag.ComputeReachability(fb, false).ToHashSet());
        focusBlocks.ForEach(fb => Descendants[fb] = dag.ComputeReachability(fb, true).ToHashSet());
        var s = new List<Split>();
        var duplicator = new Duplicator();
        void FocusRec(int focusIdx, IEnumerable<Block> blocks, IEnumerable<Block> freeBlocks)
        {
          if (focusIdx == focusBlocks.Count())
          {
            // it is important for l to be consistent with reverse topological order.
            var l = dag.TopologicalSort().Where(blk => blocks.Contains(blk)).Reverse();
            // assert that the root block, impl.Blocks[0], is in l
            Contract.Assert(l.ElementAt(l.Count() - 1) == impl.Blocks[0]);
            var newBlocks = new List<Block>();
            var oldToNewBlockMap = new Dictionary<Block, Block>(blocks.Count());
            foreach (Block b in l)
            {
              var newBlock = (Block)duplicator.Visit(b);
              newBlocks.Add(newBlock);
              oldToNewBlockMap[b] = newBlock;
              // freeBlocks consist of the predecessors of the relevant foci.
              // Their assertions turn into assumes and any splits inside them are disabled.
              if(freeBlocks.Contains(b))
              {
                newBlock.Cmds = b.Cmds.Select(c => Split.AssertIntoAssume(c)).Select(c => DisableSplits(c)).ToList();
              }
              if (b.TransferCmd is GotoCmd gtc)
              {
                var targets = gtc.labelTargets.Where(blk => blocks.Contains(blk));
                newBlock.TransferCmd = new GotoCmd(gtc.tok,
                                              targets.Select(blk => oldToNewBlockMap[blk].Label).ToList(),
                                              targets.Select(blk => oldToNewBlockMap[blk]).ToList());
              }
            }
            newBlocks.Reverse();
            Contract.Assert(newBlocks[0] == oldToNewBlockMap[impl.Blocks[0]]);
            s.Add(new Split(PostProcess(newBlocks), gotoCmdOrigins, par, impl));
          }
          else if (!blocks.Contains(focusBlocks[focusIdx])
                    || freeBlocks.Contains(focusBlocks[focusIdx]))
          {
            FocusRec(focusIdx + 1, blocks, freeBlocks);
          }
          else
          {
            var b = focusBlocks[focusIdx]; // assert b in blocks
            var dominatedBlocks = DominatedBlocks(b, blocks);
            // the first part takes all blocks except the ones dominated by the focus block
            FocusRec(focusIdx + 1, blocks.Where(blk => !dominatedBlocks.Contains(blk)), freeBlocks);
            var ancestors = Ancestors[b];
            ancestors.Remove(b);
            var descendants = Descendants[b];
            // the other part takes all the ancestors, the focus block, and the descendants.
            FocusRec(focusIdx + 1, ancestors.Union(descendants).Intersect(blocks), ancestors.Union(freeBlocks));
          }
        }

        FocusRec(0, impl.Blocks, new List<Block>());
        return s;
      }

      public static List<Split> FocusAndSplit(Implementation impl, Dictionary<TransferCmd, ReturnCmd> gotoCmdOrigins, VCGen par, bool splitOnEveryAssert)
      {
        List<Split> focussedImpl = FocusImpl(impl, gotoCmdOrigins, par);
        var splits = focussedImpl.Select(s => FindManualSplits(s, splitOnEveryAssert)).SelectMany(x => x).ToList();
        return splits;
      }

      public static List<Split /*!*/> /*!*/ DoSplit(Split initial, double splitThreshold, int maxSplits)
      {
        Contract.Requires(initial != null);
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Split>>()));

        var result = new List<Split> { initial };

        while (result.Count < maxSplits)
        {
          Split best = null;
          int bestIndex = 0;
          for (var index = 0; index < result.Count; index++) {
            var split = result[index];
            Contract.Assert(split != null);
            split.ComputeBestSplit(); // TODO check totalCost first
            if (split.totalCost > splitThreshold &&
                (best == null || best.totalCost < split.totalCost) &&
                (split.assertionCount > 1 || split.splitBlock != null)) {
              best = split;
              bestIndex = index;
            }
          }

          if (best == null)
          {
            break; // no split found
          }

          Split s0, s1;

          bool splitStats = CommandLineOptions.Clo.TraceVerify;

          if (splitStats)
          {
            Console.WriteLine("{0} {1} -->", best.splitBlock == null ? "SLICE" : ("SPLIT@" + best.splitBlock.Label),
              best.Stats);
            if (best.splitBlock != null)
            {
              GotoCmd g = best.splitBlock.TransferCmd as GotoCmd;
              if (g != null)
              {
                Console.Write("    exits: ");
                foreach (Block b in cce.NonNull(g.labelTargets))
                {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }

                Console.WriteLine("");
                Console.Write("    assumized: ");
                foreach (Block b in best.assumizedBranches)
                {
                  Contract.Assert(b != null);
                  Console.Write("{0} ", b.Label);
                }

                Console.WriteLine("");
              }
            }
          }

          if (best.splitBlock != null)
          {
            s0 = best.SplitAt(0);
            s1 = best.SplitAt(1);
          }
          else
          {
            best.splitBlock = null;
            s0 = best.SliceAsserts(best.assertionCost / 2, true);
            s1 = best.SliceAsserts(best.assertionCost / 2, false);
          }

          if (true)
          {
            var ss = new List<Block>
            {
              s0.blocks[0],
              s1.blocks[0]
            };
            try
            {
              best.SoundnessCheck(new HashSet<List<Block>>(new BlockListComparer()), best.blocks[0], ss);
            }
            catch (System.Exception e)
            {
              Console.WriteLine(e);
              best.DumpDot(-1);
              s0.DumpDot(-2);
              s1.DumpDot(-3);
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
          }

          if (splitStats)
          {
            s0.ComputeBestSplit();
            s1.ComputeBestSplit();
            Console.WriteLine("    --> {0}", s0.Stats);
            Console.WriteLine("    --> {0}", s1.Stats);
          }

          if (CommandLineOptions.Clo.TraceVerify)
          {
            best.Print();
          }

          result[bestIndex] = s0;
          result.Add(s1);
        }

        return result;
      }

      class BlockListComparer : IEqualityComparer<List<Block>>
      {
        public bool Equals(List<Block> x, List<Block> y)
        {
          return x == y || x.SequenceEqual(y);
        }

        public int GetHashCode(List<Block> obj)
        {
          int h = 0;
          Contract.Assume(obj != null);
          foreach (var b in obj)
          {
            if (b != null)
            {
              h += b.GetHashCode();
            }
          }

          return h;
        }
      }

      public Checker Checker
      {
        get
        {
          Contract.Ensures(Contract.Result<Checker>() != null);

          Contract.Assert(checker != null);
          return checker;
        }
      }

      public Task ProverTask
      {
        get
        {
          Contract.Assert(checker != null);
          return checker.ProverTask;
        }
      }

      public void ReadOutcome(ref ConditionGeneration.Outcome curOutcome, out bool proverFailed, ref int totalResourceCount)
      {
        Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);
        ProverInterface.Outcome outcome = cce.NonNull(checker).ReadOutcome();

        if (CommandLineOptions.Clo.Trace && splitNum >= 0)
        {
          System.Console.WriteLine("      --> split #{0} done,  [{1} s] {2}", splitNum + 1,
            checker.ProverRunTime.TotalSeconds, outcome);
        }

        if (CommandLineOptions.Clo.XmlSink != null && splitNum >= 0) {
          CommandLineOptions.Clo.XmlSink.WriteEndSplit(outcome.ToString().ToLowerInvariant(), 
            TimeSpan.FromSeconds(checker.ProverRunTime.TotalSeconds));
        }

        if (CommandLineOptions.Clo.VcsDumpSplits)
        {
          DumpDot(splitNum);
        }

        totalResourceCount += checker.ProverResourceCount;

        proverFailed = false;

        switch (outcome)
        {
          case ProverInterface.Outcome.Valid:
            return;
          case ProverInterface.Outcome.Invalid:
            curOutcome = ConditionGeneration.Outcome.Errors;
            return;
          case ProverInterface.Outcome.OutOfMemory:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
            {
              curOutcome = ConditionGeneration.Outcome.OutOfMemory;
            }

            return;
          case ProverInterface.Outcome.TimeOut:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
            {
              curOutcome = ConditionGeneration.Outcome.TimedOut;
            }

            return;
          case ProverInterface.Outcome.OutOfResource:
            proverFailed = true;
            if (curOutcome != ConditionGeneration.Outcome.Errors && curOutcome != ConditionGeneration.Outcome.Inconclusive)
            {
              curOutcome = ConditionGeneration.Outcome.OutOfResource;
            }

            return;
          case ProverInterface.Outcome.Undetermined:
            if (curOutcome != ConditionGeneration.Outcome.Errors)
            {
              curOutcome = ConditionGeneration.Outcome.Inconclusive;
            }

            return;
          default:
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      }

      /// <summary>
      /// As a side effect, updates "this.parent.CumulativeAssertionCount".
      /// </summary>
      public void BeginCheck(Checker checker, VerifierCallback callback, ModelViewInfo mvInfo, int no, uint timeout, uint rlimit)
      {
        Contract.Requires(checker != null);
        Contract.Requires(callback != null);

        splitNum = no;

        // Lock impl since we're setting impl.Blocks that is used to generate the VC.
        lock (Implementation) {
          Implementation.Blocks = blocks;

          this.checker = checker;

          var absyIds = new ControlFlowIdMap<Absy>();

          ProverContext ctx = checker.TheoremProver.Context;
          Boogie2VCExprTranslator bet = ctx.BoogieExprTranslator;
          var cc = new VCGen.CodeExprConversionClosure(absyIds, ctx);
          bet.SetCodeExprConverter(cc.CodeExprToVerificationCondition);

          var exprGen = ctx.ExprGen;
          VCExpr controlFlowVariableExpr = exprGen.Integer(BigNum.ZERO);
        #region proofgen
          TypePremiseEraserFactory typePremiseEraserFactory;
          switch (CommandLineOptions.Clo.TypeEncodingMethod)
          {
            case CommandLineOptions.TypeEncoding.Predicates:
              typePremiseEraserFactory = new TypePremiseEraserFactory(checker.VCExprGen, bet, true); 
              break;
            case CommandLineOptions.TypeEncoding.Monomorphic:
              typePremiseEraserFactory = new TypePremiseEraserFactory(checker.VCExprGen, bet, false);
              break;
            default:
              throw new NotImplementedException();
          } 
          ProofGenerationLayer.SetTypeEraserFactory(typePremiseEraserFactory);
          #endregion
        
        /* PROOF GEN: we pass "null" as the control flow variable expression, such that labels are not produced as they are
         * not relevant for proof generation of programs that verify */
          VCExpr vc = parent.GenerateVCAux(Implementation, null, absyIds, checker.TheoremProver.Context);
          Contract.Assert(vc != null);
        
          vc = QuantifierInstantiationEngine.Instantiate(Implementation, exprGen, bet, vc);

          #region proofgen
          if(!(ctx is DeclFreeProverContext))
          { 
            throw new NotImplementedException("Proof Generation only supports DeclFreeProverContext as context.");
          }

          var declFreeProverContext = ctx as DeclFreeProverContext;
          var premiseEraserProvider = typePremiseEraserFactory?.NewEraser();

          VCExpr eraseVC (VCExpr vc, int polarity) 
          {
            return !premiseEraserProvider.ProgramIsPolymorphic ? vc : premiseEraserProvider.EraseAndSortLet(vc, polarity);
          }

          VCExpr erasedVC = eraseVC(vc, 1);
          VCExpr erasedAxioms = eraseVC(declFreeProverContext.Axioms, -1);

          VCExpr typeAxioms = null;
          List<VCAxiomInfo> vcAxiomsInfo = null;
          if (premiseEraserProvider.ProgramIsPolymorphic) {
            typeAxioms = premiseEraserProvider.AxiomBuilder.GetNewAxiomsAndInfo(out vcAxiomsInfo);
          }

          ProofGenerationLayer.VCGenerateAllProofs(
            erasedVC, 
            erasedAxioms, 
            typeAxioms,
            vcAxiomsInfo,
            checker.TheoremProver.VCExprGen, 
            checker.TheoremProver.Context.BoogieExprTranslator,
            premiseEraserProvider?.AxiomBuilder);
          #endregion

          /* PROOF GEN: comment out label specific parts
            VCExpr controlFlowFunctionAppl =
              exprGen.ControlFlowFunctionApplication(exprGen.Integer(BigNum.ZERO), exprGen.Integer(BigNum.ZERO));
            VCExpr eqExpr = exprGen.Eq(controlFlowFunctionAppl, exprGen.Integer(BigNum.FromInt(absyIds.GetId(Implementation.Blocks[0]))));
            vc = exprGen.Implies(eqExpr, vc);
          */
          reporter = new VCGen.ErrorReporter(gotoCmdOrigins, absyIds, Implementation.Blocks, parent.debugInfos, callback,
            mvInfo, this.Checker.TheoremProver.Context, parent.program);
          
          if (CommandLineOptions.Clo.TraceVerify && no >= 0)
          {
            Console.WriteLine("-- after split #{0}", no);
            Print();
          }

          string desc = cce.NonNull(Implementation.Name);
          if (no >= 0)
          {
            desc += "_split" + no;
          }

          checker.BeginCheck(desc, vc, reporter, timeout, rlimit);
        }
      }

      private static Cmd AssertIntoAssume(Cmd c)
      {
        if (c is AssertCmd assrt)
        {
          return VCGen.AssertTurnedIntoAssume(assrt);
        }

        return c;
      }

      private void SoundnessCheck(HashSet<List<Block> /*!*/> /*!*/ cache, Block /*!*/ orig,
        List<Block /*!*/> /*!*/ copies)
      {
        Contract.Requires(cce.NonNull(cache));
        Contract.Requires(orig != null);
        Contract.Requires(copies != null);
        {
          var t = new List<Block> {orig};
          foreach (Block b in copies)
          {
            Contract.Assert(b != null);
            t.Add(b);
          }

          if (cache.Contains(t))
          {
            return;
          }

          cache.Add(t);
        }

        for (int i = 0; i < orig.Cmds.Count; ++i)
        {
          Cmd cmd = orig.Cmds[i];
          if (cmd is AssertCmd)
          {
            int found = 0;
            foreach (Block c in copies)
            {
              Contract.Assert(c != null);
              if (c.Cmds[i] == cmd)
              {
                found++;
              }
            }

            if (found == 0)
            {
              throw new System.Exception(string.Format("missing assertion: {0}({1})", cmd.tok.filename, cmd.tok.line));
            }
          }
        }

        foreach (Block exit in orig.Exits())
        {
          Contract.Assert(exit != null);
          List<Block> newcopies = new List<Block>();
          foreach (Block c in copies)
          {
            foreach (Block cexit in c.Exits())
            {
              Contract.Assert(cexit != null);
              if (cexit.Label == exit.Label)
              {
                newcopies.Add(cexit);
              }
            }
          }

          if (newcopies.Count == 0)
          {
            throw new System.Exception("missing exit " + exit.Label);
          }

          SoundnessCheck(cache, exit, newcopies);
        }
      }

      public void ReleaseChecker()
      {
        Checker.GoBackToIdle();
        checker = null;
      }
    }
}
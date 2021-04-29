# Formally Validating a Practical Verification Condition Generator: Artifact

This document contains the instructions for the artifact associated with the 
paper "Formally Validating a Practical Verification Condition Generator", which 
consists of two parts:
1. An Isabelle formalization for the Boogie intermediate verification language.
2. An extension of the Boogie verifier that generates Isabelle proofs whenever 
it is run on an input program (that lies in a particular subset).

All required dependencies are pre-installed on the provided Ubuntu 20.04 64-bit virtual
machine. We have set the virtual machine settings to use 8 GB RAM and 4 cores.
The password for the VM user `boogie` is `test123`.
A script to install the dependencies for the sake of reproducing the artifact
is provided in `artifact/boogie_proofgen/etc/vm/setup_vm.sh` 
(also check that file to see which commit hashes we fix).

For commands that take a longer duration we provide estimates on how long the
command runs based on our own runs of the commands in the VM (using 8 GB RAM
and 4 cores).

## Main structure of home folder
* `artifact/foundational_boogie` contains the Isabelle formalization of the Boogie semantics 
and helper lemmas/definitions that we use to certify the different phases. 
* `artifact/boogie_proofgen` contains our extension of the Boogie verifier. 
* `deps` contains dependencies for the experiments/tool. In particular,
`deps/Isabelle2021` contains Isabelle version 2021.
* `local_scripts` is a folder added to the PATH.
* `paper.pdf` is the version of our paper that was reviewed.
* `README.md` is this README


## Isabelle formalization of the Boogie semantics

All the Isabelle theory files (ending with `.thy`) for the Isabelle formalization 
of the Boogie semantics and helper lemmas/definitions for the certification are stored 
in `artifact/foundational_boogie/BoogieLang`. 
It is publicly available at https://github.com/gauravpartha/foundational_boogie/ 
under the Mozilla public license 2.0.

We recommend exploring the Isabelle files using the Isabelle GUI. Open the Isabelle GUI
by invoking `deps/Isabelle2021/Isabelle2021`. The theory files can then be directly
dragged into the editor or opened via "File -> Open". Definitions of "atomic" 
terms can be explored by using "ctrl + left-click" on the term.

See the [README file](artifact/foundational_boogie/README.md) for the Isabelle 
formalization for more details on the content of the theories.

One point that we did not expand on in the paper is that we use a DeBruijn
encoding to deal with bound variables and thus we have a separate binder state.
Moreover, the files have been extended since the paper submission and now additionally
contain:
* A semantics for procedure calls with possibly free pre- and postconditions. As
a result, the context of the semantics includes a procedure context.
* Preliminary where-clause support (semantics of havoc is affected, but for 
programs without where-clauses there is no difference)
* Division and modulo operator support

Programs that use these features (except division and modulo) are in general
not yet supported by our proof generation tool, but our tool works with the 
extended interface.

The theory files that do not contain ML code contain comments that describe
the different parts. Moreover, we divided the some theory files into subsections. 
You can use Isabelle's "sidekick" on the right of the Isabelle GUI to navigate the theory
files via the subsections.

## Proof generation extension of the Boogie Verifier
Our proof generation extension of the Boogie verifier is stored at 
`artifact/boogie_proofgen`.
It is publicly available at https://github.com/gauravpartha/boogie_proofgen/ under 
the MIT license (inherited from the original Boogie repository). 

### Source code
The tool is a fork of the [original Boogie verifier](https://github.com/boogie-org/boogie).
The latest commit version we have merged is the [following](https://github.com/boogie-org/boogie/commit/3d09d0b07756d7da3f9051978f4049859da950d3).
Our source code for the proof generation module is stored in 
`artifact/boogie_proofgen/Source/ProofGeneration`. Moreover, we have added various
calls in the existing Boogie code to our module for the purpose of proof generation.
In some cases, we have also extended the existing infrastructure.
[ProofGenerationLayer.cs](`artifact/boogie_proofgen/Source/ProofGeneration/ProofGenerationLayer.cs`)
in our module acts as the main interface between the code in the existing
Boogie infrastructure and the proof generation module. 
Calls from the existing infrastructure mainly go to this class. 
Two examples of such calls:
1. `ProofGenerationLayer.BeforeCFGToDAG` is invoked with the source CFG of the 
CFG-to-DAG phase. The method is invoked right before the CFG-to-DAG phase is 
executed in the existing Boogie verifier code.
2. `ProofGenerationLayer.NextPassificationHint` provides a hint on which variable
before the passification is related to which expression in the passified program.
This method is invoked during the passification phase in the existing code.

We have added comments for the public methods of `ProofGenerationLayer.cs` in
the file itself.

One example for an infrastructure extension is the method `AddTypeAxiom` in the 
file [TypeErasure.cs](`artifact/boogie_proofgen/Source/VCExpr/TypeErasure.cs) 
(class `TypeAxiomBuilder`). Originally, this method only had a single 
argument, which was an axiom for the type encoding. We extended it to accept
a second argument that additionally provides hints on what this axiom represents. 
We changed relevant callsites to include the correct hint.

To check the adjustments to the existing code base, you can compare with the
code at `deps/boogie_orig/`, where we have checked out the corresponding version
of the original Boogie verifier. We have added/adjusted some more existing lines 
compared to the paper submission, but not by much.

#### Changes to the VC
As we have pointed out in the paper, we modified Boogie to generate a slightly
different VC than in the original version. To make this more transparent, we 
have included a Boogie version where only the VC has been adjusted  
at `~/deps/boogie_vc` (we used the commit that was last merged into our tool as the base). 
If you invoke `git diff` in `~/deps/boogie_vc`, you will see the VC changes 
only. To inspect the VC in the SMTLIB format you can invoke 
`boogievc /proverLog:<vc_ouput_file> <boogie_input_file>` which will invoke
this version and store the VC in SMTLIB format in `vc_ouput_file`
(you could do the same with our tool, i.e., `boogieproof`, but 
you may not be convinced that we do not perform any other changes to the VC).
Note that <vc_output_file> contains the VCs for all procedure.

This version is publicly available via a [Google drive link](
  https://drive.google.com/file/d/1zY0UgHT6fmeripzlzpmd8OM6tUGSJXxv/view?usp=sharing
).

### Tool usage
Our tool can be invoked using the command `boogieproof [options] <boogie_file>`. 
In theory, one can use any option that Boogie supports, but not all of them 
are supported by the tool. For the purpose of the artifact, only the 
(optional) option `/proofOutputDir:<dir_path>` is relevant:

`boogieproof /proofOutputDir:<dir_path> <boogie_file>` creates a directory 
with path `dir_path` in which the Isabelle proofs are stored. If there already
is a directory at `dir_path`, then an error is reported. If this option is not 
provided (i.e., one invokes `boogieproof <boogie_file>`), then a new folder with 
the name `<boogie_file>_proofs` is created (and possibly some suffix if such a 
directory already exists) in which the proofs are stored.

### Tool output
After invoking the tool on some Boogie file, a folder is created that contains 
the Isabelle proofs (see "Tool usage" above). The folder contains the following:
1. `global_data.thy`: This is an Isabelle theory file that contains the global
information relevant for all procedures (function declarations, axioms, global
variables, constants). It also contains some lemmas about these global definitions
that are re-used in other theories.

2. `ROOT`: This defines the Isabelle session that refers to all theory files. 
It allows one to easily check all proofs via the command line.

3. One folder per procedure with the name `<proc_name>_proofs`. This folder
contains the following theory files
    * `<proc_name>_before_cfg_to_dag_prog.thy`: 
    Defines the CFG-to-DAG source CFG and the procedure in terms of this source CFG. 
    The goal is to prove this procedure correct. Note that we always set the
    return variables to the empty set: 
    If a procedure has return variables, we append them to the local variables as a simplifcation.
    Since we do not support procedure call certification yet, this simplification does not have
    an impact on the meaning of the certificate.
    * `<proc_name>_before_passive_prog.thy`: Defines the passification source CFG.
    * `<proc_name>_passive_prog.thy`: Defines the passification target CFG.
    * `<proc_name>_cfgtodag_proof.thy`:
    Contains the proof of the CFG-to-DAG phase (relating the CFGs defined in 
    `<proc_name>_before_cfg_to_dag_prog.thy` and `<proc_name>_before_passive_prog.thy`). 
    Moreover, contains the end-to-end theorem that proves the procedure defined in 
    `<proc_name>_before_cfg_to_dag_prog.thy` is correct under the assumption of the VC. 
    This is the main theorem for the procedure and it is at the very end of the file
    (named `end_to_end_theorem`).
    * `<proc_name>_passification_proof.thy`: Contains the proof of the passification
    phase (relating the CFGs defined in `<proc_name>_before_passive_prog.thy` and 
    `<proc_name>_passive_prog.thy`). Moreover, lifts proof to prove
    correctness of the passification source CFG under the assumption of the VC
    (using the VC phase proof).
    * `<proc_name>_vcphase_proof.thy`: Contains the definition of the VC and the 
    proof of the VC phase (relating the CFG defined in `<proc_name>_passive_prog.thy`
    and the VC)

The three theory files for the three phases contain the local block lemmas
(Isabelle lemma names starts with `block_`) and the global block theorems 
(Isabelle lemma names starts with `cfg_`) for the corresponding phase.
The suffix of the (local and global) block lemma names is usually the label that
Boogie uses internally for the block (see below for the explanation of the 
command `boogiephases` that makes these labels visible).
Morever, the main result of each phase is given by the final Isabelle lemma in the
corresponding file. Note that in the passification phase proof the final Isabelle
lemma is contained in an Isabelle locale (named `locale glue_proof` in the same
file) that defines fixed variables and various assumptions.

### Running the tool on an example program
We have prepared three different Boogie programs in 
`artifact/boogie_proofgen/ProofGenerationBenchmarks/misc` that were not used in any of 
the benchmarks and do not appear in the paper. These programs show different
features that are supported by our tool. The three files are 
1. [goto_nested_different_mods.bpl](artifact/boogie_proofgen/ProofGenerationBenchmarks/misc/goto_nested_different_mods.bpl): 
Shows an example with nested loops, where there are jumps out of loops.
2. [poly1.bpl](artifact/boogie_proofgen/ProofGenerationBenchmarks/misc/poly1.bpl): 
 Shows an example using type constructors, polymorphism, axioms, and loops.
3. [old_expr.bpl](artifact/boogie_proofgen/ProofGenerationBenchmarks/misc/old_expr.bpl):
Shows an example with global variables, constants, and old expressions.

For files with interesting specifications see the benchmarks used for table 1.

You can generate proofs for the first example as follows:
```
cd artifact/boogie_proofgen/ProofGenerationBenchmarks/misc 
boogieproof /proofOutputDir:goto_proofs goto_nested_different_mods.bpl
```
which stores the proofs in the `goto_proofs` folder.

You can next inspect the Isabelle theory files contained in `goto_proofs`
(see above for what the different files mean). For this we recommend to use the
Isabelle GUI as for the formalization (run ~/deps/Isabelle2021/Isabelle2021 and
drag the file into the browser). Note that when you open a proof, then Isabelle
will have to load the entire Boogie formalization first which takes some time.
If you keep Isabelle open, then it won't have to reload the formalization when
you open another theory file that depends on it. 
If you want to close Isabelle and re-open it without having to reload the 
Boogie formalization, then you can click on "Theories" on the far right of the 
GUI which opens a sidebar. Then click on `default (HOL)` to open a dropdown
menu from which you can select `Boogie_Lang`. The downside of this is that 
you can then not explore the Boogie formalization inside Isabelle, since it locks 
the theories (you can always change back to `HOL` to allow exploration again).

In the Isabelle theory file generated for the CFG-to-DAG phase you can see that
there is one induction proof per loop (for the global block theorems of the loop
entry blocks). You can see this by searching for `induction` in the file. 

### Further information when using our tool
When invoking our tool to generate/check proofs, take the following into account:
1. Use programs that are in our subset (see paper/benchmarks).
2. Use programs that verify (our certificates  
essentially have a false assumption if the VC is not valid and our tool 
cannot provide detailed information on errors since we removed counterexample
information from the VC). 
You can use the original Boogie version using `boogieorig <boogie_file>` to locate errors.
3. When using type constructors, include at least one polymorphic function, otherwise
Boogie monomorphizes the entire program, which leads to a VC that our tool does
not yet handle.
4. Do not use any special characters in the procedure name/file name (even if 
the original Boogie version accepts them).

### Relating the tool output to Boogie and smaller intermediate phases
If one wants to check whether our final theorem in `<proc_name>_cfgtodag_proof.thy` 
actually proves something about the Boogie verifier (in the case one does not trust our 
generation of the Isabelle embeddings), then one needs to check:

1. The VC produced by the Boogie verifier is correctly represented by its Isabelle
embedding in the end-to-end theorem.

2. The source CFG of the CFG-to-DAG phase used inside the Boogie verifier is correctly
represented by its Isabelle embedding in `<proc_name>_before_cfg_to_dag_prog.thy`.

Both of these steps must be done manually. To obtain Boogie's VC in SMTLIB form
one can use `boogievc /proverLog:<vc_ouput_file> <boogie_input_file>` as mentioned above. 
Note that instead of the let-expressions used in the VC for the weakest precondition 
of the blocks, we use separate Isabelle definitions. Moreover, instead of conjoining axioms,
our Isabelle embedding is of the form 
"forall .... . axiom1 ==> axiom2 ==> ... ==> axiomN ==> wp(entryblock, true)".

To obtain the source CFG inside the Boogie verifier, we provide the command 
`boogiephases <boogie_file>`, which prints an AST representation (using gotos and
labels) of most intermediate CFGs used in the Boogie verifier (using an option provided by 
the existing Boogie verifier itself). The labels that Boogie uses for the 
CFG blocks in the AST correspond to the internal labels that Boogie uses for those
blocks (the corresponding block lemmas in the proofs use these in their name).

The first representation that is printed in the output of `boogiephases` is the 
CFG-to-DAG source CFG (with the program description "original implementation").
As mentioned in the paper, there are various transformations performed by Boogie
before the CFG-to-DAG source CFG is produced (none of these are shown
in the output of `boogiephases`).

In the paper, we did not discuss smaller transformations that Boogie performs
after the CFG-to-DAG phase in detail even though we support them (see the 
[proof generation README](artifact/boogie_proofgen/README.md), where we mention them
). Most of them are  visible in the output of `boogiephases`. We handle each small 
transformation as part of one of the key phases without having to define separate CFGs in
the Isabelle embedding. 
For example, the target CFG that we use in the CFG-to-DAG phase proof is the 
CFG that Boogie obtains after performing the CFG-to-DAG transformation followed
by several smaller transformations such as inserting the pre- and postconditions
as assumptions and assertions.

Without going into the details, the following program descriptions used in the 
`boogiephases` output make clear which CFGs are used in the proofs of the different phases:
1) CFG-to-DAG phase: "original implementation" (source) and "after adding empty 
blocks as needed to catch join assumptions" (target)
2) Passification phase: "after adding empty blocks as needed to catch join assumptions" 
(source) and "after conversion to passive commands" (target). Note that passification 
includes constant propagation that is not shown as a separate transformation.
3) VC phase: "after conversion to passive commands" (source) and the VC (target)

With this information, inspecting the output of `boogiephases` makes clear
which transformations are combined in the proofs of the three key phases.
Moreover, note that in the paper we do not apply the smaller transformations
to the running example for the sake of presentation.


## Reproducing experiments in the paper

### Boogie test suite benchmarks selection
For the benchmarks taken from the Boogie test suite, we used the 
[following version](https://github.com/boogie-org/boogie/tree/b4be7f72e3c74cfa9257f385e2c59613b8ced898/Test).
We do not consider the civl folder in the test suite, since it only contains 
examples for the CIVL verifier, which uses an extension of Boogie. The selected
files are stored in `artifact/boogie_proofgen/ProofGenerationBenchmarks/boogie_testsuite_benchmarks`. 

We automatically selected these files from the test suite using the script in 
`artifact/boogie_proofgen/etc/scripts/find_supported_boogie_benchmarks.py` 
as described in the paper. 
More precisely, the script first filters files using a coarse grained-check that our proof 
generation tool always applies before generating proofs (removing those files that
are not in our subset or not close to our subset). This coarse-grained check
is implemented in [ProofGenSubsetChecker.cs](`artifact/boogie_proofgen/Source/ProofGeneration/Util/ProofGenSubsetChecker.cs`).
In a second step, the script picks all files that pass this check and selects those
that verify once one has removed all attributes of the form `{: ...}` and that 
have at least one procedure.

Finally, we manually rewrite the remaining files into our subset when necessary 
(this step is not included in the script). In the [README for the Boogie benchmark
files](`artifact/boogie_proofgen/ProofGenerationBenchmarks/boogie_testsuite_benchmarks/README.md`), 
we have documented which files were manually rewritten and also added some other notes
on the examples.

To run our script to find the selected tests, you can invoke the following:
```
python3 ~/artifact/boogie_proofgen/etc/scripts/find_supported_boogie_benchmarks.py -t ~/deps/boogie_testsuite/Test/ -o selected_tests.txt
```
`-t ~/deps/boogie_testsuite/Test` indicates that `~/deps/boogie_testsuite/Test` is 
the test suite folder (we have cloned the test suite into that folder and removed
the `civl` subfolder).
`-o selected_tests.txt` expresses that the script should store the paths of the 
selected files into `selected_tests.txt` (1 path per line). Note that this script
has a side effect on `~/deps/boogie_testsuite/Test`: Attributes may be removed 
from some of the files (but you can easily undo this, since the files are under
version control: but if you re-run the script, make sure the `civl` folder has
been removed).

The time for this script takes less than 6 minutes.

With our updated proof generation tool this leads to 101 files, where 1 file is a
duplicate (`functiondefine/fundef7.bpl` and `inline/test0.bpl` are the same). 
These are 5 more files than reported in the evaluation of the
paper. 4 of these 5 files have features that our tool did not support before:
* division in `test2/Gauss.bpl` and `snapshots/Snapshots39.v2.bpl`
* type coercion in `monomorphize/monomorphize2.bpl`
* free pre- and postconditions in a bodyless 
procedure that is invoked in `stratifiedinline/bar13.bpl`

1 of the 5 files was supported already before but we missed it due to 
an error in the selection process: `test21/NameClash.bpl`.

### Benchmarks in table 1
The benchmarks for table 1 are stored in `artifact/boogie_proofgen/ProofGenerationBenchmarks/external_benchmarks/modified`.
`Find.bpl`, `TuringFactorial.bpl` and `DivMod.bpl` are from the Boogie test suite
(they are also in our Boogie test suite benchmarks).
The remaining files (other than `Boogie_Summax_nomap.bpl`) are modified versions
taken from the [BLT test suite](https://github.com/emptylambda/BLT/tree/master/benchmarks/GroupA),
which were used for a paper that we cite.
`Boogie_Summax_nomap.bpl` is a modified version of an example that was used
for a verification competition (given to us by Rosemary Monahan).
The original versions of the files not from the Boogie test suite are stored in
`artifact/boogie_proofgen/ProofGenerationBenchmarks/external_benchmarks/original`.

For many of these files we desugared maps using type constructors, functions,
and axioms. We also added a polymorphic dummy function to each of them, because
if there is no polymorphism in a file, then Boogie's VC generation monomorphizes
the type constructors leading to a different VC (which we don't support yet).

### Generating and checking proofs
We have prepared scripts for generating and checking proofs for the benchmarks.
`artifact/boogie_proofgen/etc/scripts/generate_proofs.py` and
`artifact/boogie_proofgen/etc/scripts/check_proofs.py` can be used to 
generate and check proofs respectively (Note that these scripts don't have
timeouts and so on built-in, but they should work in similar settings too).
Below we show how to use them for the benchmarks.
Note that when setting the dependencies, we built an Isabelle heap image for
the Boogie formalization (`artifact/foundational_boogie`), which means proof 
checking does not need to re-check those proofs (except one opens proofs in the 
Isabelle GUI). If you change any of the Isabelle theory files in 
`artifact/foundational_boogie`, then those files have to be re-built and checking
will take longer.

#### Benchmarks in table 1
For the benchmarks in table 1, one can execute the following:
```
cd ~/artifact/boogie_proofgen/ProofGenerationBenchmarks
python3 ../etc/scripts/generate_proofs.py -i external_benchmarks/modified/ -o table_benchmarks_proofs
python3 ../etc/scripts/check_proofs.py -d table_benchmarks_proofs/ -r 1
```

The call to `generate_proofs.py` generates
 the proofs for all Boogie examples in folder `external_benchmarks/modified/`
(where the table benchmarks are stored) and stores them in the folder `table_benchmarks_proofs`.
Note that the command searches all Boogie examples recursively.
The call to `check_proofs.py` uses Isabelle to check all proofs in the folder `table_benchmark_proofs` and
every proof is checked once (`-r 1`). For each file the script prints whether 
checking the proof was successful or not.
Moreover the call to `check_proofs.py` also generates the average,median,
and standard deviation for the time spent for a single check of the proofs for a
Boogie file (these values are mainly interesting when one selects more than one repetition; 
for example, `-r 3`). This information is stored as a csv file in `table_benchmark_proofs`.

We ran the command with `-r 5` inside the VM (first number) as well as  
via the Windows subsystem for Linux (second number) and obtained the following mean
values (using the same names as in the paper)
1. Find: 31.6 / 27.3
2. MaxOfArray: 24.2 / 19.9
3. DutchFlag: 64.8 / 52.8
4. Plateau: 25.1 / 22.9
5. Summax: 20.9 / 19.1
6. TuringFactorial: 22.1 / 19.4
7. SumOfArray: 21.0 / 18.7
8. ArrayPartitioning: 32.9 / 27.6
9. WelfareCrook: 40.2 / 39.4
10. DivMod: 29.6 / 28.4

The reason the numbers for the Windows subsystem for Linux runs differ w.r.t. 
the paper is that we changed the structure of the certificate slightly. 
In particular, we define global definitions once for all procedures (`global_data.thy`), 
while earlier we defined them for each procedure separately. That's why the numbers for 
examples with more than 1 procedure are smaller than before. We also changed the 
interface of the end-to-end theorem to more directly reflect the result, which 
leads to a bit more overhead (which is why the numbers for examples with 1 procedure 
are slightly worse).

Here the generation of proofs takes around 10 seconds. The checking of proofs takes 
less than 6 minutes (with `-r 1`). All proofs are successfully checked.

Finally, you can count the non-empty Isabelle lines produced for each file using 
the following script:
```
cd ~/artifact/boogie_proofgen/ProofGenerationBenchmarks
python3 ../etc/scripts/count_lines.py -i table_benchmarks_proofs
```
The size of the certificates is similar to the paper for examples with 1 procedure,
but are smaller for those with multiple procedures due to our optimization with
global definitions.

#### Boogie test suite benchmarks
To generate and check proofs for the Boogie test suite benchmarks one can execute
```
cd ~/artifact/boogie_proofgen/ProofGenerationBenchmarks
python3 ../etc/scripts/generate_proofs.py -i boogie_testsuite_benchmarks -o boogie_benchmarks_proofs
python3 ../etc/scripts/check_proofs.py -d boogie_benchmarks_proofs/ -r 1
```

Here the generation of proofs takes less than 2 minutes. The checking of proofs takes
around 40 - 50 minutes. If this is too long, then you can generate proofs for a subset
of the tests by modifying the option "-i" to either take a subfolder or by 
copying a subset of the tests into some other folder that is then given as input.

All proofs are successfully checked, except for 4 files:
* `test20/issue-32.bpl`
* `monomorphize/monomorphize0.bpl`
* `monomorphize/monomorphize2.bpl`
* `test21/NameClash.bpl`

The first two were reported in the paper: The issue is due to calls to polymorphic
functions where the polymorphic return type is an integer or boolean type in a concrete
function call instance. In this case, Boogie uses coercions between raw VC 
integer/boolean values and lifted Boogie integer/boolean values, which we cannot 
handle currently. The other two are files that were not taken into account in the 
paper (see above). `monomorphize2.bpl` seems to have a simple fix that we noticed too late 
and could not incorporate in the artifact: The usages of theorems `expr_equiv_1_neg` and 
`expr_equiv_3_neg` in the proofs must be replaced by 
`expr_equiv_1_neg[where ?type="vc_type_of_val A"]` and 
`expr_equiv_3_neg[where ?type="vc_type_of_val A"]` (i.e., using a more specific
version of the theorem). We still need to investigate how such a general change
affects all other proofs.
`NameClash.bpl` leads to a trivial naming conflict.

The other 4 problematic files that we reported in the paper are now properly
handled. The files are
* `x == e` vs `x <--> e` issue: `test0/Quoting.bpl`, `secure/simple.bpl`, `lock/Lock.bpl`.
   All of these have assignments to boolean variables, which lead to the issue
   (it turns out that the passification itself does not use "assume x <--> e" instead
   of "assume x == e", but a transformation later on makes the change from  "==" to "<-->",
   which had a side effect on the passification CFGs).
*  loop to itself: `aitest1/Linear9.bpl` (before the CFG-to-DAG phase,
Boogie coalesces blocks if possible, that's why there is a loop from a block to itself)
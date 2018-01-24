# Theory Assistant

The Theory Assistant package is a tool for creating, manipulating, and evaluating finite automata. The current state of the package supports only deterministic and non-deterministic finite automata used in the recognition of regular languages. The supported operations on the automata are: union, intersection, complement, Kleene star, equality, and computation. Also implemented is the conversion from NFA to DFA.  The package is written in the scala programming language. The code implementing the NFA and DFA classes may be found in the directory `src/main/scala/theory` in the `NFA.scala` and `DFA.scala` files. The `GNFA` object is used in the conversion from NFA to DFA. The `TypeDefs` file describes a number of useful aliases for the package.

## Getting Started
Once you have downloaded this repository, the only thing you will need to work with it is the programming language scala. Instructions for downloading and installing scala may be found [here](https://www.scala-lang.org/download/). Downloading and installing sbt, the simple build tool, will also make youre life easier. Instructions for downloading and installing sbt may be found [here](http://www.scala-sbt.org/download.html)

### The Test Suite
There are automated test suites implemented for both the DFA and NFA classes. Assume that you have downloaded the Theory Assistant package to the `home\` directory. To run the test suite first open an sbt console:

```
home$ sbt
```
If you have downloaded and installed `sbt` correctly, you should see something like the following:
```
home$ sbt
[info] Set current project to theoryassistant (in build file:/home/TheoryAssistant)
>
```
From here you may issue the `run` command to see a list of available main methods.

```
home$ sbt
[info] Set current project to theoryassistant (in build file:/home/TheoryAssistant)
> run
[info] Compiling 6 Scala sources to home/TheoryAssistant/target/scala-2.10/classes...
[warn] Multiple main classes detected.  Run 'show discoveredMainClasses' to see the list

Multiple main classes detected, select one to run:

 [1] theory.DFATester
 [2] theory.GNFAtester
 [3] theory.NFATester

Enter number:
```
Type the number of the test that you would like to run. You can also run the tests directly with the following:
```
home$ sbt
[info] Set current project to theoryassistant (in build file:/home/TheoryAssistant)
> run-main theory.DFATester
```

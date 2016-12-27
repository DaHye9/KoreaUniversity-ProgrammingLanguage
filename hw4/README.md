# Programming Languages 2016 - Homework 4

## Goal
The goal of this homework is to build an interpreter for the "letrec" language with implicit references.
The syntax and semantics of the language are defined in "hw4.pdf" with some holes which should be completed by yourself.

## Specification
- Implement the ***eval*** function in the "m.ml".
- Do not modify the types and names of items in the "m.ml" except for the ***eval*** function.
- Use the OCaml's *read_int* function for implementing the *read* expression:
  - http://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html
- You can use the environment and memory implementation for the interpreter which are provided as built-in.
- During execution, raise the exception *UndefSemantics* whenever the semantics is undefined.
  - e.g.) ADD expression with a value of Bool type, a conditional consists of a value of Int type
  - You should use the pre-defined exception that we provided.
  - You can raise the exception as follows: ```raise UndefSemantics```

## Compilation and Execution
Compile and execute the interpreter as follows:
```
  make                (* for compilation *)
  ./run test/proc1.m  (* running the interpreter *)
```
Make sure that you are on the top of the project directory where the file "m.ml" exists before compilation.

## How to Submit
Submit the single file "m.ml" via Blackboard. Note that codes which are not compilable will be get zero point.

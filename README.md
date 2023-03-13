# Compiler construction - Latte compiler (October 2022 - January 2023)

Compiler for programming language Latte - translates provided code to quadruple code, then to Asembler x86 32-bit using language Haskell.

Command "make" creates program "latc_x86" and symlink to it "latc". Program is compiled Asembler x86 code.

+ `./latc` - reads program from standard input
+ `./latc path_to_file` - reads program from file

Implemented features:
+ basic types: integer, boolean, string, void
+ basic arythmetic, boolean and string operations
+ while loops, conditions
+ functions
+ classes and objects with inheriting, attributes and virtual methods

First bnfc translates program to Haskell data structure.
Next typechecker catches all syntax errors.
Later program is translated to quadruple code and optimised.
At the end quadruple code is translated to Asembler x86 code and compiled.

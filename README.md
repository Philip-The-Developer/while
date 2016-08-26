While Compiler
==============

This is a compiler for a While language, written in Haskell. The target language is NASM-Assembly.

The compiler is based on the work of Jonas Cleve ("Implementierung eines Compilers für die WHILE-Sprache in Haskell") and Tay Puong Ho ("Erweiterung eines in Haskell implementierten Compilers für eine erweiterte WHILE-Sprache").
The third bachelor thesis ("Umsetzung des Metaklassen-Ansatzes zur Reflexion für einen in Haskell geschriebenen Compiler") introduces Objects and Reflection.
All of these theses were published at Freie Universität Berlin.

Requirements
------------
This compiler is optimized for Linux operating systems.
To compile, nasm and gcc are recommended.

For development, a Haskell Platform with Cabal as package manager are required.
There is a buildscript `build.sh` which builds the parser and compiler for you.

Run `build.sh a` to build the compiler and run the testsuite.

Run `build.sh test` to omit the build sequence and run the testsuite only.

Have fun.

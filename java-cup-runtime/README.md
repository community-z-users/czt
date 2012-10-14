# Java CUP Runtime

This project contains runtime classes of [CUP parser generator for Java][cup-tum].

The source code is split off the main CUP library to allow lighter deployment
of generated parsers: they only need to depend on the runtime.

The code is taken from the [CUP TUM][cup-tum] repository, corresponding to the
released CUP version **0.11a**. Additional fixes are included (revision 20 of
[CUP SVN repository][cup-svn]).

[cup-tum]: http://www2.cs.tum.edu/projects/cup/
[cup-svn]: https://www2.in.tum.de/repos/cup/develop/

## Community Z Tools updates

Updated to use Java Generics and avoid other warnings.

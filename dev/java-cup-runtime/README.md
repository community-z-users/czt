# CUP runtime

This project contains runtime classes of [CUP parser generator for Java][cup].

The source code is split off the main [CUP library][cup] to allow lighter deployment
of generated parsers: they only need to depend on the runtime.

The original code was forked from the [CUP TUM][cup-tum] repository, corresponding to the
released CUP version **0.11a**. Additional fixes are included (revision 20 of
[CUP SVN repository][cup-svn]).

[cup]: ../java-cup/
[cup-svn]: https://www2.in.tum.de/repos/cup/develop/


## Community Z Tools updates (version 0.11-a-czt01)

The official [Java CUP parser generator][cup-tum] is no longer in active development.
This fork features updates added by the Community Z Tools project:

-   Updated to use Java Generics and avoid other warnings.

[cup-tum]: http://www2.cs.tum.edu/projects/cup/


## Usage

CUP runtime is required by parsers generated using [standalone CUP library][cup]
or [CUP Maven plugin][cup-maven].

[cup-maven]: ../cup-maven-plugin/


## License

CUP is released under [CUP License][cup-license] (MIT-like license).
See the included LICENSE file.

[cup-license]: http://www2.cs.tum.edu/projects/cup/licence.html

# CUP parser generator

This project contains a fork of [CUP parser generator for Java][cup-tum].
The CUP parser and lexer are already generated.

This library requires [Java CUP Runtime][cup-runtime], which is split off to allow
lighter deployment of generated parsers: they only need to depend on the runtime.

The original code was taken from the [CUP TUM][cup-tum] [SVN repository][cup-svn],
corresponding to the released CUP version **0.11a**.

[cup-tum]: http://www2.cs.tum.edu/projects/cup/
[cup-svn]: https://www2.in.tum.de/repos/cup/develop/
[cup-runtime]: ../java-cup-runtime/


## Community Z Tools updates (version 0.11-a-czt01)

The official [Java CUP parser generator][cup-tum] is no longer in active development.
This fork features several updates added by the Community Z Tools project:

-   Changed the `java_cup.emit` class to break up each case in the switch statement
    (each case in the parse table) into its own method. Furthermore, very large
    parse table definitions (e.g. action_table) are written to external files
    and loaded during runtime.

    These prevent `do_action()` method and static initialization from growing too large,
    thus avoiding the "`code too large`" Java compiler error. The error appears for very
    large grammars (e.g. in [CZT][czt] parsers).

-   Replaced `System.exit()` calls on fatal errors with unchecked exception. 
    This makes parser generation within IDEs better, since an error in generator no
    longer kills the IDE with it.

-   Also updated to use Java Generics and avoid other warnings.

[czt]: http://czt.sourceforge.net/parser/


## Usage

CUP parser generator can be used standalone. Refer to the [user manual][cup-manual]
for details on usage, configuration options and writing CUP specifications.

[CUP Maven plugin][cup-maven] allows using this CUP parser generator within Maven build.

[cup-manual]: manual.html
[cup-maven]: ../cup-maven-plugin/


## License

CUP is released under [CUP License][cup-license] (MIT-like license).
See the included LICENSE file.

[cup-license]: http://www2.cs.tum.edu/projects/cup/licence.html


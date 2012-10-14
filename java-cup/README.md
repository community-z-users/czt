# Java CUP Parser Generator

This project contains classes of [CUP parser generator for Java][cup-tum].
The CUP parser and lexer are already generated.

This library requires Java CUP Runtime, which is split off the to allow
lighter deployment of generated parsers: they only need to depend on the runtime.

The code is taken from the [CUP TUM][cup-tum] [SVN repository][cup-svn],
corresponding to the released CUP version **0.11a**.

[cup-tum]: http://www2.cs.tum.edu/projects/cup/
[cup-svn]: https://www2.in.tum.de/repos/cup/develop/


## Community Z Tools updates

Changed the `java_cup.emit` class to break up each case in the switch statement
(each case in the parse table) into its own method. This prevents `do_action()`
method from growing too large, thus avoiding the `code too large` Java compiler
error. The error appears for very large grammars (e.g. in [CZT][czt] parsers).

Replaced `System.exit()` calls on fatal errors with unchecked exception. 
This makes parser generation within IDEs better, since an error in generator no
longer kills the IDE with it.

Also updated to use Java Generics and avoid other warnings.

[czt]: http://czt.sourceforge.net/parser


## License

CUP is released under [CUP License][cup-license] (MIT-like license).
See the included LICENSE file.

[cup-license]: http://www2.cs.tum.edu/projects/cup/licence.html


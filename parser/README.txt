Notes
*****
A parser for Z is being developed in the directory
src/net/sourceforge/czt/parser/z


Some Z scanners and markup-converters are contained in the
directory src/net/sourceforge/czt/scanner:
- latex2unicode.jflex is a latex to unicode converter based on jflex
- LatexToUnicode.jj is a latex to unicode converter based on javacc
- unicode.jflex is a unicode scanner that produces tokens (Symbols)
     suitable for input into a parser.   Eventually we plan to connect this
     up to the latex converter to get a Latex-to-Symbols scanner.
- unicode2latex.cup and UnicodeToLatex.java are a converter from
     unicode files (UTF8) into LaTeX markup.

 
Requirements
************

- Java 2 SDK 1.4
  http://java.sun.com/j2se/
- Ant (>= 1.6.0)
  http://ant.apache.org/
- JavaCC
  http://javacc.dev.java.net/
- JFlex
  http://jflex.de/

- Junit (only needed for running the tests)
  http://www.junit.org
- Checkstyle (only needed for checking the source code)
  http://checkstyle.sourceforge.net/

are required to build and run the scanner.

If you don't have one of these installed on your system,
you must download and install it to compile and run the software.

Make sure that ant is in your search path, JFlex.jar and
junit.jar has been copied to <ANT_HOME>/lib/ directory
(as described in <JFLEX_HOME>/doc/jflex_anttask.html and
<ANT_HOME/docs/manual/OptionalTasks/junit.html),
and the properties in <CZT_HOME>/czt.properties are set
to the correct paths for your system.

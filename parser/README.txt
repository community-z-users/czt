Notes
*****
A parser for Z is being developed in the directory
src/net/sourceforge/czt/parser/z
It is based on code provided by Chen Chunqing.

A parser for Object Z is being developed in
src/net/sourceforge/czt/parser/oz
It is based on code provided by Tim Miller.

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

- Java 2 SDK (>= 1.4)
  http://java.sun.com/j2se/
- Ant (>= 1.6.0)
  http://ant.apache.org/
- JavaCC
  http://javacc.dev.java.net/
- Java Cup
  http://www.cs.princeton.edu/~appel/modern/java/CUP/
  (there is usually a version included in Java 2 SDK)
- JFlex
  http://jflex.de/

- Junit (only needed for running the tests)
  http://www.junit.org
- Checkstyle (only needed for checking the source code)
  http://checkstyle.sourceforge.net/

are required to build and run the scanner.

If you don't have one of these installed on your system, you must
download and install it to compile and run the software.

Make sure that ant is in your search path, JFlex.jar and junit.jar has
been copied to <ANT_HOME>/lib/ directory (as described in
<JFLEX_HOME>/doc/jflex_anttask.html and
<ANT_HOME/docs/manual/OptionalTasks/junit.html), and the properties in
<CZT_HOME>/czt.properties are set to the correct paths for your
system.

Compile
*******
Customise the czt properties contained in '<CZT_HOME>/czt.properties',
change to the directory where this file is in, and call ant.  By
default, ant will build the jar files.
Optionally, you can pass an argument to Ant.  Call "ant -projecthelp"
to get help information about which arguments are available.

You can test the Object Z parser by running './run.sh file'.  This
will parse the toolkits (number, sequence, object-z toolkits etc.) and
then parse the file supplied on the line. It only accepts one file at
this primitive stage. This will produce a basic GUI (thanks to Petra
for the code for that!) with your specification as a JTree. If you
just type './run.sh' (or 'ant run') this will start the GUI with
just the toolkits in the tree.

Troubleshooting
***************

If you have problems building the parser using the java cup task,
you may also run the shell script './cup.sh'.  Make sure to first
run 'ant install-bin' in <CZT_HOME>.

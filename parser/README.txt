---------------------
Welcome to CZT Parser
---------------------

Parser is part of the CZT project that aims at providing a framework
for building formal methods tools, especially for the Z specification
language.

This subproject contains parser and printer utilities supporting
LaTex markup and pure unicode.  E-mail markup support is planned.

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

are required to build and run the parser.

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

You can test the Object Z parser by running './run.sh file'.  This will
parse the toolkits (number, sequence, object-z toolkits etc.) and then
parse any files supplied on the command line. This will produce a basic
GUI (thanks to Petra for the code for that!) with your specification as
a JTree. If you just type './run.sh' (or 'ant run') this will start the
GUI with just the toolkits in the tree.

Troubleshooting
***************

If you have problems building the parser using the java cup task,
you may also run the shell script './cup.sh'.  Make sure to first
run 'ant install-bin' in <CZT_HOME>.

If you get
  Error: JFlex has run out of memory. Please try increasing the maximum
         JVM heap size
set the environment variable ANT_OPTS to increase the heap size.
'export ANT_OPTS=-Xmx100m' works for me.


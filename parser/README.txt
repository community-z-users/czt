Notes
*****
- There is a scanner.xml ant build file for building the scanner
  (try 'ant -f scanner.xml test' for running some tests).
  Hopefully scanner.xml will be moved to build.xml when the parser
  starts using the new scanner.

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
appropriatly.

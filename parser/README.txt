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

- Java 2 SDK (>= 1.5)
  http://java.sun.com/j2se/
- Ant (>= 1.6.0)
  http://ant.apache.org/
- JFlex (>= 1.4.1)
  http://jflex.de/

- Junit (only needed for running the tests)
  http://www.junit.org
- Checkstyle (only needed for checking the source code)
  http://checkstyle.sourceforge.net/

are required to build and run the parser.

If you don't have one of these installed on your system, you must
download and install it to compile and run the software.

This subproject also depends on other CZT subprojects.  You need to
compile and install the CZT subprojects corejava and the ant-task
located in devtools/ant before you can compile the parser.

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

Troubleshooting
***************

If you get

  Error: JFlex has run out of memory. Please try increasing the maximum
         JVM heap size

set the environment variable ANT_OPTS to increase the heap size.
'export ANT_OPTS=-Xmx100m' works for me.



If you get

  taskdef class JFlex.anttask.JFlexTask cannot be found

you probably forgot to copy the JFlex.jar file into the
<ANT_HOME>/lib directory (see requirements section above).

             CZT          Community Z Tools
             ==============================

The CZT project aims to provide a set of tools for editing, typechecking
and animating formal specifications written in the Z specification
language.  It provides a Java framework for building formal methods tools.

It includes the following sub-projects 
(not all of these will be included in a given release)

admin/       Tools for administration, preparing releases, ...
corejava/    Java AST classes for standard Z
doc/         General Documentation and Articles
gaffe/       GUI-builder for Z animators
gnast/       GeNerate AST classes from XML schemas
jedit/       Support for editing Z with the JEdit editor
parser/      Parses and prints Z specs (various markups) into and from ZML
translators/ Various tools for translating into and from ZML
typechecker/ Typechecks a ZML file
web/         Sources to the czt.sourceforge.net web site
zml/         XML schemas for Z and examples

The file czt.properties controls various properties used for
building and running czt software.  Please have a look at this
file and adjust the settings according your needs.

See the README file in each directory for more details on each sub-project.

See the CZT web site for general details about CZT:

      http://czt.sourceforge.net

Requirements
************
Please read the README.txt files within the sub-projects directories
to learn the requirements for each of the subproject you want to use.
For instance, read '<CZT_HOME>/corejava/README.txt' to get detailed
information on requirements for the corejava sub-project.

Most of the sub-projects will need the following:
- Java 2 SDK 1.4
  http://java.sun.com/j2se/
- Ant
  http://ant.apache.org/
- Java Web Services Developer Pack (JWSDP) 1.3
  http://java.sun.com/webservices/downloads/webservicespack.html

If you don't have one of these installed on your system,
you should download and install it to compile and run czt.

Make sure that ant is in your search path, and set the properties
in the file '<CZT_HOME>/czt.properties' appropriately.

Compile
*******
Customise the file czt.properties and call ant.  By default, ant will
build the jar files and install them in the '<CZT_HOME>/lib' directory.
Optionally, you can pass an argument to Ant.  Call "ant -projecthelp"
to get help information about which arguments are available.

What next?
**********
The sub-projects README files provide more information on how the
subprojects can be used.  You may also want to have a look at the
command line tools in '<CZT_HOME>/bin'.
Currently, the beanshell script provides a nice way to explore
czt.  You need to install beanshell (http://www.beanshell.org)
and provide its location in czt.properties before compiling czt.
Just call the script beanshell which is located in CZT_HOME/bin.
Then type 'importCommands("bsh");' to get access to the czt
commands provided in '<CZT_HOME>/bin/bsh'.

Example files are located in '<CZT_HOME>/zml/examples'.

Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

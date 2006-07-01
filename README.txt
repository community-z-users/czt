             CZT          Community Z Tools
             ==============================

The CZT project aims to provide a set of tools for editing, typechecking
and animating formal specifications written in the Z specification
language, and some extension of Z, such as Object-Z.  
It provides a rich Java framework for building formal methods tools.

It includes the following sub-projects in the form of sub-directories
in <CZT_HOME> (which is the directory where this README is in).
Note that not all of these may be included in a given release.

corejava/    Java AST classes for standard Z
java_cup/    The Java Cup parser generator adabted for the CZT project
jaxb/        Support classes for reading/writing Z XML files.
jedit/       Several CZT plugins for the JEdit editor
modeljunit/  Model-based unit testing, used by ZLive
parser/      Parses and prints Z specs (various markups) into and from ZML
rules/       Support for Z AST transformation rules (see doc/papers/rules)
typechecker/ Typechecks Z and Object-Z specifications
util/        Support classes that are independent of Z
web/         Sources to the czt.sourceforge.net web site
zlive/       Z animator
zml/         XML schemas for Z and several Z extensions, with examples

Here are the main dependencies between these projects:
jaxb         uses:  util
corejava     uses:  jaxb
parser       uses:  session, java_cup
typechecker  uses:  parser
rules        uses:  typechecker
zlive        uses:  typechecker, modeljunit
jedit        uses:  zlive

See the README file in each directory for more details on each sub-project.

See the CZT web site for general details about CZT:

      http://czt.sourceforge.net


Compiling
*********

Currently, there are two alternatives to compile CZT.
The recomended way is to use maven.  It doesn't require to install so
many things since maven downloads the dependencies automatically.
Using ant is the more traditional way but it requires to install all
the 3rd party software in advance.  It also requires to set the paths
to the installed software in the czt.properties file appropriately,
which is cumbersome.


Compiling using maven
*********************

You need at least the following:
- Java 2 SDK >= 1.5
  http://java.sun.com/j2se/
- Maven version >= 2.0.4
  http://maven.apache.org/
to build CZT.  If you don't have these installed on your system,
you should download and install them before you can build czt.

Maven will download most of the dependencies automatically.
However, there are a few things that maven can't download
for you.  This includes
jflex (downloadable from http://jflex.de/download.html),
jEdit (downloadable from http://jedit.org/index.php?page=download),
and jEdit plugins that can be downloaded using the jEdit plugin
manager.  Please follow the instructions given by maven to install
those in the maven respository so that maven can find them.

To build CZT, you need to increase the Java heap size to at least
256Mb, which is done by seting the MAVEN_OPTS environment variable
to "-Xmx256m".

To build CZT, change into the (top level) CZT directory (<CZT_HOME>),
and call
  mvn install
This should install all the CZT tools into your local maven
repository, ready to be used in your own projects.  It should also
create jar files in <CZT_HOME>/bin as well as <CZT_HOME>/jedit/bin.

The jar file in <CZT_HOME>/bin is an (command line) executable jar
file, which can be executed by calling
  java -jar czt-dep.jar

See <CZT_HOME>/jedit/README.txt for how to install the various jEdit
plugins in <CZT_HOME>/jedit/bin.


Compiling using ant
*******************

Most of the sub-projects will need at least the following:
- Java 2 SDK >= 1.5
  http://java.sun.com/j2se/
- Ant version >= 1.6
  http://ant.apache.org/
- Java Web Services Developer Pack (JWSDP) >= 1.5
  http://java.sun.com/webservices/downloads/webservicespack.html

If you don't have these installed on your system,
you should download and install them before you compile and run czt.

Additional requirements are described in the top-level czt.properties
file--you should start by reading that file, checking that you have
installed the libraries/tools that are needed for the subprojects
that you want to use, and set the paths to point to the correct
installation locations for your system.

More information about the requirements for each subproject can
often be obtained from the README.txt files within the sub-projects
directories (but these are sometimes less up-to-date than czt.properties).
For instance, read '<CZT_HOME>/corejava/README.txt' to get detailed
information on requirements for the corejava sub-project.

1. Customise the file czt.properties.
   CZT relies on quite a few (10-15!) external libraries and tools.
   You will need to install these and change the paths in czt.properties
   to point to the correct location of these libraries/tools on your system.
   Each path variable in czt.properties includes a URL to obtain
   the library/tool from, and a recommended version to use.
   We suggest that you use the recommended versions to get CZT
   working correctly, before you experiment with newer (or older)
   versions.  Most problems with compiling CZT are due to differences
   between versions of external libraries.

2. Call `ant -Xmx256m'
   You will need to have ant in your path to do this, obviously.
   You should also ensure that JUnit is correctly installed and known
   to ant (you should have the JUnit*.jar file in ant's lib directory).

   The argument increases the Java heap size to 256Mb, which is 
   necessary to build some of the CZT parsers.
   Alternatively, you can set the ANT_OPTS environment variable
   to -Xmx256m before you call ant.

   By default, ant will build the jar files and install them in 
   the '<CZT_HOME>/lib' directory.  Optionally, you can pass an 
   argument to ant.  Call "ant -projecthelp" to get help information 
   about which arguments are available.

3. Enjoy CZT!  (See the "What next?" section below)


Troubleshooting
***************
Please read the README.txt file within the sub-project you have
trouble with.


What next?
**********
There are at least three ways of using the CZT tools.

1. From within jEdit.
   The CZT plugin for the jEdit editor gives WYSIWYG editing of
   the Unicode markup for Z, template-based insertion of Z constructs
   for LaTeX and Unicode markup, automatic typechecking on each save,
   a SideKick panel that shows the structure of your Z specification
   and much much more.  See jedit/README.txt for instructions.

2. Command line tools.  
   See '<CZT_HOME>/bin'.   The *.bat scripts are for Windows (and Cygwin),
   while the scripts with no extensions are for Linux etc.
   Example:  bin/zedtypecheck[.bat] -t zml/examples/z/birthdaybook.tex 

3. Interactively via beanshell.
   This is a good way for programmers to experiment with the
   APIs offered by CZT and to view results (such as XML files).
   You need to install beanshell (http://www.beanshell.org)
   and provide its location in czt.properties before compiling czt.
   Just call the script beanshell which is located in CZT_HOME/bin.
   Then type 'importCommands("bsh");' to get access to the czt
   commands provided in '<CZT_HOME>/bin/bsh'.

The sub-projects README files provide some more information on how each
subproject can be used.  

Example files are located in '<CZT_HOME>/zml/examples'.


Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

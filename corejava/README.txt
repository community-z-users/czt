-------------------
Welcome to corejava
-------------------

Corejava is part of the CZT project that aims at providing a framework
for building formal methods tools, especially for the Z specification
language.

For more information, please have a look in the doc/ directory, as
well as the CZT web site
http://czt.sourceforge.net/

Here is a description of what each of the top level directories
contains:

build/      This is a temporary build directory.
doc/        This is where the documentation lives.
examples/   This is where the examples live.
src/        This is where all of the source code lives.
tests/      This is where all of the tests live.
            
Requirements
************

- Java 2 SDK 1.4
  http://java.sun.com/j2se/
- Ant
  http://ant.apache.org/
- Java Web Services Developer Pack (JWSDP) 1.3
  http://java.sun.com/webservices/downloads/webservicespack.html
- Junit (only needed for running the tests)
  http://www.junit.org
are required to build and run corejava.

If you don't have one of these installed on your system,
you must download and install it to compile and run the software.

Make sure that ant is in your search path, and set the property
jwsdp.classpath in the file '<CZT_HOME>/czt.properties'.

Compile
*******
Customise the czt properties contained in '<CZT_HOME>/czt.properties',
change to the directory where this file is in, and call ant.  By
default, ant will build the jar files and the API documentation
located in doc/api.
Optionally, you can pass an argument to Ant.  Call "ant -projecthelp"
to get help information about which arguments are available.

What next?
**********
Have a look in the examples directory.  Here is a short overview:

	debug			- shows how the corejava classes can
				  be debuged
	marshal			- marshalling to XML (into a file
				  or to stdout)
	object-z                - marshalling and unmarshalling
                                  object Z specifications
                                  (shows what kind of errors are to be
                                  expected when the
                                  wrong reader or writer is used)
	substitutionVisitor 	- an example of a visitor;
		learn how you can write your own visitor for the AST
		classes and perform some kind of substitution
	unmarshal		- unmarshalling an XML file

Read the API documentation in doc/api (you have to build it by calling
'ant' or 'ant api' before you can read it).

Hava a look in the tests directory.  It shows how the classes are
supposed to work.

Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

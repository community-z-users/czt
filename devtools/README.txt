-------
CUP-TUM 
-------

This directory contains only the generated source code that is part of
the CUP-TUM package (http://www2.cs.tum.edu/projects/cup/). The CUP
grammar and lexer are not included in this release, so that CZT
developers need not have to worry about problems faced when using CUP
to build itself. This package is NOT part of the CZT project.

The build script takes the source code, and changes the package name
from java_cup to net.sourceforge.czt.java_cup to avoid clashes with
JEdit plugins that use older versions of CUP.

Requirements
************

- Java 2 SDK (>= 1.5)
  http://java.sun.com/j2se/
- Ant (>= 1.6.0)
  http://ant.apache.org/

are required to build and run CUP-TUM.

To Compile
**********
Customise the czt properties contained in '<CZT_HOME>/czt.properties',
change to the directory where this file is in, and call ant.  By
default, ant will build the jar files.
The two properties needed to be set in '<CZT_HOME>/czt.properties' for
this project are:
 - java_cup.jar.file: the name of the jar file containing the class
   files that is generated from this code.
 - java_cup.runtime.jar.file: the name of the jar file containing only
   the runtime classes (the code necessary for use by a parser written
   using CUP-TUM).

Then type 'ant install', and it will install the CUP-TUM jar files
into the CZT library directory.

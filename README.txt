             CZT          Community Z Tools
             ==============================

The CZT project aims to provide a set of tools for editing, typechecking
and animating formal specifications written in the Z specification
language, and some extension of Z, such as Object-Z.  
It provides a rich Java framework for building formal methods tools.

It includes the following sub-projects in the form of sub-directories
in <CZT_HOME> (which is the directory where this README is in).
Note that not all of these may be included in a given release.

admin/       Tools for administration, preparing releases, ...
corejava/    Java AST classes for standard Z
devtools/    Some libraries (java_cup etc.) and tables of Z characters
doc/         General Documentation and Articles
eclipse/     A CZT plugin for Eclipse (under development)
gaffe/       GUI-builder for Z animators
gnast/       GeNerate AST classes (into corejava and jaxb) from XML schemas
jaxb/        Support classes for reading/writing Z XML files.
jedit/       Several CZT plugins for the JEdit editor
modeljunit/  Model-based unit testing, used by ZLive
parser/      Parses and prints Z specs (various markups) into and from ZML
rules/       Support for Z AST transformation rules (see doc/papers/rules)
translators/ Various tools for translating into and from ZML
typechecker/ Typechecks Z and Object-Z specifications
util/        Support classes that are independent of Z
web/         Sources to the czt.sourceforge.net web site
zlive/       Z animator
zml/         XML schemas for Z and several Z extensions, with examples

See the README file in each directory for more details on each sub-project.

See the CZT web site for general details about CZT:

      http://czt.sourceforge.net

See INSTALL.txt on how to compile CZT.

Licensing
*********

Most of the CZT software is licensed under the GNU General Public
License, which can be found in the file COPYING in this directory.

The "CZT Sans" font is derived from the Bitstream Vera Sans
font (about 120 Z characters were added), and is distributed
under the original Bitstream Vera Copyright, as follows.
See http://www.gnome.org/fonts for details.

JDSL, which is part of modeljunit, is licensed under a BSD style
license; see file LICENSE.jdsl in this directory for more information.

3rd party licenses:

Java CUP is licensed under the Standard ML of New Jersey.
See LICENSE.cup in this directory for more information.

JAXB is part of JWSDP.  Its license can be found at
http://java.sun.com/webservices/docs/1.5/LICENSE

JFlex is licensed under the GNU General Public License.

JUnit is licensed under the Common Public License
http://www.opensource.org/licenses/cpl.php

Running CZT
***********

There are at least two ways of using the CZT tools.

1. From within jEdit.

   The CZT plugins for the jEdit editor gives WYSIWYG editing of the
   Unicode markup for Z, template-based insertion of Z constructs for
   LaTeX and Unicode markup, automatic typechecking on each save, a
   SideKick panel that shows the structure of your Z specification and
   much much more.  See jedit/README.txt for more information.

2. Command line tool.

   The jar file <CZT_HOME>/lib/czt-dep.jar
   can be executed by calling
     java -jar czt-dep.jar

   Calling it without arguments as shown here prints usage information.

Example files are located in '<CZT_HOME>/zml/examples'.

There is a CZT font that supports the Z Starndard characters in the
<CZT_HOME>/fonts directory.  See the README.txt file in the fonts
directory for more information of how to install and use the font.


Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

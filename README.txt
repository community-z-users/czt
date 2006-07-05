             CZT          Community Z Tools
             ==============================

The CZT project aims to provide a set of tools for editing, typechecking
and animating formal specifications written in the Z specification
language, and some extensions of Z, such as Object-Z, TCOZ, and Circus.  
It provides a rich Java framework for building formal methods tools.

See the CZT web site for more information about CZT:
      http://czt.sourceforge.net

If you are dealing with a source version of CZT, please follow the
instructions in INSTALL.txt to get it compiled and installed.  This
will create jar files in <CZT_HOME>/bin and <CZT_HOME>/jedit/bin (or,
if ant has been used, in the directories set up in czt.properties,
usually lib and <CZT_HOME>/lib/jedit) for you.  Note that <CZT_HOME>
is the top level directory of CZT.
In a binary release, the jar files will be already there.

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
   much much more.  See jedit/README.txt for more information.  You
   will need the jar file <CZT_HOME>/bin/czt-dep.jar (ant users can
   use <CZT_HOME>/lib/czt.jar but be aware that it doesn't include 3th
   party libraries) and the various plugin jar files in
   <CZT_HOME>/jedit/bin (or <CZT_HOME>/lib/jedit).

2. Command line tool.

   The jar file <CZT_HOME>/bin/czt-dep.jar (or <CZT_HOME>/lib/czt.jar)
   can be executed by calling
     java -jar czt-dep.jar
     (or java -jar czt.jar correspondingly)
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

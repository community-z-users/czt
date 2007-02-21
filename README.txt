             CZT          Community Z Tools
             ==============================

The CZT project aims to provide a set of tools for editing, typechecking
and animating formal specifications written in the Z specification
language, and some extension of Z, such as Object-Z, TCOZ, and Circus.
It provides a rich Java framework for building formal methods tools.
See the CZT web site for general details about CZT:

      http://czt.sourceforge.net

See INSTALL.txt on how to compile CZT (only for source distributions).


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

There is a CZT font that supports the Z Starndard characters in the
<CZT_HOME>/fonts directory.  See the README.txt file in the fonts
directory for more information of how to install and use the font.


Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

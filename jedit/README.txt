--------------------------------------
Welcome to the jEdit subproject of CZT
--------------------------------------

The aim of this project is to provide WYSIWYG editing of Z specifications 
in Unicode markup using the jEdit editor (see http://www.jedit.org).

For more information about CZT, please have a look at our web site
http://czt.sourceforge.net/
We encourage you to file bugs, ask for help, provide patches, etc.
All this can be done starting from our sourceforge site
http://sourceforge.net/projects/czt/

NOTE: The jEdit subproject is experimental, and highly subject to change!

Requirements
************

- jEdit
  http://www.jedit.org

The plugins and extension provided in this directory
have been tested using jEdit version 4.2final and 4.3pre9.

Installation
************

In the following, it is assumed that jEdit has already been installed
and <JEDIT_SETTINGS_DIR> is the jEdit settings directory (this might be
the global settings directory as well as the user specific settings
directory).  The location of this directory is system-specific.  On a
linux machine, for example, the user specific settings directory is
usually ~/.jedit.  See jEdit User's Guide for more information on
jEdits's settings directory.

a) Installing the jEdit plugins
--------------------------------------------

If you are working with a source distribution, follow the instructions
in <CZT_HOME>/INSTALL.txt to compile and install CZT.  This creates
jar files in <CZT_HOME>/lib, including the plugin jar files mentioned
below.

To install a jEdit plugin, first make sure to deinstall previous
versions.

To install the ZCharMap plugin you need to:
  1. copy <CZT_HOME>/lib/ZCharMap.jar to JEDIT_SETTINGS_DIR/jars

To install the ZSideKick plugin you need to:
  1. Install the SideKick and ErrorList plugin
     using jEdit's Plugin manager
  2. copy <CZT_HOME>/lib/ZSideKick.jar to JEDIT_SETTINGS_DIR/jars
     AND <CZT_HOME>/lib/czt.jar to JEDIT_SETTINGS_DIR/jars/czt.jar
  3. update the catalog file in JEDIT_SETTINGS_DIR/modes
     (see the paragraph about installing the Z modes below)

To install the ZLive plugin you need to:
  1. Install the Console plugin using jEdit's Plugin manager,
  2. install the ZSideKick plugin as described above, and
  3. copy <CZT_HOME>/lib/ZLivePlugin.jar to JEDIT_SETTINGS_DIR/jars

Please restart jEdit to load the new plugins.

b) Installing the Z modes
-------------------------

The file zed.xml contains the beginnings of a jEdit syntax-colouring
mode for Z in Unicode mark-up that highlights Z paragraphs and Z
keywords.  To install it,

   1. copy zed.xml to JEDIT_SETTINGS_DIR/modes
   2. update the catalog file in JEDIT_SETTINGS_DIR/modes
      as given by the example catalog file located in this directory

Please also see Chapter 10 of the jEdit User's Guide for complete
instructions on installing edit modes.


What next?
**********

Documentation for each of the plugins can be found in jEdit's Help
system.  The plugins are accessible via jEdit's menu
Plugins/<plugin-name>.  Is is also possible to dock each of the
plugins.  To do this, edit Global Options/Docking and see the jEdit
documentation for more information.


NOTES AND WARNINGS
******************

Depending upon which font you use (to change the font, see
Utilities/Global Options/jEdit/Text Area/Text Font), you may
see some Z characters as empty boxes, because most fonts do not
support all unicode characters.  You should install the CZT font
to get best results.

jEdit cannot distinguish UTF8 files from plain-ASCII files (they can
be identical), so when you load an UTF8 file, you must RIGHT-CLICK on
the filename in the Open browser, then set the Encoding to UTF8 BEFORE
Opening it.

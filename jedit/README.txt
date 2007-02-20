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

Here is a short description of the directories and files contained.
Note that not all of these may be included in a given release.
   Zchars.utf8     A list of all Z unicode characters (UTF8).
   Zchars.utf16    A list of all Z unicode characters (UTF16).
                   (This is useful to see which chars your font supports)

   zed.xml         The beginnings of a jEdit syntax-colouring mode for Z.

   catalog         An example catalog file.

   zcharmap/       A jEdit plugin that displays special Z characters
                   and allows you to click on them to insert them.

   zsidekick/      A jEdit plugin for parsing and typechecking
                   Z specifications.

   zlive/          A jEdit plugin for the ZLive animator.


Requirements
************

- jEdit
  http://www.jedit.org

The plugins and extension provided in this directory
have been tested using jEdit version 4.2final and 4.3pre9.

Installation
************

In the following, it is assumed that SETTINGS_DIR is the
jEdit settings directory (this might be the global settings
directory as well as the user specific settings directory).
The location of this directory is system-specific (see
jEdit User's Guide; Customizing jEdit). The user specific
settings directory for jedit on a unix machine is usually
~/.jedit

a) Installing the Z mode
------------------------

zed.xml contain the beginnings of a jEdit syntax-colouring mode for Z.

   1. copy zed.xml to SETTINGS_DIR/modes
   2. update the catalog file in SETTINGS_DIR/modes
      (see the catalog file to see how to do this)

Please see Chapter 10 of the jEdit User's Guide for complete
instructions on installing edit modes.


b) Installing the jEdit plugins
--------------------------------------------
Change into <CZT_HOME>, the top level directory of CZT, and
follow the instructions in INSTALL.txt to install CZT.
This creates jar files in <CZT_HOME>/lib, including the plugin
jar files mentioned below.

To install a jEdit plugin, first make sure to deinstall previous
versions.

To install the ZCharMap plugin you need to:
  1. copy ZCharMap.jar to SETTINGS_DIR/jars
  2. restart jEdit to load the new plugin

To install the ZSideKick plugin you need to:
  1. Install the SideKick and ErrorList plugin
     using jEdit's Plugin manager
  2. copy ZSideKick.jar to SETTINGS_DIR/jars
     AND czt-dep.jar to SETTINGS_DIR/jars/czt.jar
  3. update the catalog file in SETTINGS_DIR/modes
     (see the catalog file to see how to do this)
  4. restart jEdit to load the new plugin

To install the ZLive plugin you need to:
  1. Install the Console plugin using jEdit's Plugin manager,
  2. install the ZSideKick plugin as described above, and
  3. copy ZLivePlugin.jar to SETTINGS_DIR/jars
  3. restart jEdit to load the new plugin


What next?
**********

Load one of the example files.

Depending upon which font you use (to change the font, see
Utilities/Global Options/jEdit/Text Area/Text Font), you may
see some Z characters as empty boxes, because most fonts do not
support all unicode characters.  You should install the CZT font
to get best results.

If you have the Z mode installed, the Z paragraphs should
be highlighted differently than the text between them.

The plugins are accessible via menu Plugins/<plugin-name>.
Is is also possible to dock each of the plugins. To do this,
edit Global Options/Docking.

NOTES AND WARNINGS
******************

jEdit cannot distinguish UTF8 files from plain-ASCII files (they can
be identical), so when you load a UTF8 file, you must RIGHT-CLICK on
the filename in the Open browser, then set the Encoding to UTF8 BEFORE
Opening it.

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

Here is a short description of the directories and files contained:
   bbook.utf8      Small birthday book example in UTF8 (8-bit) unicode.
   bbook.utf16     Small birthday book example in UTF16 (16-bit) unicode.

   Zchars.utf8     A list of all Z unicode characters (UTF8).
   Zchars.utf16    A list of all Z unicode characters (UTF16).
                   (This is useful to see which chars your font supports)

   zed.xml         The beginnings of a jEdit syntax-colouring mode for Z.

   catalog         An example catalog file which shows how the
                   syntax-colouring mode for Z can be installed.

   ZCharMap/       A jEdit plugin that displays special Z characters
                   and allows you to click on them to insert them.

   z.cliplibrary   An alternative way of inserting Z characters, by using
                   the Clipper plugin.

   z.insert.xml    Yet another alternative way of inserting Z characters,
                   using the XInsert plugin.

Requirements
************

- jEdit
  http://www.jedit.org

The plugins and extension provided in this directory
have been tested using jEdit version 4.1final.

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


b) Installing the Z character map (ZCharMap)
--------------------------------------------
A jEdit plugin that displays special Z characters
and allows you to click on them to insert them.

This seems better than the following approaches, but
you must edit ZCharMap/ZCharMap.java and rebuild the
plugin to add new chars.

To compile this plugin you need to install
- Java 2 SDK
  http://java.sun.com/j2se/
- Ant
  http://ant.apache.org/

To build ZCharMap you need to:
  1. change into directory ZCharMap
  2. set your jEdit install directory in build.xml
  3. call ant

To install ZCharMap you need to:
  4. copy ZCharMap.jar to SETTINGS_DIR/jars
  5. restart jEdit to load the new plugin


c) Installing Zed in Clipper
----------------------------
  1. install the Clipper plugin
  2. create the directory SETTINGS_DIR/clipper
  3. copy z.cliplibrary to  SETTINGS_DIR/clipper
  4. Use Utilities/Global-Options/Plugins/Clipper and
     set the Clipper directory to SETTINGS_DIR/clipper
  5. restart jEdit to reload the new clipper library


d) Installing Zed in XInsert
----------------------------
  1. install the XInsert plugin
  2. copy the z.insert.xml file into
     SETTINGS_DIR/xinsert (this directory can be customized
     -- see the XInsert documentation)

What next?
**********

Load one of the example files (bbook.utf16 or bbook.utf8).

Depending upon which font you use (to change the font, see
Utilities/Global Options/jEdit/Text Area/Text Font), you may
see some Z characters as empty boxes, because most fonts do not
support all unicode characters.  Some Z characters, like partial
functions, were added to the Unicode standard quite recently, so 
very few fonts support them yet.  This will change (I hope)...
One of the best fonts is "Arial Unicode MS" (comes with Microsoft Office)
but it still does not have the newest Z characters.

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



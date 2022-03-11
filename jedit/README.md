# CZT plugins for jEdit

[![CZT plugins for jEdit](images/thumb-czt-jedit.png)]( images/czt-jedit.png "CZT plugins for jEdit" )

The aim of this project is to provide WYSIWYG editing of Z specifications 
in Unicode markup using the [jEdit editor][jedit].

Currently CZT provides the following plugins:

-   [**ZSideKick**][zsidekick] - parsing and typechecking Z specifications, display document
    structure and errors
-   [**ZCharMap**][zcharmap] - a palette of Z characters and elements for easy input in LaTeX
    and Unicode markups.
-   [**ZLive**][zlive] - integrates [ZLive][zlive-proj] animator in jEdit console.
-   [**Z/EVES**][zeves] - integrates Z/EVES theorem prover in jEdit console.

Refer to each plugin information for more details.

NOTE: The jEdit subproject is experimental, and highly subject to change!

[jedit]: http://www.jedit.org
[zlive-proj]: ../zlive/
[zsidekick]: ZSideKick/
[zcharmap]: ZCharMap/
[zlive]: ZLivePlugin/
[zeves]: ZEvesPlugin/


## Requirements

-   [Java 6](http://www.java.com/getjava/)
-   [jEdit][jedit]

The CZT plugins and extensions should be working using jEdit 5.

## Installation

In the following, it is assumed that jEdit has already been installed and `JEDIT_SETTINGS_DIR`
is the jEdit settings directory (this might be the global settings directory as well as the
user-specific settings directory). The location of this directory is system-specific.
On a Linux machine, for example, the user specific settings directory is usually _~/.jedit_.
See jEdit User's Guide for more information on jEdits's settings directory.

### Installing the jEdit plugins

If you are working with a source distribution, follow the [CZT setup instructions][czt-setup]
to compile and install CZT. This creates jar files in `CZT_HOME/lib`, including the plugin
jar files mentioned below.

To install a jEdit plugin, first make sure to uninstall previous versions.

-   To install the [**ZCharMap** plugin][zcharmap] you need to:
    
    1.   Copy `ZCharMap.jar` to `JEDIT_SETTINGS_DIR/jars`
    
-   To install the [**ZSideKick**][zsidekick] plugin you need to:
    
    1.  Install the SideKick and ErrorList plugin using jEdit's Plugin manager.
    2.  Copy `ZSideKick.jar` to `JEDIT_SETTINGS_DIR/jars`.
    3.  Copy `czt.jar` to `JEDIT_SETTINGS_DIR/jars`.
    4.  Update the `catalog` file in `JEDIT_SETTINGS_DIR/modes`
        (see the paragraph about installing the Z modes below).
    
-   To install the [**ZLive** plugin][zlive] you need to:
    
    1.  Install the Console plugin using jEdit's Plugin manager.
    2.  Install the ZSideKick plugin as described above.
    3.  Copy `ZLivePlugin.jar` to `JEDIT_SETTINGS_DIR/jars`
    
-   The installation for [**Z/EVES** plugin][zeves] is identical to ZLive plugin.

Please restart jEdit to load the new plugins.

[czt-setup]: ../dev/setup.html


### Installing the Z modes

The files in `modes` directory (e.g. `zed.xml`) contain the beginnings of a jEdit syntax-colouring
mode for Z in Unicode mark-up that highlights Z paragraphs and Z keywords.
To install it, you need to:

1.  Copy `zed.xml` to `JEDIT_SETTINGS_DIR/modes`.
2.  Update the `catalog` file in `JEDIT_SETTINGS_DIR/modes` as given by the example `catalog` file
    located in this directory

Please also see Chapter 10 of the jEdit User's Guide for complete instructions on installing edit
modes.


## What next?

Documentation for each of the plugins can be found in jEdit's Help system. The plugins are
accessible via jEdit's menu `Plugins/plugin-name`. Is is also possible to dock each plugin.
To do this, edit Global Options/Docking and see the jEdit documentation for more information.


## Notes and warnings

Depending upon which font you use (to change the font, see
`Utilities/Global Options/jEdit/Text Area/Text Font`), you may see some Z characters as empty
boxes, because most fonts do not support all Unicode characters. You should install the
[CZT font][font] to get the best results.

jEdit cannot distinguish UTF8 files from plain-ASCII files (they can be identical), so when you
load an UTF8 file, you must **right-click** on the filename in the Open browser, then set the
Encoding to UTF8 **before** opening it.

[font]: ../font.html


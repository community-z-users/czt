             CZT          Community Z Tools
             ==============================
  
  The Community Z Tools (CZT) project is an open-source Java framework
  for building formal methods tools for Z and Z dialects.  It also
  includes a set of tools for parsing, typechecking, transforming and
  printing standard Z specifications in LaTeX, Unicode and XML
  formats, plus a jEdit plugin which gives WYSIWYG editing of Z
  specifications and buttons for some of the most common CZT tools.
  
  So, you can run the CZT tools via the jEdit plugin (best for new users), 
  or from within a beanshell command prompt (good for programmers).
  
1. Requirements
***************

- Java 2 SDK >= 1.5
  http://java.sun.com/j2se/

- jEdit >= 4.1
  http://jedit.org/
  if you want to use the jEdit plugin

2. Run CZT using the jEdit plugin
*********************************

CZT provides a jEdit plugin providing parsing, typechecking and 
editing facilities for Z specifications in LaTeX or Unicode.
It includes a Z Unicode font called "CZT" which contains all the 
special Z characters defined in the ISO Z standard.  This font is used
to display the Z characters in the entry palette (which is useful for
both Unicode and LaTeX Z users) as well as display Z characters
in any Unicode specifications that you edit.

2.1 Installing the CZT jEdit plugin
-----------------------------------

First make sure jEdit is really using Java 1.5.
(Under Windows, you can check the properties of your jEdit shortcut
and make sure it is using the Java 1.5.x javaw.exe program).

Since the plugin is installed manually (not using the plugin manager),
we also need to take care of the plugin's dependencies.  The ErrorList
plugin is required by the CZT plugin, so please install the "ErrorList"
plugin from within jEdit's plugin manager, and then use the 
"Plugins / ErrorList / Error List" menu entry to start up the ErrorList plugin.
We like to dock the ErrorList window at the bottom of the main jEdit window.

If you plan to view or edit Z specifications in Unicode markup, you should 
also install the jEdit "Whitespace" plugin and enable the
"Show other whitespaces" option (use the "Plugins / WhiteSpaces" menu),
to ensure that you can see the ENDZED character.

Now copy all the jar files provided in this directory, EXCEPT bsh.jar, 
to the /jars subdirectory of either:
(a) the directory in which jEdit is installed, or
(b) your user settings directory (which you can find
    by evaluating the BeanShell expression
    jEdit.getSettingsDirectory()).


After you restart jEdit, you should now find an entry "Community Z Tools"
in the plugin menu, which pops up the CZT plugin.  It will show some
"missing font" square boxes until you install the CZT font (below).
We like to "dock" this plugin at the top or bottom of the main jEdit 
window -- see the jEdit documentation how plugins can be docked etc.

Documentation for the CZT plugin can be viewed via the "Help / jEdit Help"
menu, then scroll down to the "Plugins / Community Z Tools" entry.

You can test the installation so far by opening the sample bbook.zed
specification and typechecking it (click the "Typecheck" button in the
CZT plugin).  After a few seconds, it should say 
"Z typechecking complete, 0 errors" at the bottom of the CZT plugin.
You might like to try inserting some syntax errors, to see how they are
reported using the ErrorList plugin (Note: you must open the ErrorList
plugin to see the errors, then you can click on an error to go the
the cause of the problem in the Z specification).


2.2 Installing the CZT font
----------------------------

We are not experts in installing fonts, so please check the
documentation of your operating system how fonts are installed.  The
following summarises our experiences with installing the font on
Windows XP and Linux.

2.2.1(Windows): Installing the CZT font on Windows XP

Go into Start/Control Panel, then into the "Fonts" program.  (If you
are using the new XP categories, you need to select "Appearance and
Themes" first, then the "Fonts" link will appear in the left-hand
sidebar).  Once you are in the "Fonts" program, use the "File/Install
new font" menu entry, then browse to the CZTSans.ttf file and add it.

2.2.1(Linux): Installing the CZT font on Linux

Executing the following commands worked for me on gentoo
(without having root privileges):
  cd fonts/ttf
  ttmkfdir > fonts.scale
  mkfontdir
  xset fp+ `pwd`
  xset fp rehash

More information can be obtained from:
http://www.gnome.org/fonts
http://www.linux.org/docs/ldp/howto/Font-HOWTO/
http://linux.org.mt/article/ttfonts

2.2.2: Selecting the CZT font within jEdit

After installing the font, we must tell jEdit to use that font in all its
buffers.  To do this, go into the jEdit global settings panel
(you can use the "Utilities / Global Options" menu to open this panel),
then into the "Text Area" pane and set the "Text Font" to be CZT
(clicking on the existing font name will open a requestor, then you
can scroll down the left-hand column to select the "CZT" family).
You might also like to enable the "Smooth Text" and "Fractional Font
Metrics" on this "Text Area" pane, to turn on anti-aliasing of fonts.

You need to restart jEdit to see the font in the CZT plugin as well,
since the font in the CZT plugin cannot yet be set dynamically.  
After you have done this, you should see all the Z characters in the CZT
plugin (no little square boxes, which mean a missing symbol in the font).  

2.2.3: Test it -- create a Z Unicode specification!

In jEdit, use the "File / New" menu entry to create a new file.
Then select "Unicode Markup" in the CZT plugin.
Then click the "Sect",  "::=" and "Sch" buttons in the CZT plugin.
These should insert a section header, then a free type definition,
then a schema definition.  The resulting buffer should look like the
example screenshot.png in this directory.  If you are missing some
of the Z symbols, then recheck the CZT font installation.
If you cannot see the ENDZED characters (the little red diamonds),
then make sure you have installed the "WhiteSpace" plugin and
turned on the "Show other whitespace" option.


3. Run CZT without jEdit
************************

You can also run the CZT tools directly without using jEdit.
Just call
  java -jar czt.jar
and a beanshell console pops up.

Beanshell (http://www.beanshell.org/)
is a fully Java compatible scripting language.
It understands standard Java statements,
expressions, and method declarations.  That is,
if you can write Java programs, you can use
Beanshell as well :-)

To get access to the czt commands, type
  importCommands("czt");
Now execute the "Capture System in/out/err"
command of the Beanshell "File" menu.  This will
ensure that you see any errors produced by CZT.
 
Now you are free to explore the czt commands.

For example,
  spec = parse();
opens a file chooser and parses the file provided.
The resulting AST is assigned to the variable spec.

For another example,
  spec = typecheck();
parses and then typechecks the file that you choose.

See czt_commands.html for a list of available
commands.


4. Questions, Feedback, Bug Reports
***********************************

Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

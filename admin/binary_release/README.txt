             CZT          Community Z Tools
             ==============================
1. Requirements
***************

- Java 2 SDK >= 1.5
  http://java.sun.com/j2se/

- jEdit >= 4.1
  http://jedit.org/
  if you want to use the jEdit plugin

2. Run CZT using the jEdit plugin
*********************************

CZT ships a jEdit plugin providing parsing, typechecking, and editing
facilities for Z specifications in LaTeX or Unicode and a Z Unicode
font.

2.1 Installing the plugin
-------------------------

First make sure jEdit is really using Java 1.5.

Then copy all the jar files provided except bsh.jar to the /jars
subdirectory of either
(a) the directory in which jEdit is installed, or
(b) your user settings directory (which you can find
    by evaluating the BeanShell expression
    jEdit.getSettingsDirectory()).

Since the plugin is installed manually (not using the plugin manager),
we also need to take care of the plugin's dependencies.  The ErrorList
plugin is required by the CZT plugin, so please install the ErrorList
plugin from within jEdit's plugin manager.

Now we should find an entry "Community Z Tools" in the plugin menu,
which pops up the CZT plugin.  See the jEdit documentation how plugins
can be docked etc, and have a look at the plugin documentation
available from the jEdit help menu.

2.2 Installing the CZT font
----------------------------

We are not experts in installing fonts, so please check the
documentation of your operating system how fonts are installed.  The
following summarises our experiences with installing the font on
Windows XP and Linux.

Once installed, the CZT font can be selected in the "Global Options"
and then "Text Area" settings.  You need to restart jEdit to get the
font in the CZT plugin as well since the font in the CZT plugin cannot
yet be set dynamically.

2.2.1. Installing the CZT font on Windows XP

Go into Start/Control Panel, then into the "Fonts" program.  (If you
are using the new XP categories, you need to select "Appearance and
Themes" first, then the "Fonts" link will appear in the left-hand
sidebar).  Once you are in the "Fonts" program, use the "File/Install
new font" menu entry, then browse to the CZTSans.ttf file and add it.

2.2.1. Installing the CZT font on Linux

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

3. Run CZT without jEdit
************************

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

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

Make sure jEdit is using Java 1.5,
so install Java 1.5 first and then jEdit.

2.1 Installing the CZT font
----------------------------

We are not experts in installing fonts,
so please check the documentation of your
operating system how fonts are installed.

Once installed, the CZT font can be selected in the
"Global Options" and then "Text Area" settings.

2.1.1. Installing the CZT font on Windows XP

Go into Start /  Control Panel, then into the "Fonts" program.
(If you are using the new XP categories, you need to select
"Appearance and Themes" first, then the "Fonts" link will appear
in the left-hand sidebar).
Once you are in the "Fonts" program, use the "File / Install new font"
menu entry, then browse to the CZTSans.ttf file and add it.

2.1.1. Installing the CZT font on linux

The following worked for me on gentoo
(without having root privileges):
1) Change into the font directory fonts/ttf containing CZTSans.ttf
2) call 'ttmkfdir > fonts.scale'
3) call 'mkfontdir'
4) call 'xset fp+ /home/petra/fonts/ttf'
5) call 'xset fp rehash'

More help can be obtained from:
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

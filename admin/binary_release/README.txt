             CZT          Community Z Tools
             ==============================
Requirements
************
- Java 2 SDK >= 1.5
  http://java.sun.com/j2se/

Run CZT
*******
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

Questions, Feedback, Bug Reports
********************************
Please visit our web-site at
http://sourceforge.net/projects/czt/
There you can file bugs, ask for help, provide patches, ...

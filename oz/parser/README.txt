---------------
Object-Z parser
---------------

This is just a quick note to tell people how to build and run the
parser. I'll write a better readme at a further date.

To compile, just type 'ant', unless you are using a version of
JavaCup < 1.0k. In that case, run './cup.sh' followed by 'ant code'.
Make sure that ant is in your search path, JFlex.jar 
has been copied to <ANT_HOME>/lib/ directory
(as described in <JFLEX_HOME>/doc/jflex_anttask.html)
and the properties in <CZT_HOME>/czt.properties are set
to the correct paths for your system. You also need to build
the subprojects corejava and parser.

To run a specification, type './run.sh file'. This will parse the
toolkits (number, sequence, object-z toolkits etc.) and then parse the
file supplied on the line. It only accepts one file at the primitive
stage. This will produce a basic GUI (thanks to Petra for the code for 
that!) with your specification as a
JTree. If you just type './run.sh' (or 'ant run') this will start the
GUI with just the toolkits in the tree.

Currently, there are two scanners available. You can switch between
the two scanners by editing src/net/sourceforge/czt/parser/oz/Main.java.

Happy parsing!

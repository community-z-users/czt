---------------
Object-Z parser
---------------

This is just a quick note to tell people how to build and run the
parser. I'll write a better readme at a further date.

To compile, just type 'ant', unless you are using a version of JavaCup < 
1.0k. In that case, run './cup.sh' followed by 'ant code'.

To run a specification, type './run.sh file'. This will parse the
toolkits (number, sequence, object-z toolkits etc.) and then parse the
file supplied on the line. It only accepts one file at the primitive
stage. This will produce a basic GUI (thanks to Petra for the code for 
that!) with your specification as a
JTree. If you just type './run.sh' (or 'ant run') this will start the
GUI with just the toolkits in the tree.

Happy parsing!

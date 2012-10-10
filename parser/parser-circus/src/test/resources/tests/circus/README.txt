Circus Parser testing suite (v.1.2, April 2007)
-----------------------------------------------

This directory contains a set of examples used 
to test the Circus parser. One can use it to 
learn the proper LaTeX typesetting for Circus.
Further examples can be found at the CZT Z tests
directory for the Z parser.

The test suite run both error and normal tests.
All *.tex files are syntactically correct, whereas
the *-errors.txt have syntactic errors.

If you are interested in extending the suite or
make improvements, you can download it from the
repository and use the DEBUG_TESTING flag (default
is FALSE) at net.sourceforge.czt.parser.circus.AbstractParserTest.
This flag makes the testing suite to look for files 
under the ".\debug" directory, rather than here.

To switch this flag on/off, just add the file 
"debug-please" (no extension) to this directory.

Please send bugs, suggestions, or requests to:

Leo Freitas, leo@cs.york.ac.uk
Department of Computer Science, 
University of York, YO10 5DD

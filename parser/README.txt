Here is a very alpha draft version of the Z parser.
It reads LaTeX Z specifications and produces XML files.
The grammar does not exactly follow the Z standard yet,
and it does not handle operator templates.

Author: CHEN Chunqing, National University of Singapore,
  with some modifiations by Mark Utting, The University of Waikato.

To compile it:

   cup.sh     (or run JLex then JavaCUP manually)
   ant

To run it on the example 'upload/upload.tex' file:

   ant run


To run it on your own file, make sure that the 'build' subdirectory
is in your CLASSPATH, then:

   java net.sourceforge.czt.parser.z.LTFZnogui  myfile.tex

(this should create 'myfile.xml').


Please report problems and bugs to chenchun@comp.nus.edu.sg
and marku@cs.waikato.ac.nz



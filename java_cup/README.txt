                             -------
                             CUP-TUM 
                             -------

  This CZT subproject contains only the generated source code that is
  part of the {{{http://www2.cs.tum.edu/projects/cup/} CUP-TUM
  package}}. The CUP grammar and lexer are not included in this
  release, so that CZT developers need not have to worry about
  problems faced when using CUP to build itself.

  The build script takes the source code, and changes the package name
  from java_cup to net.sourceforge.czt.java_cup to avoid clashes with
  JEdit plugins that use older versions of CUP.

  There is also a change to the emit class, which breaks up each case
  in the switch statement (each case in the parse table) into its own
  method, so the do_action method does not grow too large, thus
  removing the "code too large" problem that javac raises when
  compiling the TCOZ parser.

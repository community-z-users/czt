             ------------------------------
             CZT          Community Z Tools
             ------------------------------

About

  The {{{http://czt.sourceforge.net} Community Z Tools (CZT)}} project
  is an open-source Java framework for building formal methods tools
  for Z and Z dialects. It includes a set of tools for parsing,
  typechecking, transforming, animating and printing ISO Standard Z
  conforming specifications in LaTeX, Unicode and XML formats.

  The latest version includes parser, typechecker, and printer for Z,
  Object Z, and Circus, an animator for Z (supports only a restricted
  subset of Z) as well as jEdit and eclipse plugins that give WYSIWYG
  editing of Z specifications and easy access to the CZT tools.

  Releases can be
  {{{http://sourceforge.net/project/showfiles.php?group_id=86250}
  downloaded from Sourceforge}}.  There are three bundles on the
  sourceforge web-site. The bundle <corejava> is deprecated and
  contains only old releases of corejava. The bundle <czt> is a
  collection of all the tools that we consider mature enough to be
  distributed, and also contains <corejava>.  The bundle <typechecker>
  contains a stand-alone typechecker for Z and Object Z specifications.

Source Releases

  If you are dealing with a source release, see INSTALL.txt on how to
  compile CZT.

* Sources from Subversion

  If you are really feeling adventurous, you can try to build CZT
  using the sources from Subversion. See
  {{{http://sourceforge.net/svn/?group_id=86250} the documentation about
  Subversion on sourceforge}} for more information about how to access
  the CZT repository.

Using CZT

  If you are dealing with the CZT sources, see chapter Source Releases
  and follow the installation instructions.  This will create the jar files
  mentioned below.

  There are at least three ways of using the CZT tools.

* Running CZT as a command line tool

  The jar file <<<CZT_HOME/bin/czt.jar>>> can be executed and used as
  a command line tool by calling 

+-----------------------+
    java -jar czt.jar
+-----------------------+

  followed by arguments. Calling it without arguments prints its usage
  information. The command line tool can be used in two different ways.

  Firstly, it can be called with the file name as argument, preceded
  by optional flags. This file is then parsed and typechecked and
  errors, if present, are reported. By specifying an output file using
  the -o flag, a specification can be translated into a different
  mark-up. The mark-up of a file (input or output) is determined by its
  file ending. For example, to translate a file in LaTeX mark-up into
  Unicode, call

+-------------------------------------------------+
    java -jar czt.jar -o file.utf8 file.tex
+-------------------------------------------------+

  See the usage information to get a list of supported mark-ups and
  file endings. There are other various flags that control the parsing
  behaviour; see the usage message to get more information about those.

  Secondly, the command line tool can be used to call other CZT tools
  like, for example, the Z animator zlive. This is done by giving the
  name of the CZT tool as first argument followed by the arguments for
  the selected tool. For example, the animator is started using

+----------------------------+
java -jar czt.jar zlive
+----------------------------+

  See the usage information for a list of availabe tools.





* Running CZT from within jEdit.

  The CZT plugins for the {{{http://www.jedit.org/}jEdit editor}}
  gives WYSIWYG editing of the Unicode markup for Z, template-based
  insertion of Z constructs for LaTeX and Unicode markup, automatic
  typechecking on each save, a SideKick panel that shows the structure
  of your Z specification and much much more.

  See {{{jedit/index.html} subproject jedit}} for more information'
  about how to install and use the jEdit plugins.




* The CZT font

  There is a CZT font in the <<<CZT_HOME/fonts>>> directory that
  supports the Z Starndard characters.  See fonts/INSTALL.txt
  on how to install and use the font.


Questions, Feedback, Bug Reports

  Please visit our
  {{{http://sourceforge.net/projects/czt/} web-site at sourceforge}},
  where you can file bugs, ask for help, provide patches, etc.

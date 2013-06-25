# Community Z Tools

The [Community Z Tools (CZT)][czt] project is an open-source Java framework for building formal methods tools for Z and Z dialects. It includes a set of tools for parsing, typechecking, transforming, animating and printing ISO Standard Z conforming specifications in LaTeX, Unicode and XML formats.

The latest version includes parser, typechecker, and printer for Z, Object Z, and Circus, an animator for Z (supports only a restricted subset of Z) as well as jEdit and Eclipse plugins that give WYSIWYG editing of Z specifications and easy access to the CZT tools.

[czt]: http://czt.sourceforge.net

## Downloads

Releases and nightly builds can be [downloaded from Sourceforge][download]. There are different download bundles available:

-   [`czt-ide`](http://sourceforge.net/projects/czt/files/czt-ide/) - Releases of standalone CZT IDE, based on Eclipse platform. Use it to author, develop and verify Z specifications.

-   [`czt-ide-updates`](http://sourceforge.net/projects/czt/files/czt-ide-updates/) - Update sites for released CZT Eclipse plugins to be installed in your own Eclipse IDE.

-   [`czt-jedit`](http://sourceforge.net/projects/czt/files/czt-jedit/) - Plugins for the jEdit text editor adding support for typesetting Z specifications.

-   [`czt`](http://sourceforge.net/projects/czt/files/czt/) - Standalone CZT library (classic distribution).

-   [`maven`](http://sourceforge.net/projects/czt/files/maven/) - Instructions how to use CZT libraries deployed to Maven Central.


-   [`corejava (old)`](http://sourceforge.net/projects/czt/files/corejava%20%28old%29/) - Old releases of _corejava_ (deprecated).

-   [`typechecker`](http://sourceforge.net/projects/czt/files/typechecker/) - Old releases of standalone typechecker for Z and Object Z specifications (deprecated).

[czt]: http://czt.sourceforge.net
[download]: http://sourceforge.net/projects/czt/files


## Source code

Refer to the [Developer documentation][dev] for information on working with the CZT Git repository and building CZT from source.

[dev]: dev/


## Using CZT

Depending on the CZT bundle you have downloaded, there are different ways of using them. If you are working with CZT sources, refer to [Developer documentation][dev] on how to build these bundles and JAR files mentioned below.


There are several ways of using the CZT tools. Independently of the way, you need the Java Runtime Environment (JRE) 6 (1.6) or any later version, which can be downloaded from [here](http://www.java.com/getjava).


### Running CZT as a command line tool

The CZT jar file `czt.jar` can be executed and used as a command line tool by calling 

    java -jar czt.jar

followed by arguments. Calling it without arguments prints its usage information. The command line tool can be used in two different ways.

Firstly, it can be called with the file name as argument, preceded by optional flags. This file is then parsed and typechecked and errors, if present, are reported. By specifying an output file using the `-o` flag, a specification can be translated into a different mark-up. The mark-up of a file (input or output) is determined by its file ending. For example, to translate a file in LaTeX mark-up into Unicode, call

    java -jar czt.jar -o file.utf8 file.tex

See the usage information to get a list of supported mark-ups and file endings. There are other various flags that control the parsing behaviour; see the usage message to get more information about those.

Secondly, the command line tool can be used to call other CZT tools like, for example, the Z animator zlive. This is done by giving the name of the CZT tool as first argument followed by the arguments for the selected tool. For example, the animator is started using

    java -jar czt.jar zlive

See the usage information for a list of available tools.


### Using CZT Eclipse IDE

CZT provides an Eclipse-based **Community Z Tools IDE** to develop Z specifications. It is a modern IDE for editing and checking Z specifications, verification condition generation, Z/EVES theorem prover integration and much more!

Check out all features and learn more at [CZT Eclipse](eclipse/) subproject.


### Running CZT from within jEdit

The CZT plugins for the [jEdit editor](http://www.jedit.org) give WYSIWYG editing of the Unicode markup for Z, template-based insertion of Z constructs for LaTeX and Unicode markup, automatic typechecking on each save, a SideKick panel that shows the structure of your Z specification and much much more.

See the [CZT jEdit subproject](jedit/) for more information on installing and using the CZT jEdit plugins.

## CZT LaTeX

A [CZT LaTeX][latex] style is available that supports the LaTeX characters for Z and its extensions. 
See the [latex page][latex] for information on downloading and using the font.

[latex]: latex/


## CZT font

A [CZT font][font] is available that supports the Z Standard characters and its extensions. 
See the [font page][font] for information on downloading and using the font.

[font]: fonts/


## Questions, feedback, bug reports

Please visit our [project site at SourceForge][czt-sf]! There you can file bugs, ask for help and otherwise contribute to the project.

[czt-sf]: http://sourceforge.net/projects/czt/

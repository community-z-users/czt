# CZT user interface

This project provides the main command-line user interface to CZT tools as well as
a basic Swing-based GUI.

## Running command-line CZT

CZT was originally developed for command-line and required users to enter specific commands
into the command-line prompt for desired outcomes.

The CZT standalone release JAR file _czt.jar_ can be executed and used as a command-line tool
by calling

    java -jar czt.jar <args>

with specific arguments. Calling it without arguments invokes the CZT graphical user interface
(see below). The command-line tool can be used in two different ways:

-   Firstly, it can be called with the file name as argument, preceded by optional flags.
    This file is then parsed and typechecked. The errors, if present, are reported. By specifying
    an output file using the `-o` flag, a specification can be translated into a different markup.
    The markup of a file (input or output) is determined by its file ending. For example, to
    translate a file in LaTeX markup into Unicode, call

        java -jar czt.jar -o file.utf8 file.tex

    See the usage information to get a list of supported markups and file endings. There are other
    various flags that control the parsing behaviour; see the usage message to get more
    information about those.
-   Secondly, the command line tool can be used to call other CZT tools like, for example, the
    Z animator [ZLive][zlive]. This is done by giving the name of the CZT tool as first argument
    followed by the arguments for the selected tool. For example, the animator is started using

        java -jar czt.jar zlive

For more help, type "`-help`" without quotes as the argument when starting CZT.

[zlive]: ../zlive/


## CZT graphical user interface

CZT also provides a basic user interface to drive the main functions of CZT tools. It allows
parsing and typechecking specifications written in Z and its extensions, inspecting the document
structure as well as running [ZLive animator][zlive].

![CZT user interface](images/czt-ui.png)

Recent development effort has been towards providing a better support for developing
Z specifications and a richer user interface via CZT integrations with IDEs:

-   [CZT Eclipse](../eclipse/)
-   [CZT jEdit](../jedit/)

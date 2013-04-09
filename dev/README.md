# CZT developer documentation

This part of website is intended for developers interested in working with CZT sources
and contributing to the project.

Feel free to ask questions related to the CZT internals and discuss ideas for enhancements and
bug fixes on the [czt-devel][] mailing list.

[czt-devel]: mail-lists.html

Some documentation is available for setting up CZT development in command-line environment
or Eclipse IDE:

-   [**Setup**](setup.html)

    -   [Requirements](setup.html#Requirements)
    -   [Get source code](setup.html#Get_source_code)
    -   [Build CZT](setup.html#Build_CZT)
    -   [Advanced build](setup.html#Advanced_build)

-   [**Setup in Eclipse IDE**](eclipse/index.html)

    -   [Get source using EGit](eclipse/index.html#Clone_Git_repository)
    -   [Import projects into Eclipse](eclipse/index.html#Import_projects_into_Eclipse)
    -   [Set CZT target platform](eclipse/index.html#Set_CZT_target_platform)
    -   [Launch CZT IDE](eclipse/index.html#Launch_CZT_IDE)
    -   [CZT code style](eclipse/index.html#CZT_code_style)
    -   [Maven `eclipse:eclipse` (alternative)](eclipse/index.html##Using_Maven_eclipseeclipse)

-   [**Guidelines**](guidelines.html)

    -   [General](guidelines.html#General_remarks)
    -   [Committing](guidelines.html#Committing_to_Git_repository)
    -   [Project layout](guidelines.html#CZT_project_layout)
    -   [Code style](guidelines.html#Java_style_guidelines)

This part of website also hosts custom tools used to build CZT itself (see sidebar and modules).


---

### CZT developer tools

CZT project also releases the custom tools used for building CZT itself. The tools are quite
generic and could be used for other projects in addition to Community Z Tools.

#### GnAST

Source code generator for creating Java ASTs from XML Schema definitions.

-   [**GnAST**][gnast] - the standalone library.
-   [**GnAST Maven plugin**][gnast-mvn] - Maven plugin.

[gnast]: gnast/
[gnast-mvn]: gnast-maven-plugin/


#### ParserGen

Generates source files for different CZT parser generators by slicing the corresponding XML
definition files. Allows common definition of different Z dialects.

-   [**ParserGen Maven plugin**][parsergen] - Maven plugin for ParserGen tool.

[parsergen]: parsergen-maven-plugin/


#### Java CUP

CZT parsers are generated using [CUP parser generator for Java][cup-tum].

CZT project provides a fork of the abandoned original project with several updates to support
large parser grammars and others.

-   [**Java CUP**][cup] - the standalone library and parser generator.
-   [**Java CUP Runtime**][cup-runtime] - runtime library needed to use CUP-generated parsers.
-   [**CUP Maven plugin**][cup-mvn] - Maven plugin.

[cup-tum]: http://www2.cs.tum.edu/projects/cup/
[cup]: java-cup/
[cup-runtime]: java-cup-runtime/
[cup-mvn]: cup-maven-plugin/

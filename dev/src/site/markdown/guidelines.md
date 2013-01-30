# Developer guidelines

This document is targeted at developers wanting to contribute to the Community Z Tools project.

## General remarks

Make yourself familiar with the project by following the announcements and discussions on
[czt-devel mailing list][czt-devel].

When you want to contribute code, it is best to start from the sources in CZT Git repository.
See the [setup instructions][setup] how to setup CZT development on your computer.
If you are not yet a member of the CZT project, you may contribute patches via the
[CZT page on SourceForge][czt-sf]. If you are already a member, you should have write access
to (parts of) Git repository.

[czt-devel]: http://lists.sourceforge.net/lists/listinfo/czt-devel
[setup]: setup.html
[czt-sf]: http://sourceforge.net/projects/czt


## Committing to Git repository

-   Make yourself familiar with Git, for instance by reading the [Git book][git-book].

-   Before committing, make sure that your changes do not break compilation and unit tests to
    avoid disrupting the work of other developers. Build all CZT repository using `buildall`
    script to make sure nothing breaks.

-   Commit and push often to help other developers keep their code in sync with your code.

[git-book]: http://git-scm.com/book


## CZT project layout

The CZT project consists of several sub-projects, each living in its own subdirectory.
The file and directory structure within each project directory should follow the
[standard Maven directory layout][mvn-dir].

[mvn-dir]: http://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html


## Java style guidelines

In order to make it easier for other developers to read your Java source code, please follow the
[Java Programming Style Guidelines from Geotechnical Software Services][java-style].

Automatic checking of these guidelines is supported via [Checkstyle][checkstyle] tool.
Refer to [CZT Checkstyle][czt-checkstyle] settings for more information.

[java-style]: http://geosoft.no/development/javastyle.html
[checkstyle]: http://checkstyle.sourceforge.net/
[czt-checkstyle]: checkstyle/

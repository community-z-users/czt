# Setup CZT development

CZT is open source and built using Java and Maven. This document provides
instructions to download and build CZT from source code using command-line
Maven.

If you are using [Eclipse IDE][eclipse] for your development, additional
instructions are available on [setting up CZT development in Eclipse][setup-eclipse].

[eclipse]: http://www.eclipse.org
[setup-eclipse]: eclipse/index.html


## Requirements

You need at least the following to build CZT:

*    [Git][git] client to get the source files
     ([various GUI clients are available][git-gui])
     
*    [Java Development Kit][jdk] version 8 or newer

*    [Maven][mvn] version 3.3.3 or newer

[jdk]: http://www.oracle.com/technetwork/java/javase/downloads
[mvn]: http://maven.apache.org/
[git]: http://git-scm.com
[git-gui]: http://git-scm.com/downloads/guis

Make sure you have these available on your system before you can build CZT.
The following sections outline basic steps to get and build CZT.


## Get source code

CZT source code is available on SourceForge. To download the source code,
you need to clone CZT Git repository. To clone the whole repository to
directory `czt`, use the following Git command:

    git clone git://git.code.sf.net/p/czt/code

This will clone the read-only CZT repository. Refer to
[CZT developer page][czt-dev] for further details.

Developers should familiarize themselves with Git by reading the
[Git Documentation][git-doc] or traversing through a
[Git tutorial][git-tutorial].

[czt-dev]: http://sourceforge.net/projects/czt/develop/
[git-doc]: http://git-scm.com/doc/
[git-tutorial]: http://gitimmersion.com/


### Line breaks (Windows only)

On Windows, CZT expects Windows-style line breaks (CR+LF). The conversion is
usually set by default (e.g. using `msysgit`) and nothing else is necessary.

If, however, you encounter build problems with some CZT modules, try forcing
the Windows line breaks using the following Git command in your repository:

    git config core.autocrlf true

Then reset your Git repository to checkout correct line breaks:

    git rm --cached -r .
    git reset --hard


## Build CZT

After getting the source code, build it using Maven. It will download all
necessary dependencies automatically.

For convenience, we provide build scripts that perform the main build commands:

-    `buildall.sh` for Linux and Mac OS X
-    `buildall.bat` for Windows

Upon execution the script will launch Maven builds, which will compile and test
all CZT projects. This includes core libraries, as well as Eclipse plugins.

If the build fails, we would advice to try running it again. Sometimes the
issue is a timeout or similar and re-running solves it. Otherwise read on for
advanced instructions and troubleshooting.


## Advanced build

Building CZT manually is a quite straightforward 2-step process using standard
Maven commands:

1.   First, the CZT core libraries are built in root directory.
2.   Second, CZT Eclipse plugins are built in `/eclipse` subdirectory.
     This needs to be a separate step otherwise CZT core bundles are not
     resolved correctly.

To accommodate the CZT build, Maven Java heap size needs to be increased to at
least 512Mb. This is done by setting the `MAVEN_OPTS` environment variable to
at least `-Xmx512m`. Recommended settings are `-Xmx1024m -XX:MaxPermSize=256m`.

Then change to root CZT directory (`CZT_HOME`) and build from the command-line
using Maven command:

    mvn clean install

This should compile, test, package, and install all the CZT tools into your
local Maven repository, ready to be used in your own projects.

To build CZT Eclipse plugins, switch to `eclipse` subdirectory and run
Maven there:

    cd eclipse
    mvn clean install

Running the CZT tests takes quite a long time.  If you want to skip running
the unit tests use the following command instead:

    mvn clean install -Dmaven.test.skip=true

If build gets stuck in the middle and you want to resume, or if you want to
perform a partial build, the following command builds from the `<project-name>`
onwards:
    
    mvn clean install -rf :<project-name>
    
See the [user manual][czt-usage] on how to use CZT.

[czt-usage]: ../manual.html


### Setting Maven environment variables

To set Maven environment variables in Windows command prompt (`cmd.exe`),
use the following commands:

    set MAVEN_OPTS=-Xmx1024m -XX:MaxPermSize=512m
    set PATH=%PATH%;c:\maven\bin

Adjust the paths to match your Java & Maven installation directories.
These commands will set the environment variables temporarily. You can also set
them permanently in the System settings of the Control Panel.

For Unix based systems, set environment variables using `export` command, e.g.:

    export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"
    

### CZT Eclipse and CZT core as OSGI bundles

We use [Eclipse Tycho][tycho] to build CZT Eclipse plugins using Maven.

Eclipse uses OSGI framework to provide modular plugins. To adhere to these
practices, we provide OSGI bundles for CZT core projects. This way CZT can
be used in OSGI applications in a modular manner.

The CZT core is still developed as Maven project, using 'POM-first' approach.
Then the modules are OSGI-fied using [`maven-bundle-plugin`][maven-bundle]
for consumption, e.g. as Eclipse plugins based on the information in their
POM files.

Note that currently we preserve the modular structure of CZT in OSGI and have
a separate bundle (JAR) for each project, instead of packaging everything into
one JAR, e.g. as in `czt.jar`. This is a provision for modular packaging in the
future (e.g. if we want a _Circus_ only deployment). This requires to adapt
the code that expect everything to be in one bundle.

The process of OSGI-fying CZT modules requires a 2-step build of CZT. First,
the core modules are produced as OSGI bundles. Then we launch `eclipse` build
so that its dependency resolved can find these core bundles. If done in one
reactor build, the dependency resolution for Eclipse plugins starts too
early and cannot find the core bundles. See [instructions for building such
projects][tycho-pom-first] for more details.

When CZT is developed using Eclipse (see [instructions][setup-eclipse]),
these issues are alleviated by using [Eclipse m2e][m2e] and its integration
with Eclipse PDE and Tycho.

[tycho]: http://www.eclipse.org/tycho
[maven-bundle]: http://felix.apache.org/site/apache-felix-maven-bundle-plugin-bnd.html
[tycho-pom-first]: http://wiki.eclipse.org/Tycho/How_Tos/Dependency_on_pom-first_artifacts
[m2e]: http://www.eclipse.org/m2e/


## Troubleshooting

### Troubleshooting: error downloading dependencies

Occasionally, Maven reports an error while downloading one of the various
dependencies. This is typically a timeout and rerunning the build and letting
Maven pick up where it left off is usually sufficient (you might need to do
this several times). You might also try to configure a more reliable mirror
closer to you; see the [Maven documentation][mvn-mirrors] on how to configure
a Maven mirror.

[mvn-mirrors]: http://maven.apache.org/guides/mini/guide-mirror-settings.html


### Troubleshooting: tests failing due to line breaks (Windows only)

Tests can fail because of Unix-style line breaks used in Windows builds.
Ensure correct line breaks when checking out from Git
(see [above](#Line_breaks_Windows_only)).

# Compiling and installing CZT

CZT is open source and built using Java and Maven. This document provides
instructions to download and build CZT from source code.

You need at least the following to build CZT:

*    [Git][git] client to get the source files
     ([various GUI clients are available][git-gui])
     
*    [Java Development Kit][jdk] version 6 or newer

*    [Maven][mvn] version 2.0.4 or newer

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

    git clone git://czt.git.sourceforge.net/gitroot/czt/czt

This will clone the read-only CZT repository. Refer to
[CZT developer page][czt-dev] for further details.

[czt-dev]: http://sourceforge.net/projects/czt/develop


## Build CZT

After getting the source code, build it using Maven. It will download all
necessary dependencies automatically.

To accommodate the CZT build, Maven Java heap size needs to be increased to at
least 512Mb. This is done by setting the `MAVEN_OPTS` environment variable to
at least `-Xmx256m`. Recommended settings are `-Xmx1024m -XX:MaxPermSize=256m`.

Then change to root CZT directory (`CZT_HOME`) and build from the command-line
using Maven command:

    mvn clean install

This should compile, test, package, and install all the CZT tools into your
local Maven repository, ready to be used in your own projects.

Running the CZT tests takes quite a long time.  If you want to skip running
the unit tests use the following command instead:

    mvn clean install -Dmaven.test.skip=true

If build gets stuck in the middle and you want to resume, or if you want to
perform a partial build, the following command builds from the `<project-name>`
onwards:
    
    mvn clean install -rf :<project-name>
    
See README file for information on how to use CZT.


### Setting Maven environment variables

To set Maven environment variables in Windows command prompt (`cmd.exe`),
use the following commands:

    set MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"
    set JAVA_HOME="C:\Program Files\Java\jdk1.7"
    set PATH=%PATH%;c:\maven\bin

Adjust the paths to match your Java & Maven installation directories.
These commands will set the environment variables temporarily. You can also set
them permanently in the System settings of the Control Panel.

For Unix based systems, set environment variables using `export` command, e.g.:

    export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"
    

### Troubleshooting: error downloading dependencies

Occasionally, Maven reports an error while downloading one of the various
dependencies. This is typically a timeout and rerunning the build and letting
Maven pick up where it left off is usually sufficient (you might need to do
this several times). You might also try to configure a more reliable mirror
closer to you; see the [Maven documentation][mvn-mirrors] on how to configure
a Maven mirror.

[mvn-mirrors]: http://maven.apache.org/guides/mini/guide-mirror-settings.html

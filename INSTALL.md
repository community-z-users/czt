# Compiling and installing CZT

CZT is open source and built using Java and Maven. This document provides
instructions to download and build CZT from source code.

You need at least the following to build CZT:

*    [Git][git] client to get the source files
     ([various GUI clients are available][git-gui])
     
*    [Java Development Kit][jdk] version 6 or newer

*    [Maven][mvn] version 3.0.4 or newer

[jdk]: http://www.oracle.com/technetwork/java/javase/downloads
[mvn]: http://maven.apache.org/
[git]: http://git-scm.com
[git-gui]: http://git-scm.com/downloads/guis

Make sure you have these available on your system before you can build CZT.
The following sections outline basic steps to get and build CZT.
Furthermore, specific instructions for use with Eclipse IDE are also available.


## Get source code

CZT source code is available on SourceForge. To download the source code,
you need to clone CZT Git repository. To clone the whole repository to
directory `czt`, use the following Git command:

    git clone git://czt.git.sourceforge.net/gitroot/czt/czt

This will clone the read-only CZT repository. Refer to
[CZT developer page][czt-dev] for further details.

[czt-dev]: http://sourceforge.net/projects/czt/develop

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

### Troubleshooting: tests failing due to line breaks (Windows only)

Tests can fail because of Unix-style line breaks used in Windows builds.
Ensure correct line breaks when checking out from Git (see above).


## Using Eclipse IDE

These instructions outline steps how to develop CZT source code using
[Eclipse IDE][eclipse]. Information is based on Eclipse Juno (4.2).

The instructions are for generating Eclipse projects using `mvn eclipse:eclipse`.
Alternatively, experimental support for [Eclipse m2e][m2e] is described
afterwards.

[eclipse]: http://www.eclipse.org


### Clone CZT source code Git repository

Eclipse provides a Git client - [EGit][egit] - as part of IDE. It can be used
to clone CZT Git repository. If you have already checked out CZT source code,
skip to the next step.

The general steps to clone a repository in Eclipse IDE are the following:

1.    Launch clone wizard by selecting Import > Projects from Git > URI
2.    In the repository information, supply the CZT repository URI:
      `git://czt.git.sourceforge.net/gitroot/czt/czt`
3.    Select branches to clone (e.g. at least `master` - the main branch)
4.    Provide destination directory
5.    Select _Import as general project_ to have the root directory visible as
      project in Eclipse
6.    Provide root project name, e.g. `czt`

This will create a new general project in Eclipse, which contains all CZT
repository contents. For more information on using EGit, refer
to [its user guide][egit-usage].

CZT is built with Maven, so to use the CZT submodules in Eclipse, they need
to be converted to separate Eclipse projects. The following steps explain
how to do that. 

[egit]: http://www.eclipse.org/egit/
[egit-usage]: http://wiki.eclipse.org/EGit/User_Guide


### Generate Eclipse projects

To convert CZT modules to Eclipse project, we will use
[Apache Maven Eclipse][mvn-eclipse] plugin. 

First of all, add Maven repository variable to workspace classpath. Eclipse
projects will need to reference libraries in the local Maven repository.
Add the `M2_REPO` classpath variable with the following Maven command:
	
	mvn -Declipse.workspace=<path-to-eclipse-workspace> eclipse:add-maven-repo

Now Maven Eclipse can generate Eclipse projects with all dependencies for
corresponding Maven modules. To achieve that, go to the root CZT directory
(where the root `pom.xml` file is) and execute Maven command:
	
	mvn eclipse:eclipse -DdownloadSources -DdownloadJavadocs

This will build CZT (can take a long time!) and generate Eclipse projects
(i.e. `.project` and `.classpath` files) for each Maven module. Furthermore,
it will attach sources and JavaDocs for referenced libraries.

[mvn-eclipse]: http://maven.apache.org/plugins/maven-eclipse-plugin


#### Troubleshooting: out of memory
	
If the build fails with error `java.lang.OutOfMemoryError : Java heap space`,
the available Maven heap space must be increased (see above).
	
Then rerun the initial command:
	
	mvn clean
	mvn eclipse:eclipse


#### Troubleshooting: 'filtering' is not identical

When building `ui` project, it can fail with the following error:
`Request to merge when 'filtering' is not identical`. It seems to be an issue
with Maven Eclipse plugin. A workaround is to use version 2.6 of the plugin.
So resume the build with this plugin version:

	mvn org.apache.maven.plugins:maven-eclipse-plugin:2.6:eclipse -DdownloadSources -DdownloadJavadocs -rf :ui


### Import Eclipse projects into workspace

If the Eclipse projects were generated successfully with the step before,
they can now be imported into workspace. Open Eclipse IDE and select
File > Import > Existing Projects into Workspace. Browse to the root CZT
directory and select to import all projects.
Do not check "copy projects to workspace".

This will import CZT modules as Eclipse projects and everything should build
successfully. If some dependency errors exists, try building and installing CZT:

	mvn clean install
	
Note that if source has been checked out using EGit into a root project,
the root directory will only show the top project (already imported `czt`) in
the Import wizard. In this case each project will have to be imported manually
in the same way - just select each project in the Import wizard.
[Fix for this issue is underway in Eclipse][import-nested-bug].

[import-nested-bug]: https://bugs.eclipse.org/bugs/show_bug.cgi?id=144610


### Rebuilding after changes

The Eclipse projects are resolved with dependencies between projects, so when
a file is changed, the affected projects are rebuilt. However, in some cases
(e.g. when source code needs to be regenerated or if final JARs are needed),
it is necessary to run Maven build again. In this case, run appropriate Maven
commands from the the command line, e.g. `mvn clean install`.

It is possible to simplify this a little and define Maven as an _external tool_
in Eclipse IDE. Then specific commands can be run based on the selection in
Eclipse, e.g. select a project and then run `clean install` on the selection.
For more information on configuring Maven as an _external tool_ in Eclipse
see the [plugin usage documentation][mvn-eclipse-usage].

[mvn-eclipse-usage]: http://maven.apache.org/plugins/maven-eclipse-plugin/usage.html


### Link projects to EGit

Each resolved project can now be linked to [EGit][egit] to display changes and
allow version control functionality on the source code. To link projects with
EGit follow these steps:

1.    Select all of CZT projects
2.    Select Team > Share Project... from the context menu
3.    In the sharing wizard, select `Git` as the repository type
4.    Make sure _Use or create repository in parent folder of project_ checkbox
      is selected. This relates the project to parent Git repository, as it is
      configured in CZT
5.    Select all projects to connect and click _Finish_.

Now EGit actions/decorations can be used on the projects.

If EGit was used to checkout the main CZT directory originally, user may want
to close the root `czt` project, as almost all of its contents are now
accessible via the subprojects. 


### Use CZT code style

CZT code style file is available for Eclipse IDE to provide common code
formatting. [Download it][czt-style] and import in Eclipse Preferences >
Java > Code Style > Formatter tab.

[czt-style]: doc/eclipse-code-format-style.xml


### m2e support

The [Maven integration with Eclipse (m2e)][m2e] project aims to provide
first-class Apache Maven support in Eclipse IDE. However, it also aims to
participate in Eclipse automatic builds, which causes problems with certain
Maven plugins. See [M2E wiki][m2e-cover] for more details on that.

We provide experimental support for m2e when building CZT source code.


#### m2e connectors for CZT build plugins

Basic m2e connectors are available to handle "lifecycle mapping" for CZT Maven
plugins (i.e. `gnast-maven-plugin`, `cup-maven-plugin` and `parser-src`).
They are not available in the official m2e marketplace and should be installed
from [CZT developer update site][czt-dev-p2]:

    http://czt.sourceforge.net/dev/eclipse/updates/latest

Install the connectors (_m2e support for building CZT_) before importing
CZT Maven projects. Also install other related plug-ins from the update site:

-    _m2e connector for `maven-jflex-plugin`_
-    _m2e Connector for XML Transform_ (`xml-maven-plugin`)

Several other Maven plugins have m2e connectors available in m2e marketplace.
Install them when asked during CZT project import. For other m2e 'incompatible'
plugins, we provide some default lifecycle mapping. However, it raises some
issues with the workspace not being refreshed properly.

[czt-dev-p2]: http://czt.sourceforge.net/dev/eclipse/updates/latest


#### Import CZT Maven projects into workspace

Importing CZT projects using m2e requires a bit of fiddling at the moment.
The following steps give rough outline of the process - try adding performing
additional rebuilds/refreshes/update project to get everything built.

For best results, build everything from command-line: `mvn clean install` and
only then import the projects. The following steps are for unbuilt projects
and may help with troubleshooting.

1.  Select File > Import > Existing Maven Projects
2.  Select root CZT directory and import all necessary projects
3.  If asked to get m2e connectors from the marketplace, allow that
    (restart Eclipse if needed)
4.  After import, wait until _Building workspace_ job finishes
    (can take long!)
5.  If there are build errors, select all projects and refresh them.
    This should trigger another build. It is because some plugins do not have
    correct m2e connectors available
6.  This should get core CZT projects built successfully. There may still be
    errors with CZT Eclipse plug-ins
7.  CZT Eclipse plug-ins are built upon `installed` CZT core JARs, so
    run `mvn clean install` on the root CZT directory.
    
    This can be done by selecting `czt` project and then Run As > Maven build...
    Enter `clean install` in _goals_ field. Furthermore, in _JRE_ tab increase
    the allowed memory: add `-Xmx1024m -XX:MaxPermSize=512m` to _VM arguments_
    
8.  After everything is built successfully, refresh `net.sourceforge.czt.library`
    project
9.  Select Maven > Update Project... in the context menu of
    `net.sourceforge.czt.library` project. This should build the CZT Eclipse
    plug-ins successfully in the IDE

Note that these steps are rough guidelines - we may try to streamline the
m2e support in the future.


#### Building CZT m2e connectors

The m2e connectors for CZT Maven plugins are also available as Eclipse plug-ins
in CZT repository: `<CZT_HOME>/eclipse/m2e`. When the full CZT build is
performed, e.g. via `mvn clean install`, the plug-ins are built and packaged
into CZT p2 repository. To install them from your local source code, add it
as Eclipse update site with the following address:
	
	file:<CZT_HOME>/eclipse/net.sourceforge.czt.eclipse.repository/target/repository/


[m2e]: http://www.eclipse.org/m2e/
[m2e-cover]: http://wiki.eclipse.org/M2E_plugin_execution_not_covered

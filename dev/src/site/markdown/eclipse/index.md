# Setup CZT in Eclipse

These instructions outline steps how to develop CZT source code using
[Eclipse IDE][eclipse]. Information is based on Eclipse Mars (4.5).

Refer to [general setup instructions][setup] for more details on CZT
development setup.

We recommend using [Eclipse m2e][m2e] for building CZT using Eclipse and Maven.
It is available as part of [Eclipse RCP/RAP or Classic][eclipse-download]
packages. Download one of these packages to use with CZT development.

[eclipse]: http://www.eclipse.org
[m2e]: http://www.eclipse.org/m2e/
[eclipse-download]: http://www.eclipse.org/downloads
[setup]: ../setup.html


## Clone Git repository

Eclipse provides a Git client - [EGit][egit] - as part of IDE. It can be used
to clone CZT Git repository. If you have already checked out CZT source code,
skip to the next step.

The general steps to clone a repository in Eclipse IDE are the following:

1.    Launch clone wizard by selecting **Import > Projects from Git > URI**
2.    In the repository information, supply the CZT repository URI:
      `git://git.code.sf.net/p/czt/code`
3.    Select branches to clone (e.g. at least `master` - the main branch)
4.    Provide destination directory
5.    Select **Import as general project** to have the root directory visible as
      project in Eclipse
6.    Provide root project name, e.g. `czt`

This will create a new general project in Eclipse, which contains all CZT
repository contents. For more information on using EGit, refer
to [its user guide][egit-usage].

[egit]: http://www.eclipse.org/egit/
[egit-usage]: http://wiki.eclipse.org/EGit/User_Guide

## Import projects into Eclipse

The [Maven integration with Eclipse (m2e)][m2e] project aims to provide
first-class Apache Maven support in Eclipse IDE. However, it also aims to
participate in Eclipse automatic builds, which causes problems with certain
Maven plugins. See [M2E wiki][m2e-cover] for more details on that.

If this is the first time you built CZT, you need to build it from the
command line before importing into Eclipse. This is necessary because
of CZT-specific Maven plugins, which are built on-the-fly. You can
import them into Eclipse after everything is built first.

Furthermore, you need to install m2e connectors for CZT build
before importing the projects (see below).

[m2e-cover]: http://wiki.eclipse.org/M2E_plugin_execution_not_covered


### m2e connectors for CZT build

Several Maven plugins used by CZT require installing m2e connectors from
3rd party update sites (namely `maven-jflex-plugin` and `xml-maven-plugin`).
They are not available in the official m2e marketplace and should be installed
from the [CZT developer Eclipse update site][czt-dev-p2]:

    http://czt.sourceforge.net/dev/eclipse/updates/

[Install the connectors][eclipse-update] before importing CZT Maven projects:

-    _m2e connector for `maven-jflex-plugin`_, version `>= 1.2.0`
-    _m2e Connector for XML Transform_ (`xml-maven-plugin`), version `>= 3.0.0`

Several other Maven plugins have m2e connectors available in m2e marketplace.
Install them when asked during CZT project import.

[czt-dev-p2]: http://czt.sourceforge.net/dev/eclipse/updates/
[eclipse-update]: http://www.vogella.com/articles/Eclipse/article.html#plugin_installation


### Import CZT Maven projects into workspace

After installing all prerequisites and building everything from command line
the first time, you can import the CZT projects into Eclipse IDE.
To do that, follow these steps:

0.    (If EGit was used to checkout the source code, delete the `czt` project).
1.    Select **File > Import > Existing Maven Projects**
2.    Select root CZT directory and import all necessary projects
3.    If asked to get m2e connectors from the marketplace, allow that
      (restart Eclipse if needed)
4.    After import, wait until _Building workspace_ job finishes
      (can take long!)
5.    Set CZT target platform ([see below](#Set_CZT_target_platform)).
5.    If there are build errors, select all projects and refresh them.
      This should trigger another build.
6.    Done - this should get CZT projects built successfully.
7.    Launch CZT IDE from within Eclipse ([see below](#Launch_CZT_IDE))


## Set CZT target platform

The target platform comprises all dependencies available for building CZT for Eclipse plug-ins. It
is defined in _net.sourceforge.czt.eclipse.target_ project. Open the target definition file at
**/net.sourceforge.czt.eclipse.target/net.sourceforge.czt.eclipse.target.target** within Eclipse.

![CZT target platform](images/czt-target-platform.png "CZT target platform")

When the target definition file is opened, wait for some time until its contents are resolved. Then
select **Set as Target Platform** in the top-right of the editor. These dependencies will be
loaded for use in builds and all CZT for Eclipse projects should build successfully now. Note that
this needs to be done once at the beginning and then only if the dependencies/target platform
change (close the target file afterwards to avoid unnecessary resolution).

If you still encounter build errors, try refreshing the projects (select all and choose
**File > Refresh**) or cleaning them (**Project > Clean**).


## Launch CZT IDE

For convenience, a launch configuration is provided to start CZT IDE from the checked-out projects.
It defines all features and plug-ins that are required for CZT.

Select the launch configuration at **/net.sourceforge.czt.eclipse.repository/czt-ide.launch**. Choose **Run As > czt-ide** in the context menu.

![CZT IDE launch file](images/czt-ide-launch-file.png)

This will launch CZT IDE as a separate application. All your changes will be reflected in
the launched program. The launch configuration will also now be available in the main **Run** and
**Debug** toolbars for convenient access. Use this launch configuration to run and debug CZT for
Eclipse IDE.


## Link projects to EGit

Each imported project can now be linked to [EGit][egit] to display changes and
allow version control functionality on the source code. To link projects with
EGit follow these steps:

1.    Select all of CZT projects
2.    Select **Team > Share Project...** from the context menu
3.    In the sharing wizard, select **Git** as the repository type
4.    Make sure **Use or create repository in parent folder of project** checkbox
      is selected. This relates the project to parent Git repository, as it is
      configured in CZT
5.    Select all projects to connect and click **Finish**.

Now EGit actions/decorations can be used on the projects.


## CZT code style

CZT code style file is available for Eclipse IDE to provide common code
formatting. [Download it][czt-style] and import in **Eclipse Preferences >
Java > Code Style > Formatter** tab.

Furthermore, you may want to use [Eclipse Checkstyle][eclipse-cs] plugin with
[CZT Checkstyle][czt-checkstyle] settings for additional code style checking.

[czt-style]: czt-code-style.xml
[eclipse-cs]: http://eclipse-cs.sourceforge.net/
[czt-checkstyle]: ../checkstyle/


## Using Maven `eclipse:eclipse`

_(This is an alternative way of using CZT in Eclipse and not needed if m2e is used.)_

An alternative way of working with CZT in Eclipse is to convert the Maven
plugins to separate Eclipse projects. For that we can use
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
**File > Import > Existing Projects into Workspace**. Browse to the root CZT
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

If EGit was used to checkout the main CZT directory originally, you may want
to close the root `czt` project, as its contents are now
accessible via the subprojects. 

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

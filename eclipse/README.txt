             -----------------------
             CZT Plugins for Eclipse
             -----------------------


Overview

  This directory contains two Eclipse plugins.

  The czteditor plugin provides a Z editor with continuous
  typechecking, cross-referencing, syntax highlighting, outlining and
  many other features.  It also has partial support for Object-Z.

  The czthelp plugin provides online help for the above CZT editor.
  (Once it is installed, then the "Help / Contents" menu will show
  a help manual called "CZT Developer User Manual").


Compilation and Testing
  
  To work on one of these plugins, you can import it into
  Eclipse (version 3.2 or higher) using the "File / Import /
  General / Existing Projects into Workspace" and use the Browse
  button to select the czteditor or the czthelp directory.

  To run one of the plugins to test it, just right-click on the
  project in Eclipse and use the usual "Run As / Eclipse Application"
  command.


Creating Releases

  To create a release of these plugins, which other users can download
  and install into Eclipse, use the "File / Export / Deployable Features
  and Plugins" command.  Then select the plugins that you want to export
  (usually both of them), choose a directory to export them to, and
  click "Finish".  In the "Options" tab, you can include the source code
  if you wish.  This will create a "plugins" directory that contains
  the .jar files for each of the plugins.  

  The plugins can be installed into another Eclipse installation
  simply by copying these .jar files into the existing "plugins"
  directory of that Eclipse installation.  It is also possible to
  create an Eclipse update site, so that updates can be done via
  the Eclipse update manager.  We have not done this yet, since the
  advantages seem small.







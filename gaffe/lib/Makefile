${TopDir}/Rules.make:; $(error make should be run from GAfFE's top level directory.)
include ${TopDir}/Rules.mk

thisdir.squeaky:
	rm -f *.jar
# Change Log:
# $Log$
# Revision 1.1  2003/06/13 06:54:35  ntd1
# 13 Jun 2003 - Groundwork for having multiple form design windows, + more.
# 	- Expanded ToolWindow.Tool and its subclasses to include functions for carrying out
# 	- Created ToolWindow.SelectBeanTool
# 	- Created Listener and Event classes for ToolChange, and for BeanSelected
# 		- used respectively by ToolWindow when a tool is selected, and by FormDesign when a
# 		  bean is selected.
# 	- Modified FormDesign to use 'Tool' provided by ToolWindow (is now a ToolChangeListener)
# 	  instead of the BeanInfo tool from its old toolbar.
# 	- Makefile -  'lib' directory is no longer removed by a 'squeaky' clean.
# 	- renamed FormDesign.contentPane to FormDesign.beanPane to avoid confusion with RootPane's
# 	  contentPane property.
# 	- Made FormDesign.StatusBar class, instead of using a JLabel for the status bar.
# 	- Added function FormDesign.addBean, used by ToolWindow.PlaceBeanTool.  Adds a new bean to the
# 	  form.
# 	- Discontinued use of MoveHandle (though not deleted yet).
# 	- Due to moving of responsibilities from FormDesign to DesignCore, it is (at present) not
# 	  possible to open the properties window.  This will be fixed in the next commit, when keeping
# 	  the reference to the properties window, will be managed by the DesignCore.
# 	- Tasks that need to be done soon:
# 		- Move the PropertiesWindow to the DesignCore
# 		- Fix all code that assumes a bean is a component. (Mostly in FormDesign.java).
# 		- Add the ability to put components inside the Form.
# 		- Stop non-component beans from going in the Form, stop component beans from going
# 		  outside the form.
# 		- Hack up a fix to make PropertyChangeEvents get sent to the listeners on a component
# 		  for changes to the 'name' property.  (Components, and possibly other bean types don't
# 		  trigger a PropertyChangeEvent when the name property changes; this is annoying when
# 		  we want status bars, etc. to update).
# 		- Determine if problems are caused by having only the one copy of  the window menu.  Is
# 		  it permissible to have one menu in two menu bars.  (i.e. the one JMenu object serving
# 		  two windows).
#
#  4 Jun 2003 - (not committed)
# 	- Moved DesignCore.java to the czt.animation.gui.design package.
# 	- Created ToolWindow.java in the czt.animation.gui.design package.
# 		- Created 'resources' directory for holding non .class files destined for the jar file.
# 	- Modified DesignCore.java to be more than just a shell.
# 		- Tried BeanContextServices for tracking ToolWindow, PropertiesWindow, ActionMap,
# 		  InputMap, window JMenu.  Changed to constructor parameters instead.  Becomes overly
# 		  complicated for this purpose.
# 		- Keeps track of 'FormDesign's
# 		- Keeps instance of ToolWindow
# 	- Eliminated need for temp directory - changed manifest file to be intermediate target.
# 	- Removed main function in FormDesign.java - used for testing.
#

${TopDir}/Rules.make:; $(error ${TopDir} make should be run from GAfFE's top level directory.)
include ${TopDir}/Rules.mk
thisdir.squeaky:;rm -rf ${APIDocPath}

#Don't want to recurse into the subdirectories here.
SubDirs=

# Change Log:
# $Log$
# Revision 1.2  2003/06/23 06:04:49  ntd1
# 23 Jun 2003 (2) -
# 	- Changed Rules.mk's doc rule to 'mkdir -p' instead of just 'mkdir' the api directory.
# 	- Blocked the 'doc' directory's makefile from recursing deeper.
# 	- Added icons for various windows.
# 	- Added new functions to ToolWindow.Tool - selected, unselected.  Called when tool is selected
# 	  and in its argument-taking form when a FormDesign learns that the tool is selected.
# 	- Removed cursor property from ToolWindow.Tool.  Tools can achieve the same effect by setting
# 	  the cursor on FormDesigns themselves.
# 	- Added oldTool property to ToolChangeEvent.
# 	- Made some protected members of ToolWindow private.
# 	- Added some API documentation.
#
# Revision 1.1  2003/05/27 05:55:19  ntd1
# 27 May 2003 - First commit to CVS:
# 	- Placing of beans in Form Design window works.
# 	- Display of properties, methods, and events working.
# 	- Editing of properties partially working. (Need to sort out stuff between the visual
# 	  component, the table it's in, and the property itself.)
# 	- Before Milestone 0, need:
# 		- to fix editing of properties completely.
# 		- ability to link beans via events.
# 		- ability to work on multiple forms.
# 		- ability to place component beans visually inside the form being designed.
# 	- Thoughts:
# 		- May be desirable to move toolbar into its own window, if there's going to be multiple
# 		  forms.
# 		- May want to add seperate tool for moving beans, rather than just click-dragging on
# 		  them.  Makes things easier when beans are allowed to be placed inside the form.
#
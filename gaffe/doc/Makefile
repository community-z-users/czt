${TopDir}/Rules.make:; $(error ${TopDir} make should be run from GAfFE's top level directory.)
include ${TopDir}/Rules.mk
thisdir.squeaky:;rm -rf ${APIDocPath}

#Don't want to recurse into the subdirectories here.
SubDirs=

# Change Log:
# $Log$
# Revision 1.1.2.1  2003/06/23 04:37:28  ntd1
# 23 June 2003 - False start on allowing components to be inserted into a FormDesign's Form.
# 	- Mostly running into problems with translating coordinate contexts.
# 	- Results in ResizeHandles being in wrong places, possible problems with mouse coordinates.
# 	- Also resizing from top/left should move contents of Form down/right.
# 	- FormDesign should provide functions for doing this translation.
# 	- Ideally coordinate translation should handle multiple levels of containers (for future use).
#
# NOTE:	- This Branch is a one off dead-end.
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
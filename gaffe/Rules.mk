# Rules.make
# 
# Change log at end of file.

all:jar

ifndef BSFHOME
    BSFHOME=${TopDir}
endif
ifndef RHINOHOME
    RHINOHOME=${TopDir}/lib
endif

PWD=$(shell pwd)
export SourcePath=${TopDir}/src
export ClassDestPath=${TopDir}/classes
export ResourcesPath=${TopDir}/resources
export JarPath=${TopDir}/lib
export ClassPath=${ClassDestPath}:${BSFHOME}/lib/bsf.jar:${RHINOHOME}/js.jar
export APIDocPath=${TopDir}/doc/api
export DistPath=${TopDir}/dist

SubDirs=$(foreach fd,$(shell echo */|sed s/\*\\///|sed s/CVS\\///|sed s/resources\\///),$(fd) )

JavaFiles=$(shell echo *.java|sed s/\*.java//)
ClassFiles=$(foreach fd,${JavaFiles},${ClassDestPath}/${PathBelowSrc}$(shell basename $(fd) .java).class)

ifeq (${TopDir}, ${PWD})
  nextdir:=""
else
  nextdir:=$$dir/
endif
#The EMPTY thing is a hack to stop bash from complaining
Recurse=EMPTY="";if [ "${SubDirs}" != "" ];then for dir in ${SubDirs} $$EMPTY; do if [[ ! -e $$dir/Makefile ]];then ln -s ../Makefile $$dir/Makefile;fi; $(MAKE) -C $$dir PathBelowSrc=${PathBelowSrc}${nextdir} $@;done;fi


.SILENT .PHONY: classes clean squeaky thisdir.classes thisdir.clean thisdir.squeaky doc jar all


thisdir.classes:${ClassFiles}
thisdir.clean:
thisdir.squeaky:thisdir.clean

classes:thisdir.classes
	${Recurse}

${ClassDestPath}/${PathBelowSrc}%.class: ${SourcePath}/${PathBelowSrc}%.java
	javac -d ${ClassDestPath} -classpath ${ClassPath} -sourcepath ${SourcePath} $<

clean:thisdir.clean
	${Recurse}

squeaky:thisdir.squeaky
	rm -f *~
	${Recurse}
	rm -f `find -maxdepth 1 -type l`



doc:
	mkdir -p ${APIDocPath}
	javadoc -private -classpath ${ClassPath} -sourcepath ${SourcePath} -d ${APIDocPath} -use -version -author  `find ${SourcePath} -name \*.java -exec dirname \{\} \;|cut -b $${#SourcePath}- |cut -b3-|sort|uniq|tr / .`


${JarPath}/manifest.mf:
	echo -n "" >${JarPath}/manifest.mf
	echo "Sealed: true">>${JarPath}/manifest.mf
	echo "Main-Class: czt.animation.gui.Gaffe">>${JarPath}/manifest.mf
#Add in Manifest-Version: entry
#Add in Name: and Java-Bean: entries

.INTERMEDIATE: ${JarPath}/manifest.mf
jar:classes ${JarPath}/manifest.mf
	jar cvfm ${JarPath}/gaffe.jar ${JarPath}/manifest.mf -C ${ClassDestPath} czt
	jar uvf ${JarPath}/gaffe.jar -C ${ResourcesPath} czt
	jar -i ${JarPath}/gaffe.jar

test:
	${Recurse}


# Change Log:
# $Log$
# Revision 1.4  2003/06/25 23:53:18  marku
# Added default settings for BSFHOME and RHINOHOME
#
# Revision 1.3  2003/06/23 06:04:49  ntd1
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
# Revision 1.2  2003/06/13 06:54:35  ntd1
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

# Rules.make
# 
# Change log at end of file.

all:jar

PWD=$(shell pwd)
export SourcePath=${TopDir}/src
export ClassDestPath=${TopDir}/classes
export ClassPath=${ClassDestPath}:${BSFHOME}/lib/bsf.jar:${RHINOHOME}/js.jar
export APIDocPath=${TopDir}/doc/api
export DistPath=${TopDir}/dist
export TempPath=${TopDir}/temp

SubDirs=$(foreach fd,$(shell echo */|sed s/\*\\///|sed s/CVS\\///),$(shell if [ ! $(fd) -ef $(TempPath) ];then echo $(fd);fi) )

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
	rm -rf ${TempPath}
	${Recurse}

squeaky:thisdir.squeaky
	rm -rf ${TempPath}
	rm -f *~
	${Recurse}
	rm -f `find -maxdepth 1 -type l`



doc:
	mkdir ${APIDocPath}
	javadoc -private -classpath ${ClassPath} -sourcepath ${SourcePath} -d ${APIDocPath} -use -version -author  `find ${SourcePath} -name \*.java -exec dirname \{\} \;|cut -b $${#SourcePath}- |cut -b3-|sort|uniq|tr / .`


${TempPath}/manifest.mf:
	mkdir -p ${TempPath}
	echo -n "" >${TempPath}/manifest.mf
	echo "Sealed: true">>${TempPath}/manifest.mf
	echo "Main-Class: czt.animation.gui.Gaffe">>${TempPath}/manifest.mf
#Add in Manifest-Version: entry
#Add in Name: and Java-Bean: entries


jar:classes ${TempPath}/manifest.mf
	mkdir -p ${TopDir}/lib
	jar cvfm ${TopDir}/lib/gaffe.jar ${TempPath}/manifest.mf -C ${ClassDestPath} czt
	jar -i ${TopDir}/lib/gaffe.jar

test:
	${Recurse}
# Change Log:
# $Log$
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
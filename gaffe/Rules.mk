# GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
# Copyright 2003 Nicholas Daley

# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

all:jar doc

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
  nextdir:=$$dir
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
	echo "Main-Class: net.sourceforge.czt.animation.gui.Gaffe">>${JarPath}/manifest.mf
#Add in Manifest-Version: entry
#Add in Name: and Java-Bean: entries

.INTERMEDIATE: ${JarPath}/manifest.mf
jar:classes ${JarPath}/manifest.mf
	jar cvfm ${JarPath}/gaffe.jar ${JarPath}/manifest.mf -C ${ClassDestPath} net/sourceforge/czt
	jar uvf ${JarPath}/gaffe.jar -C ${ResourcesPath} net/sourceforge/czt
	jar -i ${JarPath}/gaffe.jar

test:
	${Recurse}

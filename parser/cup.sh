#!/bin/sh
# Make sure to run 'ant install-bin' in CZT_HOME
# (this will generate ../bin/settings.sh) and
# 'ant prepare-cup' in this directory before using this script.
#
# This works with JavaCup 0.10j, which is the version that
# is included in J2SDK 1.4.2.  (It has some peculiar features,
# that are fixed in JavaCup 0.10k, like only reading the .cup file 
# from standard input)

source ../bin/settings.sh
BASEDIR=`pwd`

cd ${BASEDIR}/build/src/net/sourceforge/czt/parser/z

java -cp ${JAVA_CUP} java_cup.Main -parser Parser -symbols Sym < Parser.cup

cd ${BASEDIR}/build/src/net/sourceforge/czt/parser/oz

java -cp ${JAVA_CUP} java_cup.Main -parser Parser -symbols Sym < Parser.cup

cd ${BASEDIR}/build/src/net/sourceforge/czt/print/z

java -cp ${JAVA_CUP} java_cup.Main -parser Unicode2Latex -symbols Sym < Unicode2Latex.cup

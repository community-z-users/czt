#!/bin/sh
# This works with JavaCup 0.10j, which is the version that
# is included in J2SDK 1.4.2.  (It has some peculiar features,
# that are fixed in JavaCup 0.10k, like only reading the .cup file 
# from standard input)

source ../bin/settings.sh
BASEDIR=`pwd`

cd ${BASEDIR}/src/net/sourceforge/czt/parser/z
if [ LTZscanner.lex -nt LTZscanner.java ]
then
    java -cp ${JFLEX} JLex.Main LTZscanner.lex
    mv LTZscanner.lex.java LTZscanner.java
else
    echo "LTZscanner.java is up-to-date"
fi

java -cp ${JAVA_CUP} java_cup.Main -parser LTZparser -symbols LTZsym <LTZparser.cup

cd ${BASEDIR}/src/net/sourceforge/czt/parser/oz

java -cp ${JFLEX} JFlex.Main LatexScanner.flex
java -cp ${JFLEX} JFlex.Main UnicodeScanner.jflex
java -cp ${JAVA_CUP} java_cup.Main -parser Parser -symbols Sym < Parser.cup

cd ${BASEDIR}/src/net/sourceforge/czt/scanner

java -cp ${JAVA_CUP} java_cup.Main -parser Unicode2Latex < unicode2latex.cup
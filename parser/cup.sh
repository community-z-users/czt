#!/bin/sh
# This works with JavaCup 0.10j, which is the version that
# is included in J2SDK 1.4.2.  (It has some peculiar features,
# that are fixed in JavaCup 0.10k, like only reading the .cup file 
# from standard input)
cd src/net/sourceforge/czt/parser/z
if [ LTZscanner.lex -nt LTZscanner.java ]
then
    java JLex.Main LTZscanner.lex
    mv LTZscanner.lex.java LTZscanner.java
else
    echo "LTZscanner.java is up-to-date"
fi

java java_cup.Main -parser LTZparser -symbols LTZsym <LTZparser.cup

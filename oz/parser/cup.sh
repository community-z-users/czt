export OZ_JAVA_CUP=/usr/java/java_cup/
export OZ_JFLEX=/usr/java/JFlex/lib/JFlex.jar

export OZ_SRCDIR=src/net/sourceforge/czt/parser/oz

cd $OZ_SRCDIR
java -cp $OZ_JFLEX:$CLASSPATH JFlex.Main LatexScanner.flex
java -cp $OZ_JFLEX:$CLASSPATH JFlex.Main UnicodeScanner.jflex
java -cp $OZ_JAVA_CUP:$CLASSPATH java_cup.Main -parser LatexParser -symbols LatexSym < LatexParser.cup


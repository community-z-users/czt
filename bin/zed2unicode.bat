@echo off
call "%~f0\..\settings.bat"
java -classpath "%SESSION%;%PARSER%;%JAVA_CUP%;%COREJAVA%" net.sourceforge.czt.parser.z.LatexToUnicode %1 %2 %3 %4 %5 %6 %7 %8 %9

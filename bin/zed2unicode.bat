@echo off
call %~f0\..\settings.bat
java -classpath "%PARSER%;%JAVA_CUP%;%COREJAVA%" -Dczt.lib=%~f0\..\..\parser\lib net.sourceforge.czt.parser.z.LatexToUnicode %1 %2 %3 %4 %5 %6 %7 %8 %9

@echo off
call %~f0\..\settings.bat
java -classpath "%PARSER%;%JAVA_CUP%;%COREJAVA%" net.sourceforge.czt.parser.oz.Latex2Unicode %1 %2 %3 %4 %5 %6 %7 %8 %9

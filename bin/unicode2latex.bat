@echo off
call "%~f0\..\settings.bat"
java -classpath "%PARSER%;%COREJAVA%;%JAVA_CUP%" net.sourceforge.czt.print.z.UnicodeToLatex %1 %2 %3 %4 %5 %6 %7 %8 %9

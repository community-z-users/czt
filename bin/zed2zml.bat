@echo off
call "%~f0\..\settings.bat"
java -classpath "%SESSION%;%PARSER%;%COREJAVA%;%JWSDP%;%JAVA_CUP%" net.sourceforge.czt.parser.z.LatexParser %1 %2 %3 %4 %5 %6 %7 %8 %9

@echo off
call %~f0\..\settings.bat
java -classpath "%PARSER%;%COREJAVA%;%JWSDP%;%JAVA_CUP%" -Dczt.lib=%~f0\..\..\parser\lib net.sourceforge.czt.parser.oz.LatexParser %1 %2 %3 %4 %5 %6 %7 %8 %9

@echo off
call %~f0\..\settings.bat
java -classpath "%~f0\..;%BSH%;%ZLIVE%;%PARSER%;%COREJAVA%;%JWSDP%;%JAVA_CUP%" -Dczt.lib=%~f0\..\..\parser\lib bsh.Console %1 %2 %3 %4 %5 %6 %7 %8 %9

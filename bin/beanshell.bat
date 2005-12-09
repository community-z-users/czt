@echo off
call "%~f0\..\settings.bat"
java -classpath "%~f0\..;%BSH%;%ZLIVE%;%RULES%;%SESSION%;%PARSER%;%COREJAVA%;%TYPECHECKER%;%JWSDP%;%JAVA_CUP%" bsh.Console %1 %2 %3 %4 %5 %6 %7 %8 %9

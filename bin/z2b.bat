@echo off
call %~f0\..\settings.bat
java -classpath "%PARSER%;%GAFFE%;%COREJAVA%;%JWSDP%;%Z@B%" net.sourceforge.czt.z2b.Main %1 %2 %3 %4 %5 %6 %7 %8 %9

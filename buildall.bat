:: A convenience build script that performs 2-step build of CZT.

:: 2-step build is necessary to build CZT core modules needed for
:: Eclipse plug-ins. Only after the core is built, the plug-ins
:: can be located by CZT Eclipse dependency resolution.

:: See http://wiki.eclipse.org/Tycho/How_Tos/Dependency_on_pom-first_artifacts

:: call set MAVEN_OPTS=-Xmx1024m -XX:MaxPermSize=512m

:: Step 1: Build the CZT core
:: Note a check for errors, which stops the execution if Maven fails

call mvn clean install -U
if not "%ERRORLEVEL%" == "0" pause & exit /b

:: Step 2: Build the CZT Eclipse plug-ins

call mvn -f eclipse/pom.xml clean install -U
if not "%ERRORLEVEL%" == "0" pause & exit /b

:: pause to prevent window closing
pause

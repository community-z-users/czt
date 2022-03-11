:: call set MAVEN_OPTS=-Xmx1024m -XX:MaxPermSize=512m

call mvn site site:stage -P site -U
if not "%ERRORLEVEL%" == "0" pause & exit /b

:: pause to prevent window closing
pause

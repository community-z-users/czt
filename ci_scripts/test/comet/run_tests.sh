#!/usr/bin/env bash

# Check if the comet-clients package has been installed
cd ci_scripts/test/comet/
mvn dependency:get -Dartifact=com.smartesting.comet:javaclient:2.0.0
if [ $? -ne 0 ];
then
    git clone https://bitbucket.org/smartesting/comet-clients.git;
    cd comet-clients/java/comet-javaclient;
    mvn install;
	cd -
fi
mvn install > /dev/null
mvn exec:java -Dexec.mainClass="comet.CometJavaClient"

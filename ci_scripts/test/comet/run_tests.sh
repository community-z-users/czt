#!/usr/bin/env bash

# Check if the comet-clients package has been installed
cd ci_scripts/test/comet/
mvn dependency:get -Dartifact=ci_scripts:comet_testing:0.0.1 > /dev/null
if [ $? -ne 0 ];
then
    git clone https://bitbucket.org/smartesting/comet-clients.git > /dev/null;
    cd comet-clients/java/comet-javaclient;
    mvn clean install > /dev/null;
fi
cd -
mvn clean install > /dev/null
mvn exec:java -Dexec.mainClass="comet.CometJavaClient"

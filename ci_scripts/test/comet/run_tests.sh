#!/usr/bin/env bash

cd ci_scripts/test/comet/
mvn exec:java -Dexec.mainClass="comet.CometJavaClient"

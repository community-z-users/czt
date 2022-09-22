#!/usr/bin/env bash

cd ci_scripts/test/mutation_testing/tcp_systems/comet/
mvn exec:java -Dexec.mainClass="comet.CometJavaClient"

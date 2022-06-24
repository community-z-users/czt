#!/usr/bin/env bash

# Set the heap space needed for core builds
export MAVEN_OPTS="-Xmx1024m" 

# In case of Maven errors, terminate the full build as well
# set -e

# Set the build report output file
LOGFILE=build_report.txt

# Only compile and package source and test code (skip testing phase)
mvn clean install -U -Dmaven.test.skip.exec=true > >(tee ${LOGFILE}) 2>&1

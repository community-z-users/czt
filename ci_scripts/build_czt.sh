#!/usr/bin/env bash

# Set the heap space needed for core builds
export MAVEN_OPTS="-Xmx1024m" 

# In case of Maven errors, terminate the full build as well
set -e

# Set the build report output file
LOGFILE=build_report.txt

# Build the CZT core
# Output stdout and stderr to LOGFILE and to screen.
# mvn clean install -U > >(tee ${LOGFILE}) 2>&1
mvn clean compile -U > >(tee ${LOGFILE}) 2>&1

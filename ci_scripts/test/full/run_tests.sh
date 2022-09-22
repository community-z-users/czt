#!/usr/bin/env bash

# Set the build report output file
LOGFILE=test_report.txt

# Run automated test stuite
mvn surefire:test | tee $LOGFILE

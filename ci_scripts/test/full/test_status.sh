#!/usr/bin/env bash

# Check the build report for success status
# Return 1 if build succeeded and 0 if it has not.
cat test_report.txt | grep "BUILD SUCCESS" | wc -l

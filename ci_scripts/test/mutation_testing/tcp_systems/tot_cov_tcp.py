#!/usr/bin/env python3
"""
    Python script that runs tests that cover modified lines of code.
    Test classes are prioritised based on the percentage of the modified code
    class that they cover.

    1. Get modified classes
    2. Match modified code classes to test classes that cover modified code.
       Prioritise test classes based on largest coverage percentage
    3. Run the prioritised suite.
"""
import os
import sys
from collections import OrderedDict

print("Total Coverage TCP System")

# Parse the coverage_data.txt file and extract data into 3 lists
src_files = []
tst_files = []
coverage = []
with open("ci_scripts/test/coverage/total/coverage_data.txt", 'r') as data_file:
    for line in data_file:
        data = line.split(',')
        src_files.append(data[0])
        tst_files.append(data[1])
        coverage.append(int(data[2]))

""" Utility function to match tokens to a string """
def match_path(string, tokens):
    for token in tokens:
        if token not in string:
            return False
    return True

changed_files = sys.argv[1:]

# Match to coverage data
test_classes = {}
for line in changed_files:
	for i, f in enumerate(src_files):
		if match_path(line, f.split('-')):
			test_classes[tst_files[i]] = int(coverage[i])

# Prioritised tests
for test_class in sorted(test_classes, key=test_classes.get, reverse=True):
	print(test_class)

# The rest of the test cycle
unique_tests = list(set(tst_files))
for test_class in unique_tests:
	print(test_class)


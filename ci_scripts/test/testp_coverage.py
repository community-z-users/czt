#!/usr/bin/env python3

import os

""" Global Variables """
MODIFIED_CLASSES = []
TESTS = {}

# Get a list of modified class names
with open('ci_scripts/text_files/changed_files.txt', 'r') as changed_files:
    for path in changed_files:
        MODIFIED_CLASSES.append(path.split('/')[-1].split('.java')[0])

# For each modified class name, find the tests that cover code in that class

for target_class in MODIFIED_CLASSES:
    print("Looking for tests that cover code in:", target_class)

    # For all test data, go through csv file and look for lines that contain 
    # the target class
    for csv_file in os.listdir("ci_scripts/test/coverage/data"):
        with open("ci_scripts/test/coverage/data/" + csv_file, 'r') as test_data:
            for line in test_data:
                if (target_class in line):
                    lines_covered = int(line.split(',')[8])
                    if lines_covered > 0:
                        file_name = csv_file.split('.csv')[0]
                        TESTS[file_name] = lines_covered 

with open("ci_scripts/test/test_classes.txt", 'w') as output_file:
    # NOTE: Remember to order the tests by code coverage
    for test, lines in TESTS.items():
        module = test.split('_')[0]
        test = test.split('_')[1]
        output_file.write(module + ',' + test)

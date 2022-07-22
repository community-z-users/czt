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

DEBUG_MODE = False
if(len(sys.argv) > 1):
	arg = sys.argv[1]
	if (arg.lower() == "--debug"):
		DEBUG_MODE = True
	else:
		print("'" + arg + "' is not a valid argument. Remove arguments or try '--debug'")
		exit()


# Parse the coverage_data.txt file and extract data into 3 lists
src_files = []
tst_files = []
coverage = []
with open("ci_scripts/test/coverage/coverage_data.txt", 'r') as data_file:
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

stream = os.popen('git diff --name-only HEAD main')
changed_files = stream.read().strip().split('\n')
# TESTING
#changed_files = ['./corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java',
#        './zml/src/main/java/net/sourceforge/czt/zml/Resources.java']

# Match to coverage data
test_classes = {}
for line in changed_files:
	if DEBUG_MODE:
		print('Modified:',line)
		for i, f in enumerate(src_files):
			if match_path(line, f.split('-')):
				print('-->', tst_files[i].split('-')[-1], 'has coverage score of', str(coverage[i]))
				test_classes[tst_files[i]] = int(coverage[i])
		print()
	else:
		for i, f in enumerate(src_files):
			if match_path(line, f.split('-')):
				test_classes[tst_files[i]] = int(coverage[i])


# Print ordered list and run tests
if DEBUG_MODE:
	print("Prioritised Test Class List:")
	for i, test_class in enumerate(sorted(test_classes, key=test_classes.get, reverse=True)):
		print(str(i+1) + '.', test_class.split('-')[-1])
	print()

# Prioritised tests
for test_class in sorted(test_classes, key=test_classes.get, reverse=True):
	name = test_class.replace('-', '.')
	line = "[INFO] Testing " + name + " : "
	print(line, end="", flush=True)
	err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + name + " >/dev/null 2>&1")
	if err:
		print("FAILED".rjust(99-len(line)))
		break
	else:
		print("PASSED".rjust(99-len(line)))

# The rest of the test cycle
FAILED_TEST = False
if DEBUG_MODE:
	print()
	print("Other tests")
unique_tests = list(set(tst_files))
for test_class in unique_tests:
	name = test_class.replace('-', '.')
	if not (test_class in test_classes.keys()):
		line = "[INFO] Testing " + name + " : "
		print(line, end="", flush=True)
		err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + name 
			+ " >test_output.txt 2>&1")
		if err:
			FAILED_TEST = True
			print("FAILED".rjust(99-len(line)))
			if DEBUG_MODE:
				os.system("cat test_output.txt")
		else:
			print("PASSED".rjust(99-len(line)))

os.system("rm test_output.txt")
if FAILED_TEST:
	exit(1)

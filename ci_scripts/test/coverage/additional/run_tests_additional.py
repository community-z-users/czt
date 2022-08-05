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
with open("ci_scripts/test/coverage/additional/additional_coverage_data.txt", 'r') as data_file:
	for line in data_file:
		data = line.split(',')
		src_files.append(data[0])
		tst_files.append(data[1])
		coverage.append(data[2].split("[")[-1].split("]")[0].split(";"))


""" Utility function to match tokens to a string """
def match_path(m_file, s_file):
	s_file = s_file + ".java"
	return m_file.endswith(s_file)

stream = os.popen('git diff --name-only HEAD main')
changed_files = stream.read().strip().split('\n')

# Match to coverage data
prioritisation = []
redundant_prioritisation = []
unprioritised = []

for m_file in changed_files:
	test_classes = {}

	print('Modified:',m_file)
	# Collect test classes that cover the source file
	for i, s_file in enumerate(src_files):
		if match_path(m_file, s_file):
			test_classes[tst_files[i]] = coverage[i]

	# Add test classes to prioritisation if possible
	covered_lines = []
	all_lines_covered = False

	while not all_lines_covered:
		all_lines_covered = True
		next_best_test_key = "" # Keep track of best next test
		max_additional_lines = 0
		for key in test_classes.keys():
			# Decide whether this test class has been covered before
			test_run_before = key in prioritisation
			test_fully_covered = all(line in covered_lines for line in test_classes[key])
			if ((not test_run_before) and (not test_fully_covered)):
				all_lines_covered = False
				additional_lines = len(test_classes[key]) - sum(line in covered_lines for line in test_classes[key])
				if additional_lines > max_additional_lines:
					next_best_test_key = key
					max_additional_lines = additional_lines


		if not all_lines_covered:
			# Add the test class to the prioritisation list and update the covered lines
			prioritisation.append(next_best_test_key)
			for line in test_classes[next_best_test_key]:
				if line not in covered_lines:
					covered_lines.append(line)
			
			# If this test was in the redundant_prioritisation list, remove it as it is now in the
			# prioritised list.
			if (next_best_test_key in redundant_prioritisation):
				redundant_prioritisation.remove(next_best_test_key)

		else:
			# Put the tests which did not make the first prioritisation into the redundant list
			for key in test_classes.keys():
				if not key in prioritisation:
					redundant_prioritisation.append(key)

# Collect the rest of the test classes that don't have any prioritisation
for test in tst_files:
	if ((not test in prioritisation) 
			and (not test in redundant_prioritisation) 
			and (not test in unprioritised)):
		unprioritised.append(test)

FAILED_TEST = False

# Prioritised tests
for test_class in prioritisation:
	line = "[INFO] Testing " + test_class + " : "
	print(line, end="", flush=True)
	err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + test_class + " >/dev/null 2>&1")
	if err:
		print("FAILED".rjust(99-len(line)))
		FAILED_TEST=True
		break
	else:
		print("PASSED".rjust(99-len(line)))

# Redundant tests
for test_class in redundant_prioritisation:
	line = "[INFO] Testing " + test_class + " : "
	print(line, end="", flush=True)
	err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + test_class + " >/dev/null 2>&1")
	if err:
		print("FAILED".rjust(99-len(line)))
		FAILED_TEST=True
		break
	else:
		print("PASSED".rjust(99-len(line)))

# Unprioritised tests
for test_class in unprioritised:
	line = "[INFO] Testing " + test_class + " : "
	print(line, end="", flush=True)
	err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + test_class + " >/dev/null 2>&1")
	if err:
		print("FAILED".rjust(99-len(line)))
		FAILED_TEST=True
		break
	else:
		print("PASSED".rjust(99-len(line)))

os.system("rm test_output.txt")
if FAILED_TEST:
	exit(1)

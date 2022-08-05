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

# stream = os.popen('git diff --name-only HEAD main')
# changed_files = stream.read().strip().split('\n')
# TESTING
changed_files = ['./zlive/src/main/java/net/sourceforge/czt/animation/eval/ExprComparator.java',
       './zml/src/main/java/net/sourceforge/czt/zml/Resources.java',
	   './corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java']

# Match to coverage data
prioritisation = []

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
			print("\n",key)


			# Decide whether this test class has been covered before
			print(key in prioritisation)
			print(all(line in covered_lines for line in test_classes[key]))
			test_run_before = key in prioritisation
			test_fully_covered = all(line in covered_lines for line in test_classes[key])
			if ((not test_run_before) and (not test_fully_covered)):
				all_lines_covered = False
				additional_lines = len(test_classes[key]) - sum(line in covered_lines for line in test_classes[key])
				print(additional_lines)
				if additional_lines > max_additional_lines:
					print("here")
					next_best_test_key = key
					max_additional_lines = additional_lines


		if not all_lines_covered:
			prioritisation.append(next_best_test_key)
			for line in test_classes[next_best_test_key]:
				if line not in covered_lines:
					covered_lines.append(line)


print(prioritisation)
exit()





	# if DEBUG_MODE:

	# else:
	# 	for i, f in enumerate(src_files):
	# 		if match_path(m_file, f.split('-')):
	# 			test_classes[tst_files[i]] = int(coverage[i])

# exit()
# # Print ordered list and run tests
# if DEBUG_MODE:
# 	print("Prioritised Test Class List:")
# 	for i, test_class in enumerate(sorted(test_classes, key=test_classes.get, reverse=True)):
# 		print(str(i+1) + '.', test_class.split('-')[-1])
# 	print()

# # Prioritised tests
# for test_class in sorted(test_classes, key=test_classes.get, reverse=True):
# 	name = test_class.replace('-', '.')
# 	line = "[INFO] Testing " + name + " : "
# 	print(line, end="", flush=True)
# 	err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + name + " >/dev/null 2>&1")
# 	if err:
# 		print("FAILED".rjust(99-len(line)))
# 		break
# 	else:
# 		print("PASSED".rjust(99-len(line)))

# # The rest of the test cycle
# FAILED_TEST = False
# if DEBUG_MODE:
# 	print()
# 	print("Other tests")
# unique_tests = list(set(tst_files))
# for test_class in unique_tests:
# 	name = test_class.replace('-', '.')
# 	if not (test_class in test_classes.keys()):
# 		line = "[INFO] Testing " + name + " : "
# 		print(line, end="", flush=True)
# 		err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + name 
# 			+ " >test_output.txt 2>&1")
# 		if err:
# 			FAILED_TEST = True
# 			print("FAILED".rjust(99-len(line)))
# 			if DEBUG_MODE:
# 				os.system("cat test_output.txt")
# 		else:
# 			print("PASSED".rjust(99-len(line)))

# os.system("rm test_output.txt")
# if FAILED_TEST:
# 	exit(1)

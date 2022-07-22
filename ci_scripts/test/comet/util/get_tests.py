#!/usr/bin/env python3

"""
	1. 	Get all test IDs from the coverage_data.txt file
	2. 	Identify modified modules
	3. 	Add classChanged and testChanged information
"""

"""     IMPORTS     """
import os


"""     GLOBAL VARIABLES     """
TESTS = {} # { test_name: (classChanged, testChanged), ... }
MODIFIED_FILES = []

"""     UTILITY FUNCTIONS     """
def name_from_path(path):
    return path.split(".java")[0].split("/")[-1]

def match_path(file_path, data_path):
	fp_name = name_from_path(file_path)
	dp_name = data_path.split('-')[-1]
	if (fp_name == dp_name):
		for token in data_path.split('-'):
			if not (token in file_path):
				return False
	else:
		return False
	return True


"""     MAIN SCRIPT     """
stream = os.popen('git diff --name-only HEAD main')
# MODIFIED_FILES = stream.read().strip().split('\n') 
MODIFIED_FILES = \
		[ "corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java",
		  "corejava/corejava-z/src/main/java/net/sourceforge/czt/z/jaxb/JaxbXmlReader.java",
		  "corejava/corejava-z/src/test/java/net/sourceforge/czt/base/util/XmlWriterReaderTest.java",
		  "corejava/corejava-z/src/test/java/net/sourceforge/czt/z/jaxb/JaxbXmlWriterReaderTest.java"]

os.chdir("../../..")
CZT_HOME=os.getcwd()

with open("ci_scripts/test/coverage/coverage_data.txt", "r") as data:
	for line in data:
		src, test, score = line.split(',')
		test_module_path = test.replace('-', '.')
		if (test_module_path not in TESTS.keys()):
			TESTS[test_module_path] = (False, False)

		for file_name in MODIFIED_FILES:
			# If the modified file matches the source name, classChanged = True
			if match_path(file_name, src): 
				if match_path(file_name, test):
					TESTS[test_module_path] = (True, True)
				else:
					classChanged, testChanged = TESTS[test_module_path]
					TESTS[test_module_path] = (True, testChanged)


for key in TESTS:
	print(key + "," + str(TESTS[key][0]) + "," + str(TESTS[key][1]))


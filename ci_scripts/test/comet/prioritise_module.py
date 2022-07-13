#!/usr/bin/env python3

"""
    1.  Identify tests within this module 
    2.  Identify modified files
    3.  Find the tests that cover modified files and filter for tests that are 
        in this module
    4.  Return the following information:
            * Whether the source file that the test covers has been modified
            * Whether the test file has been modified
"""

"""     IMPORTS     """
import os


"""     GLOBAL VARIABLES     """
MODULE_HOME = os.getcwd()
TESTS = []
MODIFIED_FILES = []
OUTPUT_DATA = {} # { test_name: (classChanged, testChanged), ... }


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
# 1)
os.chdir("src/test")
stream = os.popen('find -name "*.java"')
TESTS = stream.read().strip().split('\n')
for test in TESTS:
	OUTPUT_DATA[name_from_path(test)] = (False, False)
os.chdir(MODULE_HOME)

# 2)
stream = os.popen('git diff --name-only HEAD main')
# MODIFIED_FILES = stream.read().strip().split('\n') 
MODIFIED_FILES = \
		[ "corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java",
		  "corejava/corejava-z/src/main/java/net/sourceforge/czt/z/jaxb/JaxbXmlReader.java",
		  "corejava/corejava-z/src/test/java/net/sourceforge/czt/base/util/XmlWriterReaderTest.java"]

# 3)
# find path to coverage data
target = os.path.join(MODULE_HOME, 'ci_scripts')
while not (os.path.exists(target)):
	os.chdir('..')
	target = os.path.join(os.getcwd(), 'ci_scripts')
data_path = target + '/test/coverage/coverage_data.txt'
os.chdir(MODULE_HOME)

with open(data_path, 'r') as data_file:
	for line in data_file:
		source_class, test_class, score = line.split(',')
		for f in MODIFIED_FILES:
			if match_path(f, source_class):
				for test in TESTS:
					if match_path(test, test_class):
						OUTPUT_DATA[name_from_path(test)] = (True, False)
				

# 4)
for f in MODIFIED_FILES:
	for test in TESTS:
		if f.endswith(test.split('./')[-1]):
			classChanged, testChanged = OUTPUT_DATA[name_from_path(test)]
			OUTPUT_DATA[name_from_path(test)] = (classChanged, True)

for key in OUTPUT_DATA:
	print(key + "," + str(OUTPUT_DATA[key][0]) + ',' + str(OUTPUT_DATA[key][1]))


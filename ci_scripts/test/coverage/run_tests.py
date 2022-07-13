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
from collections import OrderedDict

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

#stream = os.popen('git diff --name-only HEAD main')
#changed_files = stream.read().strip().split('\n')
# TESTING
changed_files = ['./corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java',
        './zml/src/main/java/net/sourceforge/czt/zml/Resources.java']

# Match to coverage data
test_classes = {}
for line in changed_files:
    print('Modified:',line)
    for i, f in enumerate(src_files):
        if match_path(line, f.split('-')):
            print('-->', tst_files[i].split('-')[-1], 'has coverage score of', str(coverage[i]))
            test_classes[tst_files[i]] = int(coverage[i])
    print()

""" Utility function to get path to module from test class """
def get_module_path(test_class):
    # Locate test file
    tokens = test_class.split('-')
    for root, dirs, files in os.walk('.'):
        for f in files:
            full_path = os.path.join(root, f)
            if ((test_class.replace('-','/') in full_path) and \
                    full_path.endswith(".java") and \
                    ('/target/' not in full_path)):
                #print(full_path)
                module_dir = os.path.dirname(full_path)

    # Go up until you hit pom.xml
    found_module = False
    while not found_module:
        target = os.path.join(module_dir, 'pom.xml')
        if (os.path.exists(target)):
            found_module = True
        else:
            module_dir = os.path.dirname(module_dir)

    return module_dir

# Print ordered list
print("Prioritised Test Class List:")
for i, test_class in enumerate(sorted(test_classes, key=test_classes.get, reverse=True)):
    print(str(i+1) + '.', test_class.split('-')[-1])
print()

CZT_HOME=os.getcwd()
for test_class in sorted(test_classes, key=test_classes.get, reverse=True):

    # Navigate to correct module directory
    os.chdir(get_module_path(test_class))
    name = test_class.split('-')[-1]

    # Run the specific test
    err = os.system("mvn surefire:test -Dtest=" + name)
    if err:
        break

    # Go back to the CZT HOME directory for the next test
    os.chdir(CZT_HOME)

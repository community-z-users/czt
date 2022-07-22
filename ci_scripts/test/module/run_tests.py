#!/usr/bin/env python3

""" 
    Python script that runs module tests based on modified code of each module.

    1. Get modified modules
    2. Prioritise modified modules topologically
    3. Get modules dependent on modified modules
    4. Prioritise dependent modules topologically
    5. Run module tests in prioritised order
"""

import os
import subprocess


""" Get list of modules that can be tested """
# Filter prioritised list by modules that contain tests
output = subprocess.check_output('find -wholename "*src/test"', shell=True).decode()
testable_modules = []
for line in output.split('\n'):
    if line != "":
        line = line.split('/src/test')[0]
        line = line.split('/')[-1].replace("-", "_")
        testable_modules.append(line)


""" Parse through czt_dependencies.dot and extract dependency relationships """
modules = {}
with open("ci_scripts/dependency_tree/czt_dependencies.dot", "r") as dot_file:
    for line in dot_file:
        if not (('{}' in line) or ('digraph' in line) or (line.strip() == '}')):
            module_name = line.split(' ->')[0].strip()
            if module_name in testable_modules:
                deps = line.split(' ->')[1].replace('{', '').replace('}', '').strip().split('  ')
                modules[module_name] = deps


""" Utility function to get a rank of a module """
def get_rank(module, target):
    ranks = [0]
    if (module == target):
        ranks.append(1)
    elif ((module in modules.keys()) and (target in modules[module])):
        for dep in modules[module]:
            if (dep == target):
                ranks.append(2)
            else:
                ranks.append(1 + get_rank(dep, target))
    return max(ranks)


""" Get modified modules """
# Comparing HEAD to main
stream = os.popen('git diff --name-only HEAD origin/main')

# Using local changes (For testing)  
# stream = os.popen('git diff --name-only HEAD .')

changed_files = stream.read().strip().split('\n')


modified_modules = []
print("\nModified Modules:")
for line in changed_files:
    found_module = False
    module_dir = os.path.dirname(line.strip())
    while not found_module:
        target = os.path.join(module_dir, 'pom.xml')
        if (os.path.exists(target)):
            found_module = True
        else:
            module_dir = os.path.dirname(module_dir)
    if (module_dir != "") and (module_dir not in modified_modules):
        modified_modules.append(module_dir)
        print('-->', module_dir.split('/')[-1])

# Remove duplicates
modified_modules = list(set(modified_modules))

""" Do topological sort of modified modules """
ranked_mod_modules = {}
for module in modified_modules:
    for other_mod in modified_modules:
        if (other_mod != module):
            target = module.split('/')[-1].replace('-','_').strip()
            mod = other_mod.split('/')[-1].replace('-','_').strip()
            rank = get_rank(mod, target)

            if mod in ranked_mod_modules.keys():
                ranked_mod_modules[mod] = max(rank, ranked_mod_modules[mod])
            else:
                ranked_mod_modules[mod] = rank


""" Do topological sort of depentent modules """
ranked_dep_modules = {}
for module in modified_modules:
    target = module.split('/')[-1].replace('-','_').strip()

    for mod in modules:
        if(mod not in ranked_mod_modules.keys()):
            rank = get_rank(mod, target)
            if rank:
                if mod in ranked_dep_modules.keys():
                    ranked_dep_modules[mod] = min(rank, ranked_dep_modules[mod])
                else:
                    ranked_dep_modules[mod] = rank

""" Find module paths """
prioritised_paths = []
for module in sorted(ranked_mod_modules, key=ranked_mod_modules.get):
    target = module.split('/')[-1].replace('_', '-').strip()
    target = os.path.join(target, 'pom.xml')

    for root, dirs, files in os.walk('.'):
        for f in files:
            full_path = os.path.join(root, f)
            if (full_path.endswith(target)):
                prioritised_paths.append(os.path.dirname(full_path))

for module in sorted(ranked_dep_modules, key=ranked_dep_modules.get):
    target = '/' + module.split('/')[-1].replace('_', '-').strip()
    target = os.path.join(target, 'pom.xml')
    
    for root, dirs, files in os.walk('.'):
        for f in files:
            full_path = os.path.join(root, f)
            if (full_path.endswith(target)):
                prioritised_paths.append(os.path.dirname(full_path))


# Print prioritised list
print('\nPrioritised Module List:')
paths_to_test = []
for path in prioritised_paths:
    name = path.split('/')[-1]
    if name.replace('-','_') in testable_modules:
        paths_to_test.append(path)
        print('-->', path)


# Test prioritised list
CZT_HOME = os.getcwd()
FAILED_TEST = False
for path in paths_to_test:

    # Navigate to correct module directory
    os.chdir(path)

    # Run the specific test 
    if ('eclipse' in path):
        print("\nSKIPPING:", path)
    else:
        print("\nTESTING:", path, end="", flush=True)
        output = ""
        try:
            output = subprocess.check_output("mvn surefire:test 2>/dev/null", shell=True).decode()
            print()
        except(subprocess.CalledProcessError):
            print(" ERROR")
        finally:
            output_list = output.split('\n')
            for i, line in enumerate(output_list):
                if (("Tests run:" in line) and ("in net.sourceforge" in line)):
                # if ("Running" in line):
                    fail = line.split("Failures: ")[-1].split(",")[0] != "0"
                    error = line.split("Errors: ")[-1].split(",")[0] != "0"
                    outcome = "[INFO] Testing "+ line.split('sourceforge.')[-1] + " : "
                    if (fail or error):
                        print(outcome + "FAILED".rjust(99-len(outcome)))
                        print(line)
                        FAILED_TEST = True
                    else:
                        print(outcome + "PASSED".rjust(99-len(outcome)))


    # Go back to the CZT HOME directory for the next test
    os.chdir(CZT_HOME)      

if FAILED_TEST:
    exit(1)
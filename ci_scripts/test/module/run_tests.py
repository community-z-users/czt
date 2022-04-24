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



""" Parse through czt_dependencies.dot and extract dependency relationships """
modules = {}
with open("ci_scripts/dependency_tree/czt_dependencies.dot", "r") as dot_file:
    for line in dot_file:
        if not (('{}' in line) or ('digraph' in line) or (line.strip() == '}')):
            module_name = line.split(' ->')[0].strip()
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


""" Utility function that returns topological sort of modules """
def prioritise_list(unsorted_modules):
    pass


""" Get modified modules """
#stream = os.popen('git diff --name-only HEAD HEAD~1')
#changed_files = stream.read().strip().split('\n')
changed_files = ['./corejava/corejava-z/src/main/java/net/sourceforge/czt/z/util/OperatorName.java', \
    '/home/samuelv/czt/corejava/corejava-zpatt/src/main/java/net/sourceforge/czt/zpatt/util']

modified_modules = []
for line in changed_files:
    found_module = False
    module_dir = os.path.dirname(line.strip())
    while not found_module:
        target = os.path.join(module_dir, 'pom.xml')
        if (os.path.exists(target)):
            found_module = True
        else:
            module_dir = os.path.dirname(module_dir)
    modified_modules.append(module_dir)
    print(module_dir)

# Remove duplicates
modified_modules = list(set(modified_modules))


""" Do topological sort of modified modules """
ranked_modules = {}
for module in modified_modules:
    target = module.split('/')[-1].replace('-','_').strip()

    for mod in modules:
        rank = get_rank(mod, target)
        if rank:
            if mod in ranked_modules.keys():
                ranked_modules[mod] = min(rank, ranked_modules[mod])
            else:
                ranked_modules[mod] = rank

""" Find module paths """
prioritised_paths = []
for module in sorted(ranked_modules, key=ranked_modules.get):
    target = module.split('/')[-1].replace('_', '-').strip()
    target = os.path.join(target, 'pom.xml')

    for root, dirs, files in os.walk('.'):
        for f in files:
            full_path = os.path.join(root, f)
            if (full_path.endswith(target)):
                prioritised_paths.append(os.path.dirname(full_path))

CZT_HOME = os.getcwd()
for path in prioritised_paths:

    # Navigate to correct module directory
    os.chdir(path)

    # Run the specific test 
    print("\nTESTING:", path) 
    err = os.system("mvn surefire:test")    
    if err:
        break

    #test_passed = False
    #for line in output:
    #    if "BUILD SUCCESS" in line:
    #        test_passed = True
    #if not test_passed:
    #    break

    # Go back to the CZT HO ME directory for the next test
    os.chdir(CZT_HOME)      
                            
                            
                            
                            
                            

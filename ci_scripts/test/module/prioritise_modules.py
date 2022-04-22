#!/usr/bin/env python3


""" Parse through czt_dependencies.dot and extract deps """
modules = {}
with open("ci_scripts/dependency_tree/czt_dependencies.dot", "r") as dot_file:
    for line in dot_file:
        if not (('{}' in line) or ('digraph' in line) or (line.strip() == '}')):
            module_name = line.split(' ->')[0].strip()
            deps = line.split(' ->')[1].replace('{', '').replace('}', '').strip().split('  ')
            modules[module_name] = deps
print()


""" Utility function to get a rank of a module """
def get_rank(module, target):
    ranks = [0]
    if ((module in modules.keys()) and (module != target) and (target in modules[module])):
        for dep in modules[module]:
            if (dep == target):
                ranks.append(1)
            else:
                ranks.append(1 + get_rank(dep, target))
    return max(ranks)
            

"""
    Generate topological prioritised list of modules to test
    1. Get modified modules from 'ci_scripts/text_files/modules_to_test.txt'
    2. For each module, check which other modules are dependent on that module
       and rank how close they are.
    3. Combined ordered ranks of modified modules by taking the minimum
"""
ranked_modules = {} 
with open("ci_scripts/text_files/modules_to_test.txt", "r") as modified_modules:
    for module in modified_modules:
        target = module.split('/')[-1].replace('-','_').strip()
        print(target)

        for module in modules:
           ranked_modules[module] = get_rank(module, target) 


with open("ci_scripts/text_files/dependencies.txt", "w") as output_file:
    for mod in sorted(ranked_modules, key=ranked_modules.get):
        if (ranked_modules[mod] > 0):
            output_file.write(mod.replace('_', '-') + '\n')


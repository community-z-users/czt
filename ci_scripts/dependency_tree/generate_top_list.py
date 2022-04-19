#!/usr/bin/env python3

import subprocess

with open('ci_scripts/text_files/unsorted_deps.txt', 'r') as dot_file:
    modules = []
    for line in dot_file:
        if not (('{}' in line) or ('digraph' in line) or (line.strip() == '}')):
            modules.append(line.strip())


    sorted_modules = []
    added = False
    for i, module in enumerate(modules):
        added = False
        # Extract name from the module line
        name = module.split(' ->')[0].replace('_', '-')

        if i == 0:
            sorted_modules.append(name)
        else:
            # Check in sorted list whether this module is a dependency of another
            for i, mod in enumerate(sorted_modules):
                if name in mod:
                    sorted_modules.insert(i, name)
                    added = True
                    break

            if not added:
                sorted_modules.append(name)

with open('ci_scripts/text_files/sorted_deps.txt', 'w') as output_file:
    for mod in sorted_modules:
        output_file.write(mod + '\n')

#!/usr/bin/env python3

import subprocess 

first_module = True

with open('ci_scripts/czt_dependencies.dot', 'w') as dot_file:
    dot_file.write("digraph {")

    # Read in output from 'mvn dependency:tree' call
    output = subprocess.run(['mvn', 'dependency:tree'], capture_output=True, text=True)

    for line in output.stdout.splitlines():
        if ("[INFO] net.sourceforge.czt" in line):
            # New module found
            module_name = line.split(":")[1].replace('-', '_')
            if first_module:
                dot_file.write("\n\t" + module_name + " -> {")
                first_module = False
            else:
                dot_file.write("}\n\t" + module_name + " -> {")

        elif ("[INFO] +- net.sourceforge.czt:" in line):
            # Dependency of module found
            dot_file.write(" " + line.split(":")[1].replace('-', '_') + " ")

    dot_file.write("}\n}\n")
    

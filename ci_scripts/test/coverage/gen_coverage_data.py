#!/usr/bin/env python3

import os



"""
    Utility function to extract test class from package ending with 
    test name
"""
def get_class(test_name):
    return_string = "czt"
    for string in test_name.split('.'):
        return_string += '_' + string
    return return_string
        

"""
    1. Recursively open all html files
    2. Get package name from <body>
    3. Get tests by looking for <test-"">
        - Get coverage data
        - get test path
    4. Compile data into coverage_data.txt file in following format:
        CLASS_NAME,TEST_CLASS_NAME,COVERAGE_%
"""
is_reading = False
with open("coverage_data.txt", "w") as output_file:
    for rt, sbdrs, files in os.walk("clover"):
        for filename in files:
            if ("html" in filename):
                with open(os.path.join(rt, filename), "r") as f:
                    for line in f:
                        if(("body" in line) and ("onload" in line) and ("net.sourceforge.czt." in line)):
                            #print(filename)
                            module_name = line.split("net.sourceforge.czt.")[1].split(".java")[0].strip().replace('.','_')
                            print(module_name)

                        if (line.strip().startswith('<tr id="test-')):
                            is_reading = True
                            test_num = int(line.strip().split('test-')[1].split('">')[0].strip())

                        if is_reading:
                            if (line.strip() == '</tr>'):
                                output_file.write(module_name + ',' + test_class + ',' + str(coverage) + '\n')
                                is_reading = False
                            else:
                                if (('<div title=' in line) and ("Covered" in line)):
                                    coverage = float(line.split('title="')[1].split('%')[0])

                                if (line.strip().startswith('<td id="tc-' + str(test_num) + '">')):
                                    test_name = line.split('title="View Test Summary Page">net.sourceforge.czt.' \
                                            )[1].split('</a')[0]
                                    test_class = get_class(test_name)

                









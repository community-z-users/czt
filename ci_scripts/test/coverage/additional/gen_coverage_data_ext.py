#!/usr/bin/env python3
import subprocess
import os
import json

HOME=os.getcwd()
os.chdir("../clover")
CLOVER_HOME=os.getcwd()

output = subprocess.check_output('find -name "*.js" | grep "net/sourceforge/czt"', shell=True).decode()

COVERAGE_FILE_PATHS = []
for line in output.split('\n'):
    COVERAGE_FILE_PATHS.append(line)


"""
Coverage data is modelled by a dictionary tree:

COVERAGE_DATA = {

    "source_class_path_1": {
        "test-1": {
            "name": testSomething,
            "module": "net.sourceforge.czt.parser.z.CyclicParentParserTest"
            "methods": [],
            "pass": true,
            "statements": []
        },
        "test-2": {
            "name": testNothing,
            "methods": [],
            "pass": true,
            "statements": []
        }
    },
    "source_class_path_2": {
        ...
    },
    ...
}
"""
COVERAGE_DATA = {}

for src_path in COVERAGE_FILE_PATHS:
    # Parse js files to get testTarget data
    key = src_path.split('./')[-1].split('.js')[0]
    if key != "":
        with open(src_path, "r") as f:
            for line in f:
                if "clover.testTargets" in line:
                    data = line.split("=")[-1].strip()
                    if (data != "{}"):
                        COVERAGE_DATA[key] = {}
                        test_cases = json.loads(data)
                        COVERAGE_DATA[key] = test_cases

    # Find corresponding html file to extract the module path
    if key in COVERAGE_DATA.keys():
        html_path = "./" + key + ".html"
        for test_id in COVERAGE_DATA[key].keys():
            test_token = "tc-" + test_id.split("_")[-1]
            test_name = COVERAGE_DATA[key][test_id]["name"]

            with open(html_path, "r") as f:
                for line in f:
                    if ((test_token in line) and (test_name in line)):
                        module = line.split('<span class="sortValue">')[-1].split("." + test_name)[0]
                        COVERAGE_DATA[key][test_id]["module"] = module


OUTPUT_DATA = {}
for src_class in COVERAGE_DATA.keys():
    OUTPUT_DATA[src_class] = {}
    for test_id in COVERAGE_DATA[src_class].keys():
        test_class = COVERAGE_DATA[src_class][test_id]["module"]
        
        # Get src_lines
        covered_lines = []
        for line in COVERAGE_DATA[src_class][test_id]["methods"]:
            covered_lines.append(line["sl"])
            
        # Put into output data
        if test_class not in OUTPUT_DATA[src_class].keys():
            OUTPUT_DATA[src_class][test_class] = covered_lines
        else:
            for line in covered_lines:
                if line not in OUTPUT_DATA[src_class][test_class]:
                    OUTPUT_DATA[src_class][test_class].append(line)

os.chdir(HOME)
with open("additional_coverage_data.txt", "w") as output_file:
    for src_class in OUTPUT_DATA.keys():
        # print(src_class)
        for test_class in OUTPUT_DATA[src_class].keys():
            data = "["
            for i, num in enumerate(OUTPUT_DATA[src_class][test_class]):
                if i == 0:
                    data += str(num)
                else:
                    data += ";" + str(num)
            data += "]"
            line = src_class + "," + test_class + "," + data
            output_file.write(line + '\n')





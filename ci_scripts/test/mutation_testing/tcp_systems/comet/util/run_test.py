#!/usr/bin/env python3

import sys
import os


# Get ID of test run
test_id = sys.argv[1]
test_num = -1

# Get test number from test ID
with open("../../data/metadata/test_lookup_table.csv", "r") as f:
	for line in f:
		num, name = line.strip().split(",")
		if(name == test_id):
			test_num = num
if(test_num == -1):
	print("Couldn't find test num")
	exit(1)

# Determine Cycle Number
test_cycles = os.listdir("../../test_cycles")
cycle_num = 0
for directory in test_cycles: 
	num = int(directory.split("test_cycle_")[-1])
	if num > cycle_num:
		cycle_num = num

# Determine iteration number
iterations = os.listdir("../../test_cycles/test_cycle_"+str(cycle_num))
iter_num = 0
for directory in iterations: 
	num = int(directory.split("iteration_")[-1])
	if num > iter_num:
		iter_num = num

# Get which faults are in the test cycle
faults = []
with open("../../test_cycles/test_cycle_"+str(cycle_num)+"/iteration_"\
		+str(iter_num) + "/faults.txt", "r") as f:
	for line in f:
		faults.append(line.strip())

# Determine whether this test failed due to the bugs implemented 
with open("../../data/output_data.csv", "r") as f:
	for i, line in enumerate(f):
		if i > 0:
			line = line.strip()
			tokens = line.split(",")
			f_num = tokens[0]
			tests = tokens[1:]
			if (f_num in faults):
				if (tests[int(test_num)] == "X"):
					print("FAILED")
					exit(0)

print("PASSED")


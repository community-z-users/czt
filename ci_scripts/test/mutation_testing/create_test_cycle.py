#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob

HOME_DIR=os.getcwd()

# Obtain command line arguments
if len(sys.argv) < 3:
	print("Usage: ./create_test_cycle.py NUM_FAULTS NUM_ITERATIONS")
	exit(1)
NUM_FAULTS = int(sys.argv[1])
ITERATIONS = int(sys.argv[2])


# Parse fault name lookup table
FAULT_TABLE = {}
with open("data/metadata/fault_lookup_table.csv", "r") as fault_table:
	for row in fault_table:
		num, name = row.strip().split(",")
		if not name == "":
			FAULT_TABLE[num] = name


# Parse test/fault data result table 
DATA_TABLE = {}
with open("data/output_data.csv", "r") as data_table:
	for row in data_table:
		unpacked_row = row.strip().split(",")
		fault_num = unpacked_row[0]
		failed_tests = unpacked_row[1:]
		DATA_TABLE[fault_num] = failed_tests


# Check NUM_FAULTS input is valid
MAX_FAULTS = len(list(DATA_TABLE.keys()))
if (NUM_FAULTS > MAX_FAULTS):
	print("NUM_FAULTS is too large, maximum is:",MAX_FAULTS)
	exit(1)


# Pick NUM_FAULTS random faults
FAULT_NUMS = []
for i in range(NUM_FAULTS):
	available_faults = list(DATA_TABLE.keys())
	num = randrange(0, len(available_faults))
	
	# Make sure you don't get the same fault twice
	while (available_faults[num] in FAULT_NUMS):
		num = randrange(0, len(available_faults))
	FAULT_NUMS.append(available_faults[num])


# Extract fault number 
for i, fault in enumerate(FAULT_NUMS):
	FAULT_NUMS[i] = fault.split("F")[-1]


# Link fault number with modified file
os.chdir("../../..")
CZT_HOME_DIR=os.getcwd()
modified_files = []
for num in FAULT_NUMS:
	mod_file = FAULT_TABLE[num]
	mod_file_path = glob.glob("**/" + mod_file, recursive=True)[0]
	modified_files.append(mod_file_path)

# Parse module based TCP test table file
# NOTE: This file describes which tests are executed from a module 
# MOD_TEST_DATA = {}
# with open("tcp_systems/mod_test_table.csv","r"):
# 	pass



# Get prioritization for each TCP system
command_line_args = ""
for path in modified_files:
	command_line_args += " " + path

os.system("./ci_scripts/test/mutation_testing/tcp_systems/module_tcp.py" + command_line_args)

os.system("./ci_scripts/test/mutation_testing/tcp_systems/tot_cov_tcp.py" + command_line_args)

os.system("./ci_scripts/test/mutation_testing/tcp_systems/add_cov_tcp.py" + command_line_args)





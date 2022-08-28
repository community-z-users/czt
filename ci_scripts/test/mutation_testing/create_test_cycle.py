#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob
import matplotlib.pyplot as plt

# Create test cycle function ===================================================
def create_test_cycle(NUM_FAULTS, CYCLE_NUM, ITERATION):
	HOME=os.getcwd()

	# Create iteration directory
	ITERATION_DIR = "test_cycles/test_cycle_"+str(CYCLE_NUM)+"/iteration_"+str(ITERATION)
	os.system("mkdir "+ITERATION_DIR) 

	# Parse fault name lookup table
	FAULT_TABLE = {}
	with open("data/metadata/fault_lookup_table.csv", "r") as fault_table:
		for row in fault_table:
			num, name = row.strip().split(",")
			if not name == "":
				FAULT_TABLE[num] = name 

	# Parse test name lookup table
	# NOTE: Format is { test_name: number, ... }
	TEST_TABLE = {}
	with open("data/metadata/test_lookup_table.csv", "r") as test_table:
		for row in test_table:
			num, name = row.strip().split(",")
			if not name == "":
				TEST_TABLE[name] = num 

	# Parse test/fault data result table 
	DATA_TABLE = {}
	with open("data/output_data.csv", "r") as data_table:
		for i, row in enumerate(data_table):
			if i > 0:
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
	available_faults = list(DATA_TABLE.keys())
	for i in range(NUM_FAULTS):
		num = randrange(0, len(available_faults))
		
		# Make sure you don't get the same fault twice
		while (available_faults[num] in FAULT_NUMS):
			num = randrange(0, len(available_faults))
		FAULT_NUMS.append(available_faults[num])

	with open(ITERATION_DIR+"/faults.txt", "w") as f:
		for fault in FAULT_NUMS:
			f.write(fault+"\n")

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
	MOD_TEST_DATA = {}
	with open("ci_scripts/test/mutation_testing/tcp_systems/module_test_table.csv","r") as f:
		for line in f:
			tokens = line.strip().split(",")
			mod_name = tokens[0]
			tests = tokens[1:]
			MOD_TEST_DATA[mod_name] = tests

	# Get prioritization for each TCP system
	command_line_args = ""
	for path in modified_files:
		command_line_args += " " + path

	mod_output_file = "ci_scripts/test/mutation_testing/"+ITERATION_DIR+"/mod_prior_raw.txt"
	os.system("./ci_scripts/test/mutation_testing/tcp_systems/module_tcp.py" \
			+ command_line_args + " >" + mod_output_file)

	tot_output_file = "ci_scripts/test/mutation_testing/"+ITERATION_DIR+"/tot_prior.txt"
	os.system("./ci_scripts/test/mutation_testing/tcp_systems/tot_cov_tcp.py" \
			+ command_line_args + " >" + tot_output_file)

	add_output_file = "ci_scripts/test/mutation_testing/"+ITERATION_DIR+"/add_prior.txt"
	os.system("./ci_scripts/test/mutation_testing/tcp_systems/add_cov_tcp.py" \
			+ command_line_args + " >" + add_output_file)

	comet_output_file = "ci_scripts/test/mutation_testing/"+ITERATION_DIR+"/comet_prior.txt"
	os.system("./ci_scripts/test/mutation_testing/tcp_systems/comet_tcp.py" \
			+ command_line_args + " >" + comet_output_file)

	# Reformat Module based TCP output
	mod_output_file_proc = "ci_scripts/test/mutation_testing/"+ITERATION_DIR+"/mod_prior.txt"
	with open(mod_output_file_proc, "w") as output_f:
		with open(mod_output_file, "r") as f:
			for module in f:
				module = module.strip()
				if module in MOD_TEST_DATA.keys():
					for test in MOD_TEST_DATA[module]:
						output_f.write(test + "\n")

	# Standardise test prioritisation with test numbers
	MOD_PRIOR = []
	with open(mod_output_file_proc,"r") as f:
		for line in f:
			line = line.strip()
			for test in TEST_TABLE.keys():
				if (line in test):
					MOD_PRIOR.append(TEST_TABLE[test])

	TOT_PRIOR = []
	with open(tot_output_file,"r") as f:
		for line in f:
			line = line.strip().replace('-', '.')
			if (line in TEST_TABLE.keys()):
				TOT_PRIOR.append(TEST_TABLE[line])

	ADD_PRIOR = []
	with open(add_output_file,"r") as f:
		for line in f:
			line = line.strip().split("net.sourceforge.")[-1]
			if (line in TEST_TABLE.keys()):
				ADD_PRIOR.append(TEST_TABLE[line])

	COMET_PRIOR = []
	with open(comet_output_file,"r") as f:
		for line in f:
			line = line.strip()
			if (line.startswith("czt.")):
				if (line in TEST_TABLE.keys()):
					COMET_PRIOR.append(TEST_TABLE[line])

	# Calculate APFD
	TSPE = [] # Test Suite Percentage of Execution
	for i in range(90):
		TSPE.append(int(100*((i+1)/90)))

	# Module TCP APFD
	MOD_FAULTS_DETECTED = []
	MOD_PFD = []
	for test in MOD_PRIOR:
		# Check if a fault was detected
		for fault in FAULT_NUMS:
			if not fault in MOD_FAULTS_DETECTED: # Check for only undetected faults
				# Check if this test detects this fault
				if(DATA_TABLE["F"+fault][int(test)] == "X"):
					# Add it to the detected faults list
					MOD_FAULTS_DETECTED.append(fault)

		# Update PFD score
		MOD_PFD.append(int(100*(len(MOD_FAULTS_DETECTED)/NUM_FAULTS)))

	# Total Coverage TCP APFD
	TOT_FAULTS_DETECTED = []
	TOT_PFD = []
	for test in TOT_PRIOR:
		# Check if a fault was detected
		for fault in FAULT_NUMS:
			if not fault in TOT_FAULTS_DETECTED: # Check for only undetected faults
				# Check if this test detects this fault
				if(DATA_TABLE["F"+fault][int(test)] == "X"):
					# Add it to the detected faults list
					TOT_FAULTS_DETECTED.append(fault)

		# Update PFD score
		TOT_PFD.append(int(100*(len(TOT_FAULTS_DETECTED)/NUM_FAULTS)))

	# Additional Coverage TCP APFD
	ADD_FAULTS_DETECTED = []
	ADD_PFD = []
	for test in ADD_PRIOR:
		# Check if a fault was detected
		for fault in FAULT_NUMS:
			if not fault in ADD_FAULTS_DETECTED: # Check for only undetected faults
				# Check if this test detects this fault
				if(DATA_TABLE["F"+fault][int(test)] == "X"):
					# Add it to the detected faults list
					ADD_FAULTS_DETECTED.append(fault)

		# Update PFD score
		ADD_PFD.append(int(100*(len(ADD_FAULTS_DETECTED)/NUM_FAULTS)))

	# Comet Coverage TCP APFD
	COMET_FAULTS_DETECTED = []
	COMET_PFD = []
	for test in COMET_PRIOR:
		# Check if a fault was detected
		for fault in FAULT_NUMS:
			if not fault in COMET_FAULTS_DETECTED: # Check for only undetected faults
				# Check if this test detects this fault
				if(DATA_TABLE["F"+fault][int(test)] == "X"):
					# Add it to the detected faults list
					COMET_FAULTS_DETECTED.append(fault)

		# Update PFD score
		COMET_PFD.append(int(100*(len(COMET_FAULTS_DETECTED)/NUM_FAULTS)))

	# Save output Data
	os.chdir(HOME)
	with open(ITERATION_DIR+"/output_data.csv", "w") as f:
		f.write("module_tcp\n")
		for i, data in enumerate(MOD_PFD):
			f.write(str(TSPE[i]) + "," + str(data) + "\n")
		f.write("\n")

		f.write("tot_coverage_tcp\n")
		for i, data in enumerate(TOT_PFD):
			f.write(str(TSPE[i]) + "," + str(data) + "\n")
		f.write("\n")

		f.write("add_coverage_tcp\n")
		for i, data in enumerate(ADD_PFD):
			f.write(str(TSPE[i]) + "," + str(data) + "\n")
		f.write("\n")

		f.write("comet_coverage_tcp\n")
		for i, data in enumerate(COMET_PFD):
			f.write(str(TSPE[i]) + "," + str(data) + "\n")
		f.write("\n")


# Main script =================================================================
HOME_DIR=os.getcwd()

# Determine Cycle Number
test_cycles = os.listdir("test_cycles")
last_cycle = 0
for directory in test_cycles: 
	num = int(directory.split("test_cycle_")[-1])
	if num > last_cycle:
		last_cycle = num
CYCLE_NUM = last_cycle + 1
print("Creating Test Cycle", CYCLE_NUM)

# Create new folder for test output
os.system("mkdir -p test_cycles/test_cycle_"+str(CYCLE_NUM))

# Obtain command line arguments
if len(sys.argv) < 3:
	print("Usage: ./create_test_cycle.py NUM_FAULTS NUM_ITERATIONS")
	exit(1)
NUM_FAULTS = int(sys.argv[1])
ITERATIONS = int(sys.argv[2])

# Perform experiments
for i in range(ITERATIONS):
	print("Running Iteration:", i+1, "\t",str(int(100*(i/ITERATIONS))) + "%")
	create_test_cycle(NUM_FAULTS, CYCLE_NUM, i+1)

# REMOVE AFTER TESTING IS COMPLETE
# os.system("rm -r  /home/samuelv/czt/ci_scripts/test/mutation_testing/test_cycles/test_cycle_2")


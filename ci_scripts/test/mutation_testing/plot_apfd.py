#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob
import matplotlib.pyplot as plt

# Global variables
BLOCKLIST_TESTS = ['43','44','47','48','50','51','53','54','56','66','74','75','80','81','83','85','86','89']
#BLOCKLIST_TESTS = []
NUM_TESTS = 90 - len(BLOCKLIST_TESTS)

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


# Get test cycle to plot
CYCLE_NUM = sys.argv[1]


# Get iterations
ITERATION_DIRS = os.listdir("test_cycles/test_cycle_"+CYCLE_NUM)
ITERATION_DIRS_PATH = []
for ITERATION_DIR in ITERATION_DIRS:
	ITERATION_DIRS_PATH.append("test_cycles/test_cycle_"+CYCLE_NUM+"/"+ITERATION_DIR)

MOD_APFD = []
TOT_APFD = []
ADD_APFD = []
COMET_APFD = []
for ITERATION_DIR in ITERATION_DIRS_PATH:

	FAULT_NUMS = []
	with open(ITERATION_DIR+"/faults.txt","r") as f:
		for line in f:
			FAULT_NUMS.append(line.strip())

	NUM_FAULTS=len(FAULT_NUMS)
	#print("Introduced",NUM_FAULTS,"faults:",FAULT_NUMS)
	 
	mod_output_file_proc = ITERATION_DIR+"/mod_prior.txt"

	tot_output_file = ITERATION_DIR+"/tot_prior.txt"

	add_output_file = ITERATION_DIR+"/add_prior.txt"

	comet_output_file = ITERATION_DIR+"/comet_prior.txt"

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


	# Module TCP APFD Graph
	MOD_FAULTS_DETECTED = []
	MOD_PFD = []
	i = 0
	for test in MOD_PRIOR:
		test_num = str(int(test)+1) # change from zero index
		if not test_num in BLOCKLIST_TESTS:
			i += 1
			# Check if a fault was detected
			for fault in FAULT_NUMS:
				if not fault in MOD_FAULTS_DETECTED: # Check for only undetected faults
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						# Add it to the detected faults list
						MOD_FAULTS_DETECTED.append(fault)

						# Update PFD score
						MOD_PFD.append(i)
	
	# Total Coverage TCP APFD Graph
	TOT_FAULTS_DETECTED = []
	TOT_PFD = []
	i = 0
	for test in TOT_PRIOR:
		test_num = str(int(test)+1) # change from zero index
		if not test_num in BLOCKLIST_TESTS:
			i += 1
			# Check if a fault was detected
			for fault in FAULT_NUMS:
				if not fault in TOT_FAULTS_DETECTED: # Check for only undetected faults
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						# Add it to the detected faults list
						TOT_FAULTS_DETECTED.append(fault)

						# Update PFD score
						TOT_PFD.append(i)

	# Additional Coverage TCP APFD Graph
	ADD_FAULTS_DETECTED = []
	ADD_PFD = []
	i = 0
	for i,test in enumerate(ADD_PRIOR):
		test_num = str(int(test)+1) # change from zero index
		if not test_num in BLOCKLIST_TESTS:
			i += 1
			# Check if a fault was detected
			for fault in FAULT_NUMS:
				if not fault in ADD_FAULTS_DETECTED: # Check for only undetected faults
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						# Add it to the detected faults list
						ADD_FAULTS_DETECTED.append(fault)

						# Update PFD score
						ADD_PFD.append(i)

	# Comet Coverage TCP APFD Graph
	COMET_FAULTS_DETECTED = []
	COMET_PFD = []
	i = 0
	for i,test in enumerate(COMET_PRIOR):
		test_num = str(int(test)+1) # change from zero index
		if not test_num in BLOCKLIST_TESTS:
			i += 1
			# Check if a fault was detected
			for fault in FAULT_NUMS:
				if not fault in COMET_FAULTS_DETECTED: # Check for only undetected faults
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						# Add it to the detected faults list
						COMET_FAULTS_DETECTED.append(fault)

						# Update PFD score
						COMET_PFD.append(i)


	assert len(MOD_PFD) == NUM_FAULTS, 'Error in Module TCP '+"ITERATION:"+ITERATION_DIR+" "+str(len(MOD_PFD))+" != "+str(NUM_FAULTS)
	assert len(TOT_PFD) == NUM_FAULTS, 'Error in Total Coverage TCP'+"ITERATION:"+ITERATION_DIR+" "+str(len(TOT_PFD))+" != "+str(NUM_FAULTS)
	assert len(ADD_PFD) == NUM_FAULTS, 'Error in Additional Coverage TCP'+"ITERATION:"+ITERATION_DIR+" "+str(len(ADD_PFD))+" != "+str(NUM_FAULTS)
	assert len(COMET_PFD) == NUM_FAULTS, 'Error in Comet TCP'+"ITERATION:"+ITERATION_DIR+ITERATION_DIR+" "+str(len(COMET_PFD))+" != "+str(NUM_FAULTS)


	MOD_APFD.append(1 - (sum(MOD_PFD))/(NUM_FAULTS*NUM_TESTS) - 1/(2*NUM_TESTS))
	TOT_APFD.append(1 - (sum(TOT_PFD))/(NUM_FAULTS*NUM_TESTS) - 1/(2*NUM_TESTS))
	ADD_APFD.append(1 - (sum(ADD_PFD))/(NUM_FAULTS*NUM_TESTS) - 1/(2*NUM_TESTS))
	COMET_APFD.append(1 - (sum(COMET_PFD))/(NUM_FAULTS*NUM_TESTS) - 1/(2*NUM_TESTS))

AV_MOD_APFD = sum(MOD_APFD)/len(MOD_APFD)
AV_TOT_APFD = sum(TOT_APFD)/len(TOT_APFD)
AV_ADD_APFD = sum(ADD_APFD)/len(ADD_APFD)
AV_COMET_APFD = sum(COMET_APFD)/len(COMET_APFD)
print("Module:\t\t\t", AV_MOD_APFD)
print("Total Coverage:\t\t",AV_TOT_APFD)
print("Additional Coverage:\t",AV_ADD_APFD)
print("Comet:\t\t\t",AV_COMET_APFD)

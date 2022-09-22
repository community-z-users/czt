#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob
import matplotlib.pyplot as plt
from statistics import median, mean

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

# Parse TTF metadata file
TEST_DURATIONS = {}
with open("data/metadata/ttf_data.txt", "r") as f:
	for line in f:
		test_name, duration = line.strip().split(' ')
		TEST_DURATIONS[test_name] = float(duration)

# Get test cycle to plot
CYCLE_NUM = sys.argv[1]

# Get iterations
ITERATION_DIRS = os.listdir("test_cycles/test_cycle_"+CYCLE_NUM)
ITERATION_DIRS_PATH = []
for ITERATION_DIR in ITERATION_DIRS:
	ITERATION_DIRS_PATH.append("test_cycles/test_cycle_"+CYCLE_NUM+"/"+ITERATION_DIR)


# Generate X axis for plots (percentage of tests executed)
TSPE = [] # Test Suite Percentage of Execution
for i in range(NUM_TESTS):
    TSPE.append(int(100*((i+1)/NUM_TESTS)))


MOD_TTF = []
TOT_TTF = []
ADD_TTF = []
COMET_TTF = []
MOD_NTF = []
TOT_NTF = []
ADD_NTF = []
COMET_NTF = []
for ITERATION_DIR in ITERATION_DIRS_PATH:

	FAULT_NUMS = []
	with open(ITERATION_DIR+"/faults.txt","r") as f:
		for line in f:
			FAULT_NUMS.append(line.strip())

	NUM_FAULTS=len(FAULT_NUMS)
	 
	mod_output_file_proc = ITERATION_DIR+"/mod_prior.txt"

	tot_output_file = ITERATION_DIR+"/tot_prior.txt"

	add_output_file = ITERATION_DIR+"/add_prior.txt"

	comet_output_file = ITERATION_DIR+"/comet_prior.txt"

	# Standardise test prioritisation with test numbers
	MOD_PRIOR = []
	MOD_PRIOR_NAMES = []
	with open(mod_output_file_proc,"r") as f:
		for line in f:
			line = line.strip()
			for test in TEST_TABLE.keys():
				if (line in test):
					MOD_PRIOR.append(TEST_TABLE[test])
					MOD_PRIOR_NAMES.append(test)
	
	TOT_PRIOR = []
	TOT_PRIOR_NAMES = []
	with open(tot_output_file,"r") as f:
		for line in f:
			line = line.strip().replace('-', '.')
			if (line in TEST_TABLE.keys()):
				TOT_PRIOR.append(TEST_TABLE[line])
				TOT_PRIOR_NAMES.append(line)

	ADD_PRIOR = []
	ADD_PRIOR_NAMES = []
	with open(add_output_file,"r") as f:
		for line in f:
			line = line.strip().split("net.sourceforge.")[-1]
			if (line in TEST_TABLE.keys()):
				ADD_PRIOR.append(TEST_TABLE[line])
				ADD_PRIOR_NAMES.append(line)

	COMET_PRIOR = []
	COMET_PRIOR_NAMES = []
	with open(comet_output_file,"r") as f:
		for line in f:
			line = line.strip()
			if (line.startswith("czt.")):
				if (line in TEST_TABLE.keys()):
					COMET_PRIOR.append(TEST_TABLE[line])
					COMET_PRIOR_NAMES.append(line)


	# Module TCP APFD Graph
	MOD_PASSED_TESTS = []
	found = False
	for i,test in enumerate(MOD_PRIOR):
		test_num = str(int(test)+1) # change from zero index
		if not found:
			if not test_num in BLOCKLIST_TESTS:
				# Check if a fault was detected
				for fault in FAULT_NUMS:
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						found = True
						break
				MOD_PASSED_TESTS.append(TEST_DURATIONS[MOD_PRIOR_NAMES[i]])
		else:
			break
	MOD_TTF.append(sum(MOD_PASSED_TESTS))
	MOD_NTF.append(len(MOD_PASSED_TESTS))
	
	# Total Coverage TCP APFD Graph
	TOT_PASSED_TESTS = []
	found = False
	for test in TOT_PRIOR:
		if not found:
			test_num = str(int(test)+1) # change from zero index
			if not test_num in BLOCKLIST_TESTS:
				# Check if a fault was detected
				for fault in FAULT_NUMS:
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						found = True
						break
				TOT_PASSED_TESTS.append(TEST_DURATIONS[TOT_PRIOR_NAMES[i]])
		else:
			break
	TOT_TTF.append(sum(TOT_PASSED_TESTS))
	TOT_NTF.append(len(TOT_PASSED_TESTS))

	# Additional Coverage TCP APFD Graph
	ADD_PASSED_TESTS = []
	found = False
	for i,test in enumerate(ADD_PRIOR):
		if not found:
			test_num = str(int(test)+1) # change from zero index
			if not test_num in BLOCKLIST_TESTS:
				# Check if a fault was detected
				for fault in FAULT_NUMS:
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						found = True
						break
				ADD_PASSED_TESTS.append(TEST_DURATIONS[ADD_PRIOR_NAMES[i]])
		else:
			break
	ADD_TTF.append(sum(ADD_PASSED_TESTS))
	ADD_NTF.append(len(ADD_PASSED_TESTS))

	# Comet Coverage TCP APFD Graph
	COMET_PASSED_TESTS = []
	found = False
	for i,test in enumerate(COMET_PRIOR):
		if not found:
			test_num = str(int(test)+1) # change from zero index
			if not test_num in BLOCKLIST_TESTS:
				# Check if a fault was detected
				for fault in FAULT_NUMS:
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						found = True
						break
				# no fault was detected, add passed test to list
				COMET_PASSED_TESTS.append(TEST_DURATIONS[COMET_PRIOR_NAMES[i]])
		else:
			break
	COMET_TTF.append(sum(COMET_PASSED_TESTS))
	COMET_NTF.append(len(COMET_PASSED_TESTS))


AV_MOD_TTF = mean(MOD_TTF)
AV_TOT_TTF = mean(TOT_TTF)
AV_ADD_TTF = mean(ADD_TTF)
AV_COMET_TTF = mean(COMET_TTF)
print("Mean of TTF")
print("Module:\t\t\t", AV_MOD_TTF)
print("Total Coverage:\t\t",AV_TOT_TTF)
print("Additional Coverage:\t",AV_ADD_TTF)
print("Comet:\t\t\t",AV_COMET_TTF)


MED_MOD_TTF = median(MOD_TTF)
MED_TOT_TTF = median(TOT_TTF)
MED_ADD_TTF = median(ADD_TTF)
MED_COMET_TTF = median(COMET_TTF)
print("\nMedian of TTF")
print("Module:\t\t\t", MED_MOD_TTF)
print("Total Coverage:\t\t",MED_TOT_TTF)
print("Additional Coverage:\t",MED_ADD_TTF)
print("Comet:\t\t\t",MED_COMET_TTF)

RE_MOD_TTF = mean(MOD_TTF) * 1.36
RE_TOT_TTF = mean(TOT_TTF) * 3.21
RE_ADD_TTF = mean(ADD_TTF) * 3.24
RE_COMET_TTF = mean(COMET_TTF) * 3.58
print("\nReal scaled mean of TTF")
print("Module:\t\t\t", RE_MOD_TTF)
print("Total Coverage:\t\t",RE_TOT_TTF)
print("Additional Coverage:\t",RE_ADD_TTF)
print("Comet:\t\t\t",RE_COMET_TTF)

MED_MOD_NTF = mean(MOD_NTF)
MED_TOT_NTF = mean(TOT_NTF)
MED_ADD_NTF = mean(ADD_NTF)
MED_COMET_NTF = mean(COMET_NTF)
print("\nAverage number of tests before failure")
print("Module:\t\t\t", MED_MOD_NTF)
print("Total Coverage:\t\t",MED_TOT_NTF)
print("Additional Coverage:\t",MED_ADD_NTF)
print("Comet:\t\t\t",MED_COMET_NTF)


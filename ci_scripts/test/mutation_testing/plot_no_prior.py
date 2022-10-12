#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob
import matplotlib.pyplot as plt
from statistics import median

# Global variables
#BLOCKLIST_TESTS = ['43','44','47','48','50','51','53','54','56','66','74','75','80','81','83','85','86','89']
BLOCKLIST_TESTS = []
NUM_TESTS = 90 - len(BLOCKLIST_TESTS)


BLOCKLIST_TESTS = [
		"czt.vcg",
		"czt.circus",
		"czt.circuspatt",
		"czt.circustime",
		"czt.circusconf",
		"czt.parser.ozpatt",
		"czt.typecheck.circus",
		"czt.typecheck.oz",
		"czt.typecheck.zeves",
		"czt.z.impl.AstTest",
		"czt.print.circus.PrintTest",
		"czt.parser.circus.ParserTest",
		"czt.parser.circus.ParserFailTest",
		"czt.parser.circus.CyclicParentParserTest",
		"czt.parser.zeves.ProofScriptParsingTest",
		"czt.parser.zeves.ScanningTest",
		"czt.parser.zeves.CyclicParentParserTest",
		"czt.parser.zpatt.CyclicParentParserTest",
		"czt.parser.oz.ParserTest",
		"czt.parser.oz.LatexToUnicodeTest",
		"czt.parser.oz.CyclicParentParserTest",
		"czt.typecheck.z.TypeCheckerTest",
		"czt.print.circustime.PrintTest",
		"czt.parser.circusconf.ParserTest",
		"czt.parser.circusconf.ParserFailTest",
		"czt.parser.circusconf.CyclicParentParserTest",
		"czt.rules.TypeCheckRewriteTest",
		"czt.rules.rewriter.InnermostTest",
		"czt.zeves.CZT2ZEvesPrintingTest",
		"czt.print.circusconf.PrintTest",
		"czt.parser.circustime.ParserTest",
		"czt.parser.circustime.ParserFailTest",
		"czt.parser.circustime.CyclicParentParserTest",
		]

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


# Generate X axis for plots (percentage of tests executed)
TSPE = [] # Test Suite Percentage of Execution
for i in range(NUM_TESTS):
    TSPE.append(int(100*((i+1)/NUM_TESTS)))

# Get no prioritisation order
no_prior_list = []
with open("trimmed_test.txt", 'r') as f:
	for line in f:
		line = line.strip()
		test = line.split("- in ")[-1]
		block = False
		for t in BLOCKLIST_TESTS:
			if t in test:
				block = True

		if not block:
			no_prior_list.append(test.strip())


APFD = []
for ITERATION_DIR in ITERATION_DIRS_PATH:

	FAULT_NUMS = []
	with open(ITERATION_DIR+"/faults.txt","r") as f:
		for line in f:
			FAULT_NUMS.append(line.strip())

	NUM_FAULTS=len(FAULT_NUMS)
	#print("Introduced",NUM_FAULTS,"faults:",FAULT_NUMS)

	# Standardise test prioritisation with test numbers
	PRIOR = []
	for t in no_prior_list:
		for test in TEST_TABLE.keys():
			if (test in t):
				PRIOR.append(TEST_TABLE[test])
	
	# Module TCP APFD Graph
	FAULTS_DETECTED = []
	PFD = []
	FAULT_INDEX = []
	i = 0
	for test in PRIOR:
		test_num = str(int(test)+1) # change from zero index
		if not test_num in BLOCKLIST_TESTS:
			i += 1
			# Check if a fault was detected
			for fault in FAULT_NUMS:
				if not fault in FAULTS_DETECTED: # Check for only undetected faults
					# Check if this test detects this fault
					if(DATA_TABLE[fault][int(test)] == "X"):
						# Add it to the detected faults list
						FAULTS_DETECTED.append(fault)

						# Update PFD score
						FAULT_INDEX.append(i)
			PFD.append(int(100*(len(FAULTS_DETECTED)/NUM_FAULTS)))	

	# Plot Module coverage data
	plt.plot(TSPE,PFD)

	assert len(FAULT_INDEX) == NUM_FAULTS, 'Error in Module TCP '+"ITERATION:"+\
			ITERATION_DIR+" "+str(len(FAULT_INDEX))+" != "+str(NUM_FAULTS)

	APFD.append(1 - (sum(FAULT_INDEX))/(NUM_FAULTS*NUM_TESTS) - 1/(2*NUM_TESTS))

# Mean
AV_APFD = sum(APFD)/len(APFD)
print("Mean APFD\t", AV_APFD)

print()

# Median
AV_APFD = median(APFD)
print("Median APFD\t", AV_APFD)


# Show plots
plt.xlim((-5,110))
plt.ylim((-5,110))
plt.title("No Prioritisation")
plt.show()



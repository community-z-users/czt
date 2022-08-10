#!/usr/bin/env python3

import glob
import random
import os


def flip_logic():
	return random.randint(0,1) == 0

# Collect source files that are covered by tests
SRC_FILES = []
with open("ci_scripts/test/coverage/additional/additional_coverage_data.txt", "r") as f:
	for line in f:
		path = line.split(',')[0]
		path += ".java"
		SRC_FILES.append(path)

SRC_FILES = list(set(SRC_FILES))

for file_no,f in enumerate(SRC_FILES):
	
	# src_file = glob.glob("**/" + f, recursive=True)[0]
	# name = src_file.split('/')[-1].split(".java")[0]
	# copy_file = "ci_scripts/test/mutation_testing/patches/" + str(file_no) + "_" + "patch_" + name
	# os.system("cp " + src_file + " " + copy_file)

	print(src_file)
	print(copy_file)
	with open(copy_file, "r") as current_file:
		for i, line in enumerate(current_file):
			if ("==" in line):
				print("\tToken '==' found on line", i)
			elif (">" in line):
				print("\tToken '>' found on line", i)
			elif (">=" in line):
				print("\tToken '>=' found on line", i)
			elif ("<" in line):
				print("\tToken '<' found on line", i)
			elif ("<=" in line):
				print("\tToken '<=' found on line", i)

	print()
	exit()




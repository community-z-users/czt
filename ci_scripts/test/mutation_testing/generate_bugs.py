#!/usr/bin/env python3

import glob
import random
import os
import fileinput

def modify_file():
	return random.randint(0,19) == 0

# Collect source files that are covered by tests
SRC_FILES = []
with open("ci_scripts/test/coverage/additional/additional_coverage_data.txt", "r") as f:
	for line in f:
		path = line.split(',')[0]
		path += ".java"
		SRC_FILES.append(path)

SRC_FILES = list(set(SRC_FILES))

for file_no,f in enumerate(SRC_FILES):
	
	if modify_file():
		src_file = glob.glob("**/" + f, recursive=True)[0]
		name = src_file.split('/')[-1].split(".java")[0]

		with fileinput.input(src_file, inplace=True) as f:
			for line in f:
				print(line.replace(" == ", " != "), end="")


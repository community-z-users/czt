#!/usr/bin/env python3

import glob
import random
import os
import fileinput

def flip_logic():
	return random.randint(0,1) == 0

def modify_file():
	return random.randint(0,9) == 0

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
		# os.system("cp " + src_file + " tmp.txt")



		with fileinput.input(src_file, inplace=True) as f:
			for line in f:
				print(line.replace(" == ", " != "), end="")


		# print(src_file)
		# with open(src_file, "w") as current_file:
		# 	for i, line in enumerate(current_file):
		# 		if (" == " in line):
		# 			line.replace(" == ", " != ")
		# 			# print("\tToken '==' found on line", i)
		# 		# elif (" != " in line):
		# 		# 	print("\tToken '!=' found on line", i)
		# 		# elif (" > " in line):
		# 		# 	print("\tToken '>' found on line", i)
		# 		# elif (" >= " in line):
		# 		# 	print("\tToken '>=' found on line", i)
		# 		# elif (" < " in line):
		# 		# 	print("\tToken '<' found on line", i)
		# 		# elif (" <= " in line):
		# 	# 		print("\tToken '<=' found on line", i)
		# 
		# # os.system("tmp.txt > " + src_file)
		# # os.system("rm tmp.txt")
		exit()





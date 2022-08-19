#!/usr/bin/env python3

import glob
import random
import os
import fileinput

"""
for each source file:
	- make a copy file in mutation_testing/patches/src
	- make changes to the copy
	- create a patch file in mutation_testing/patches/
"""

# Collect source files that are covered by tests
SRC_FILES = []
with open("ci_scripts/test/coverage/additional/additional_coverage_data.txt", "r") as f:
	for line in f:
		path = line.split(',')[0]
		path += ".java"
		SRC_FILES.append(path)

SRC_FILES = list(set(SRC_FILES))

for file_no,f in enumerate(SRC_FILES):

	# Create copy of source file
	src_file = glob.glob("**/" + f, recursive=True)[0]
	name = src_file.split(".java")[0].replace("/","_")
	name_path = "ci_scripts/test/mutation_testing/patches/"+name
	os.system("touch " + name_path + ".txt")
	os.system("cp " + src_file + " " + name_path+".txt")

	# Make changes to the copy
	line_number = -1
	with open(name_path+".txt", "r") as source:
		for i, line in enumerate(source):
			if(" < " in line):
				line_number = i
				break
			elif(" <= " in line):
				line_number = i
				break
			elif(" > " in line):
				line_number = i
				break
			elif(" >= " in line):
				line_number = i
				break
			elif(" != " in line):
				line_number = i
				break
			elif(" == " in line):
				line_number = i
				break

	with fileinput.input(name_path+".txt", inplace=True) as f:
		for i, line in enumerate(f):
			if (i == line_number):
				if(" < " in line):
					print(line.replace(" < ", " > "), end="")
				elif(" <= " in line):
					print(line.replace(" <= ", " >= "), end="")
				elif(" > " in line):
					print(line.replace(" > ", " < "), end="")
				elif(" >= " in line):
					print(line.replace(" >= ", " < "), end="")
				elif(" != " in line):
					print(line.replace(" != ", " == "), end="")
				elif(" == " in line):
					print(line.replace(" == ", " != "), end="")
			else:
				print(line, end="")

	# Create a patch file
	os.system("diff -u " + src_file + " " + name_path+".txt" + " > " + name_path + ".patch")
	

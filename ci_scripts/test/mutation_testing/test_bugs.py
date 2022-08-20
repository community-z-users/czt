#!/usr/bin/env python3
"""
	Run this from ci_scripts/test/mutation_testing
"""

import time
import os

BRANCHES = [9]

def delete_branches():
	for i in BRANCHES:
		os.system("git push origin --delete dev/test-bug-"+str(i))
		os.system("git branch -D dev/test-bug-"+str(i))


def get_ftp(filename):
	string = ""
	with open("patches/"+filename, "r") as f:
		for i,line in enumerate(f):
			if i == 0:
				string = line.split('--- ')[1]
	return string.split("\t")[0]


patch_files = []
files = os.listdir("patches")
for f in files:
	if f.endswith(".patch"):
		patch_files.append(f)

delete_branches()

START_DIR = os.getcwd()
for i, f in enumerate(patch_files):

	if (i in BRANCHES):
		time.sleep(1)
		# 1) Create new branch
		os.system("git checkout -b dev/test-bug-"+str(i))

		# 2) Apply patch
		file_to_patch = get_ftp(f)
		os.chdir("../../..")
		print(os.getcwd())
		print("PATCH FILE:", f)
		print("PATCHING:",file_to_patch)
		os.system("patch " + file_to_patch \
				+ " < ci_scripts/test/mutation_testing/patches/" + f)

		# 3) Commit
		os.system('git add -u; git commit -m "Testing bug in '+file_to_patch+'"')
		os.system('git push -u origin dev/test-bug-'+str(i))
		os.system('hub pull-request -m "'+"test-bug-"+str(i)+'"')

		# 4) Return to starting dir and checkout previous branch
		os.system("git checkout dev/czt-devops")
		os.chdir(START_DIR)

# delete_branches()


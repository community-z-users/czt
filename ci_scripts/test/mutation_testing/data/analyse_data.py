#!/usr/bin/env python3

import os


files = os.listdir()
top_line = " "
for i in range(90):
	top_line += ",T"+str(i+1)
top_line = top_line + "\n"

body_lines = []
for f in files:
	if f.endswith(".txt"):
		fault_no = f.split("test_")[1].split(".txt")[0]
		data=open(f, "r").readlines()
		data.sort() # Sort lines into alphabetical order
		if (len(data) == 90):
			line = "F"+fault_no
			for x in data:
				if ("PASSED" in x):
					line += ","
				else:
					line += ",X"

			body_lines.append(line+"\n")

body_lines = sorted(body_lines, key=lambda x: int(x.split(',')[0].split('F')[-1]))

with open("output_data.csv", "w") as f:
	f.write(top_line)
	for line in body_lines:
		f.write(line)


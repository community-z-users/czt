#!/usr/bin/env python3

import os
import sys
from random import randrange
import glob
import matplotlib.pyplot as plt

# Global variables
NUM_TESTS = 90

# Get test cycle to plot
CYCLE_NUM = sys.argv[1]

# Get iterations
ITERATION_DIRS = os.listdir("test_cycles/test_cycle_"+CYCLE_NUM)

module_tcp_data = {}
total_tcp_data = {}
additional_tcp_data = {}
comet_tcp_data = {}
for i in ITERATION_DIRS:
	with open("test_cycles/test_cycle_"+CYCLE_NUM+"/"+i+"/output_data.csv", "r") as f:
		# Init graphs
		module_tcp_data[i] = []
		total_tcp_data[i] = []
		additional_tcp_data[i] = []
		comet_tcp_data[i] = []

		current_graph = ""
		for line in f:
			line = line.strip()
			if line == "":
				continue
			elif not ("," in line):
				current_graph = line
			else:
				# Reading data
				if (current_graph == "module_tcp"):
					module_tcp_data[i].append(int(line.split(",")[-1]))
				elif (current_graph == "tot_coverage_tcp"):
					total_tcp_data[i].append(int(line.split(",")[-1]))
				elif (current_graph == "add_coverage_tcp"):
					additional_tcp_data[i].append(int(line.split(",")[-1]))
				elif (current_graph == "comet_coverage_tcp"):
					comet_tcp_data[i].append(int(line.split(",")[-1]))
				


TSPE = [] # Test Suite Percentage of Execution
for i in range(NUM_TESTS):
	TSPE.append(int(100*((i+1)/90)))

# Plot module data
plt.subplot(141)
plt.xlim((-5,110))
plt.ylim((-5,110))
plt.title("Module Based TCP")
for i in module_tcp_data:
	plt.plot(TSPE, module_tcp_data[i])

# Plot total coverage data
plt.subplot(142)
plt.xlim((-5,110))
plt.ylim((-5,110))
plt.title("Total Coverage Based TCP")
for i in total_tcp_data:
	plt.plot(TSPE, total_tcp_data[i])

# Plot Additional coverage data
plt.subplot(143)
plt.xlim((-5,110))
plt.ylim((-5,110))
plt.title("Additional Coverage Based TCP")
for i in additional_tcp_data:
	plt.plot(TSPE, additional_tcp_data[i])

# Plot Comet coverage data
plt.subplot(144)
plt.xlim((-5,110))
plt.ylim((-5,110))
plt.title("Comet Coverage Based TCP")
for i in comet_tcp_data:
	plt.plot(TSPE, comet_tcp_data[i])

plt.show()


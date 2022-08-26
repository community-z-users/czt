#!/usr/bin/env python3

import sys
import os


cmds = ""
for arg in sys.argv[1:]:
	cmds += " " + arg

os.chdir("ci_scripts/test/mutation_testing/tcp_systems/comet")
os.system("mvn clean install")
os.system('mvn exec:java -Dexec.mainClass="comet.CometJavaClient" -Dexec.args="'+cmds+'"')

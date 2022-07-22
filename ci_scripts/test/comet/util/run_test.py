#!/usr/bin/env python3

import sys
import os

# Go back up to home dir
os.chdir("../../..")

os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + str(sys.argv[1]))

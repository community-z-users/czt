#!/usr/bin/env python3

import sys
import os

# Go back up to home dir
os.chdir("../../..")

err = os.system("mvn surefire:test -DfailIfNoTests=false -Dtest=" + str(sys.argv[1]))

if err:
    exit(1)

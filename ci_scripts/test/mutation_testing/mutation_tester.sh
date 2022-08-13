#!/bin/sh

# Clean working environment
git reset --hard origin/dev/czt-devops

# Introduce bugs
./ci_scripts/test/mutation_testing/generate_bugs.py

# Show modified files
echo "==========================================================================="
echo "Modified:"
git diff --name-only HEAD .
echo "==========================================================================="


# Build CZT Project
echo "==========================================================================="
echo "Building CZT Project"
./ci_scripts/build/build_czt.sh > /dev/null
if [ `echo $?` == 0 ]
then
	echo "Build Failed"
fi
echo "==========================================================================="

# Run Total Coverage TCP System
echo "==========================================================================="
./ci_scripts/test/coverage/total/run_tests.py | tee ci_scripts/test/mutation_testing/results/tcp_tot_coverage.txt
echo "==========================================================================="

# Run Additional Coverage TCP System
echo "==========================================================================="
./ci_scripts/test/coverage/additional/run_tests_additional.py | tee ci_scripts/test/mutation_testing/results/additional.txt
echo "==========================================================================="

# Clean up 
git reset --hard origin/dev/czt-devops

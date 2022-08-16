#!/bin/bash

# Create new branch
git checkout -b dev/mut-testing-8
 
./ci_scripts/test/mutation_testing/generate_bugs.py
git add -u; git status
git commit -m "Mutation testing round 8"
git push -u origin dev/mut-testing-8

echo "Press any key to continue"
while [ true ]
do
	read -t 3 -n 1
	if [ $? = 0 ]
	then
		exit
	fi
done

# Create ADD_COVERAGE commit
sed -i 's/TCP_SYSTEM: \"TOT_COVERAGE\"/TCP_SYSTEM: \"ADD_COVERAGE\"/' .github/workflows/CI.yml
git add -u
git commit --amend
git push -u origin dev/mut-testing-8 -f

# Create MODULE commit
sed -i 's/TCP_SYSTEM: \"ADD_COVERAGE\"/TCP_SYSTEM: \"MODULE\"/' .github/workflows/CI.yml
git add -u
git commit --amend
git push -u origin dev/mut-testing-8 -f

# Create COMET commit
sed -i 's/TCP_SYSTEM: \"MODULE\"/TCP_SYSTEM: \"COMET\"/' .github/workflows/CI.yml
git add -u
git commit --amend
git push -u origin dev/mut-testing-8 -f




# checkout dev/czt-devops
# 
# # Delete changes
# git push origin --delete dev/mut-testing-8 
# git branch -D dev/mut-testing-8

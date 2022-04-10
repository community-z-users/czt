#!/usr/bin/env bash
set -e

HOME=$(pwd)

# Set Up Function
function set_up {
  # clear files used before
  cd $HOME
  > ci_scripts/text_files/top_level_dirs.txt
  > ci_scripts/text_files/modules_to_test.txt
  > ci_scripts/text_files/dependencies.txt
  > ci_scripts/text_files/tmp.txt
}

# Clean Up Function
function clean_up {
  cd $HOME
  rm ci_scripts/text_files/top_level_dirs.txt
  rm ci_scripts/text_files/modules_to_test.txt
  rm ci_scripts/text_files/dependencies.txt
  rm ci_scripts/text_files/tmp.txt
}

set_up

# Get the files that have been modified in the last commit
# git diff --name-only HEAD HEAD~1 > ci_scripts/text_files/changed_files.txt

# Loop through modified files and find the directories they are in 
cat ci_scripts/text_files/changed_files.txt | while read line
do
  echo `dirname $line` >> ci_scripts/text_files/top_level_dirs.txt
done

# Find module (e.g. keep going up until you find pom.xml)
cat ci_scripts/text_files/top_level_dirs.txt | sort -u | while read line
do
  cd `echo $(pwd)/$line` 
  while [ `ls | grep pom.xml | wc -l` == 0 ]
  do
    cd ..
  done
  # Now we are in a module that can be tested
  echo $(pwd) >> $HOME/ci_scripts/text_files/modules_to_test.txt
  cd $HOME
done

# Go back to base dir before proceeding
cd $HOME

# Run test modules in the directories that contain modified code
echo "==============================================================================="
echo "========================== TESTING MODIFIED MODULES ==========================="
echo "==============================================================================="
cat ci_scripts/text_files/modules_to_test.txt | sort -u | while read line
do
  # Test the module
  BASENAME=`basename $line`

  #echo "|====>" $BASENAME
  #cd $line
  #mvn surefire:test | tee $HOME/ci_scripts/text_files/tmp.txt
  #TEST_RESULT=`cat $HOME/ci_scripts/text_files/tmp.txt | grep "BUILD SUCCESS" | wc -l`
  #if [ $TEST_RESULT == 0 ]; then
  #  # Exit after test failure
  #  clean_up
  #  exit 1
  #fi

  # Find dependencies
  echo "|====>" Fetching Dependencies of `basename $line`
  # mvn dependency:tree | tee $HOME/ci_scripts/text_files/tmp.txt > /dev/null
  # cut -d "]" -f2- <<< `mvn dependency:tree | grep + | grep net.sourceforge.czt`
  # cut -d ":" -f2 <<< `cat $HOME/ci_scripts/text_files/tmp.txt | grep + | grep net.sourceforge.czt` >> $HOME/ci_scripts/text_files/dependencies.txt
  UNDERSCORE_BASENAME=`echo $BASENAME | tr '-' '_'`
  cat $HOME/ci_scripts/czt_dependencies.dot | grep $UNDERSCORE_BASENAME | \
    grep -v "$UNDERSCORE_BASENAME ->" | awk -F' -' '{print $1}' | tr '_' '-' \
    | tr '\t' ' ' | awk '{ gsub(/ /,""); print }' >> $HOME/ci_scripts/text_files/dependencies.txt
  
  # Finished with this module, go back and start with next one
  echo "==============================================================================="
  cd $HOME 
done


# Run the test modules found in the dependencies of the modified modules
echo ""
echo "==============================================================================="
echo "============================== TESTING DEPENDENCIES ==========================="
echo "==============================================================================="
# cat ci_scripts/text_files/dependencies.txt | sort -u
# echo "==="
# cat ci_scripts/text_files/dependencies.txt | sort -u | while read line
# do
#   echo looking for $line
#   POM_PATH=$(echo `find . -name pom.xml | grep ${line}/pom.xml`)
#   echo $POM_PATH 
# done
# 



cat ci_scripts/text_files/dependencies.txt | sort -u | while read line
do
  POM_PATH=$(echo `find . -name pom.xml | grep ${line}/pom.xml`)
  if [ "$POM_PATH" != "" ]; then
    DEP_PATH=`dirname $POM_PATH`
    BASENAME=`basename $line`
    ALREADY_TESTED=`grep $BASENAME ci_scripts/text_files/modules_to_test.txt | wc -l`
    if [ $ALREADY_TESTED = "0" ]; then
      echo "|====>" $line
      cd $DEP_PATH
      echo $(pwd)
      mvn surefire:test | tee $HOME/ci_scripts/text_files/tmp.txt
      TEST_RESULT=`cat $HOME/ci_scripts/text_files/tmp.txt | grep "BUILD SUCCESS" | wc -l`
      if [ $TEST_RESULT == 0 ]; then
        clean_up
        exit 1
    fi
  fi

  # Finished with this module, go back and start with next one
  cd $HOME 
  fi
done

clean_up


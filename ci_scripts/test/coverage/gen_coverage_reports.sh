#!/usr/bin/env bash
set -e

CZT_HOME=$(pwd)
TMP=$CZT_HOME/ci_scripts/text_files/tmp.txt

# Set Up Function
function set_up {
  # clear files used before
  cd $CZT_HOME
  > $TMP
}

# Clean Up Function
function clean_up {
  cd $CZT_HOME
  rm $TMP
}

set_up

#mvn clean package -U -DskipTests

# Two methods for finding all test files
# find -name "*Test.java"
# find -name "*.java" | grep "src/test/"  > $TMP
find -name "*.java" | grep "src/test/" | grep "corejava"  > $TMP # Only test corejava at the moment

cat $TMP | while read line
do
  cd $CZT_HOME

  # Extract test name from path
  TEST_NAME=$(basename $line | awk -F.java '{print $1}')

  # Navigate to test directory then move up until module dir is reached (i.e. pom.xml file)
  TEST_DIR=`dirname $line`
  cd $TEST_DIR

  while [ `find -name "pom.xml" | wc -l` != 1 ]
  do
    cd ..
  done

  echo $TEST_NAME module dir at $(pwd)
  
  # Run test
  mvn clean test -Dtest=$TEST_NAME -DfailIfNoTests=false

  # Extract jacoco report
  MOD_NAME=`basename $(pwd)`
  cp `find -name "*jacoco.csv"` $CZT_HOME/ci_scripts/test/coverage/data/${MOD_NAME}_${TEST_NAME}.csv

done

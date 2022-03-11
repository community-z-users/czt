#!/bin/sh

# Set the heap space needed for core builds
#export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"

# In case of Maven errors, terminate the full build as well
# (This is to ensure step 2 does not run if step 1 fails)
set -e

echo Build typechecker $1

# Step 2: Build the CZT typechecker chosen by the given parameter
mvn -f typechecker-$1/pom.xml clean install $2

#-Dmaven.test.skip=true -U

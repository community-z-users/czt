#!/bin/sh

# Set the heap space needed for core builds
#export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"

# In case of Maven errors, terminate the full build as well
# (This is to ensure step 2 does not run if step 1 fails)
set -e

echo Build corjava $1

# -U = force snapshot updates

# Step 1: Build the CZT corejava source core
mvn -f corejava-src/pom.xml clean install -U

# Step 2: Build the CZT corejava chosen by the given parameter
mvn -f corejava-$1/pom.xml clean install -U

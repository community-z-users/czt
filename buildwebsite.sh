#!/bin/sh

# A convenience build script that performs CZT side build

# Set the heap space needed for core builds
#export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"

# In case of Maven errors, terminate the full build as well
# (This is to ensure step 2 does not run if step 1 fails)
set -e

mvn site site:stage -P site -U

#!/bin/sh

# A convenience build script that performs 2-step build of CZT.
#
# 2-step build is necessary to build CZT core modules needed for
# Eclipse plug-ins. Only after the core is built, the plug-ins
# can be located by CZT Eclipse dependency resolution.
#
# See http://wiki.eclipse.org/Tycho/How_Tos/Dependency_on_pom-first_artifacts

# Set the heap space needed for core builds
#export MAVEN_OPTS="-Xmx1024m -XX:MaxPermSize=512m"

# In case of Maven errors, terminate the full build as well
# (This is to ensure step 2 does not run if step 1 fails)
set -e

# Step 1: Build the CZT core
mvn clean install -U

# Step 2: Build the CZT Eclipse plug-ins
mvn -f eclipse/pom.xml clean install -U

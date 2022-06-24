#!/usr/bin/env bash

# Run this script from CZT_HOME 

python3 ci_scripts/dependency_tree/generate_dep_tree.py

# cat ci_scripts/dependency_tree/czt_dependencies.dot 

cat ci_scripts/dependency_tree/czt_dependencies.dot | grep -v "{}" | tee ci_scripts/dependency_tree/czt_dependencies.dot

# cat ci_scripts/dependency_tree/czt_dependencies.dot 

dot -Tsvg ci_scripts/dependency_tree/czt_dependencies.dot > ci_scripts/dependency_tree/czt_dep_tree.svg

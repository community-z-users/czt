#!/usr/bin/env bash

python3 ci_scripts/generate_dep_tree.py

cat ci_scripts/czt_dependencies.dot | grep -v "{}" > ci_scripts/czt_dependencies.dot

dot -Tsvg ci_scripts/czt_dependencies.dot > czt_dep_tree.svg

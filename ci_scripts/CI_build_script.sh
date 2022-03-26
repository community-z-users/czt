#!/bin/sh

cat main_build_report.txt | grep "BUILD SUCCESS" | wc -l

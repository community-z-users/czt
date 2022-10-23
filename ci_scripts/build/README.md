# Build Scripts

These scripts are used by the CI workflow

`build_czt.sh` builds the CZT project without running unit tests. It can be
used from the home CZT directory as follows:
```
chmod +x ci_scripts/build/*.sh  # Ensure scripts are executable
./ci_scripts/build/build_czt.sh
```

`build_status.sh` identifies the outcome of the build. This is probably not
useful for developers since they will see the outcome after running the script
above.


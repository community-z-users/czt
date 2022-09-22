# CZT Coverage Based TCP 

1) Generate Clover Coverage Data
    * Add the following to the Maven settings file (~/.m2/settings)
    ```
      <pluginGroups>
        <pluginGroup>org.openclover</pluginGroup>
      </pluginGroups>
    ```
    * Run the following command:
    ```
    mvn clean clover:instrument install clover:aggregate clover:clover
    ```

2) Move the clover coverage directory (named 'clover') to this directory
3) Run the gen_coverage_data.py script from this directory to create/update the coverage_data.txt file
4) Run the test script as described below

Navigate to CZT home directory (../../..) and run the following:
```
chmod +x ci_scripts/test/coverage/run_tests.py  # Make the python and bash scripts executable
./ci_scripts/test/coverage/run_tests.py

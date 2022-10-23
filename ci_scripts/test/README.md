# Test Case Prioritisation

## Full
This script executes the entire test suite.

## Module
The CZT project is split among modules that provide separate functionality.
Each module has several test classes that cover code within that module. The
Module based TCP system should identify and prioritise modules that have been
modified. Tests are then executed in the modified module before running tests
in modules that are dependent on the modified module.

## Coverage
### Total
The OpenClover tool is used to generate a coverage report of the CZT project.
Test classes are prioritised based on the absolute amount of modified source
code that they cover.

### Additional
Similar to Total coverage based TCP, Additional coverage based TCP prioritises
test classes that cover the largest amount of source code that has not yet been
covered.

## Comet [Depracated until further notice]
As the title suggests, this TCP system is depracted as of 09/09/22 as that is
when the API was disabled. The comet TCP system works as follows:

Using Smartesting’s Comet TCP system, the test suite will be sent to the API
with relevant metadata such as modified test and source class information. The
Comet API will return the prioritised order of tests. After executing the test
suite in the prioritised order, the results are sent to the Comet API to
improve their machinelearning based prioritisation system.

## Mutation Testing
The work conducted to evaluate the TCP systems is contained in this folder.


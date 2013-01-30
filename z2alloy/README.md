# Translator from Z to Alloy

This project provides a translator from Z specifications to [Alloy][alloy] notation.

Only a subset of Z constructs is supported by the translator.

A paper describing the translation was presented in ABZ 2010 conference:
[_"Translating Z to Alloy"_][alloy-paper].

[alloy]: http://alloy.mit.edu
[alloy-paper]: http://dx.doi.org/10.1007/978-3-642-11811-1_28


## Dependency on Alloy library

The project requires Alloy library to compile, which is not available in Maven Central.
For this reason, `z2alloy` is not deployed to Maven Central as well. Use the CZT repository
version instead.

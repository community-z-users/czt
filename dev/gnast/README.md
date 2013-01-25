# GnAST AST generator

GnAST is a source code generator that generates Java interfaces and classes from an XML Schema
definition. 

GnAST was designed to generate an annotated syntax tree (AST) for standard Z from the
schema describing [ZML][zml], an XML markup for the Z specification language.
It is also used to generate ASTs for Schemas describing Z extensions and even could be used
for Schemas that have nothing to do with the Z language.

[zml]: http://czt.sourceforge.net/zml/


## Usage

Refer to [FAQ][faq-usage] for some hints on how GnAST works. Use available [ZML schemas][zml]
for examples on how to define XML Schemas for generating AST using GnAST.

GnAST can be used standalone or within Maven builds using [GnAST Maven plugin][gnast-mvn].

[faq-usage]: faq.html#how_gnast_works
[gnast-mvn]: ../gnast-maven-plugin/

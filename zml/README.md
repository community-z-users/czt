# ZML: an XML markup for Z

This page describes an XML markup for the Z specification language,
based on the ISO Z Standard (2002).

The official ISO Z standard (_ISO/IEC 13568:2002_) is now available for
[free download][iso-z-download] (search for "Z formal specification"). For differences between
standard Z and Spivey Z, refer to [Ian Toyn's list][z-diffs].

The ZML format is specified by an XML schema file (_Z.xsd_). This specifies the allowable
'syntax' of each ZML construct. A paper describing this markup has been presented in
ZB2003 conference: [_ZML: XML Support for Standard Z_][zml-paper].

[iso-z-download]: http://standards.iso.org/ittf/PubliclyAvailableStandards/index.html
[z-diffs]: http://www.cs.york.ac.uk/hise/cadiz/standard.html
[zml-paper]: http://dx.doi.org/10.1007/3-540-44880-2_26


## ZML schema versions

To allow for evolution of the ZML format, each Z specification file (_spec.xml_) should specify
which version of the ZML format it is using, by including a `version="Major.Minor"` attribute
in the `<Spec>` tag. The default is the oldest version: `version="1.0"`.

The latest version of ZML is [**2.1**][zml-latest].
The following release location can be used in the `schemaLocation` attribute of _.xml_ files:

    http://czt.sourceforge.net/zml/zml/Z_2_1.xsd

Refer to [ZML release notes][zml-releases] for details about all public releases of _Z.xsd_ schema.

[zml-latest]: zml/Z_2_1.xsd
[zml-releases]: zml/index.html


## Background and rationale

The goal of providing an XML markup for Z specifications is to make it easier for tools to
exchange _annotated specifications_. For example, a specification might be parsed and typechecked
by one tool, then passed to another tool (in XML format) which expands schema calculus and puts
predicates into disjunctive normal form, then passed to another tool (in XML format) which
generates test cases from each disjunct. The XML format is simply a textual representation of the
annotated syntax tree of the Z specification.

Some advantages of using XML to exchange Z specifications between tools:

-   all programming languages provide libraries for loading and saving XML files,
    so multiple-language toolsets are easier.
-   annotations can be attached to any node of this ZML format, so it is easy to include type
    information for every variable and every expression.
-   each tool does not need to parse and typecheck Z -- this can be done by one tool,
    and the results used by many other tools.
-   there are many analysis and transformation tools for XML, such as the XSLT language,
    which makes it easy to transform XML files into other formats. 

A disadvantage is that XML files are large (at least 20 times larger than the Z specification
source), which makes transfer between tools a reasonably costly operation. For this reason, CZT
also offers libraries of Java classes and utilities which can directly manipulate the Z AST in
memory. This allows tighter integration of tools, but is limited to tools written in Java that use
our Z AST classes. So in practice, we expect that existing tools and non-Java tools will use the
ZML format to transfer specifications between tools, while new Z tools written in Java using CZT
will be able to directly pass AST objects from one tool to another, as well as being able to read
and write them as ZML. 

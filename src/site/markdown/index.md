#### [CZT for Eclipse][czt-eclipse]

[![CZT Eclipse IDE](eclipse/images/carousel-z-unicode.png)][czt-eclipse]

Develop Z specifications in Eclipse-based Community Z Tools IDE: parsing, typechecking, verification condition generation and more!


#### [CZT for jEdit][czt-jedit]

[![CZT for jEdit](jedit/images/carousel-jedit.png)][czt-jedit]

If jEdit is your editor of choice, use CZT jEdit plugins to typeset your Z specifications.


[czt-eclipse]: eclipse/
[czt-jedit]: jedit/


---

## CZT 2.0 preview!

This website represents a preview of the upcoming **CZT 2.0** release - the information available here may refer to tools that are part of the upcoming release. [Download][download] the nightly releases to get the latest and greatest version of Community Z Tools.

# Overview

The Community Z Tools (CZT) project is building a set of tools for editing, typechecking and animating formal specifications written in the [Z specification language][z], with some support for Z extensions such as Object-Z, Circus, etc. These tools are all built using the CZT Java framework for Z tools.

Beta-versions of the end-user CZT tools are now included in the CZT releases ([download][download]). These include an Eclipse-based [Community Z Tools IDE][czt-eclipse] as well as plug-ins for the [jEdit editor][czt-jedit]. Refer to each sub-project and the [manual][manual] for more information.

[z]: http://formalmethods.wikia.com/wiki/Z_notation
[download]: http://sourceforge.net/projects/czt/files
[manual]: manual.html

## CZT objectives

Our objectives are to encourage interchange between existing Z
tools (via a standard XML interchange format for Z),
and to provide open-source libraries for building and integrating
new Z tools.
The software we are building includes:

-   An [XML Schema markup](zml/) for Z.

-   [Java classes](corejava/) for Z annotated syntax trees (AST).

-   Java classes for converting between XML and Java AST.

-   Java libraries for the common operations needed in every Z tool (markup-converters, parser, type-checker, etc). A [paper](http://www.springerlink.com/index/10.1007/11415787_5) describing these has been presented at [ZB2005](http://www.zb2005.org).

-   Graphical Z editors, with facilities for easily entering the special Z unicode symbols. Currently we provide plug-ins for [Eclipse IDE][czt-eclipse] and [jEdit editor][czt-jedit].

-   A Z animation tool called ZLive, with a customisable graphical user interface.

-   Export tools, to output Z in other notations or for other Z tools.

-   Extended versions of the libraries and tools to support Z extensions
such as [Object-Z](http://www.itee.uq.edu.au/~smith/objectz.html),
[Circus](http://www.cs.york.ac.uk/circus/) and others.

-   And more - check out all CZT subprojects!


## CZT projects

Community Z Tools consists of a number of interconnected projects. Each sub-project is placed in its own website - use the **Modules** menu in the top-right to browse the CZT projects.


---

## Background

(Adapted from Andrew Martin's [original CZT proposal][czt-proposal])

The Z specification language was adopted as an ISO standard in 2002.
It can be used to precisely specify the requirements or behaviour of
systems, and analyze that behaviour via proof, animation,
test generation, etc. However, one of the biggest barriers to the
widespread use of the Z specification language seems to be the issue
of tool support.

Many projects have constructed Z tools, some of product quality,
most as student projects. Few of them are integrated with each other;
few support all the new ISO standard; fewer still build together
to form the kind of integrated environment that developers are
beginning to expect. Many good ideas have been developed to
prototype stage, and then have been lost as projects have
finished and students or researchers have moved on. The number
of times a request for a Z parser arises in the Z newsgroup
suggests lots of people are producing tools, most of which will
never be seen outside their own institute. An integrated effort
will move forward the state of tools, and thereby the take-up of Z. 

[czt-proposal]: http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT/proposal.html

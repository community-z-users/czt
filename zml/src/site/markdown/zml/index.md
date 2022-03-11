# ZML schema versions

To allow for evolution of the ZML format, each Z specification file (_spec.xml_) should specify
which version of the ZML format it is using, by including a `version="Major.Minor"` attribute
in the `<Spec>` tag. The default is the oldest version: `version="1.0"`.

The following list shows the public versions of _Z.xsd_ that have been released plus the
official location of that schema (this can be used in the `schemaLocation` attribute of _.xml_
files). It also relates that public version number to the internal revision number of `Z.xsd`
within the CZT source code repository, and gives a summary of the significant changes from the
previous version. An exhaustive list of all changes to _Z.xsd_ (most of which do not affect the
XML format) can be found in the CZT [source code repository][czt-src].

[czt-src]: ../source-repository.html


## ZML 2.1

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_2_1.xsd`](Z_2_1.xsd)
-   SVN revision: 5169

Changes:

-   Removed XML Schema elements and types `DeclName`, `ZDeclName`, `RefName`, `ZRefName`,
    `DeclNameList`, `ZDeclNameList`, `RefNameList`, and `ZRefNameList` and introduce new XML Schema
    elements and types `Name`, `ZName`, `NameList`, and `ZNameList` instead since the distinction
    between `DeclName` and `RefName` does not seem to be relevant and makes handling of IDs more
    difficult. `Name` is now used in places where either a `DeclName` or a `RefName` has been used;
    `NameList` is used in places where either a `DeclNameList` or a `RefNameList` has been used.
-   Removed optional attributes `Author`, `Modified`, and `Source` from element `Spec`.
    Annotations can be used to preserve this sort of information.

## ZML 2.0

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_2_0.xsd`](Z_2_0.xsd)
-   CVS revision: 1.95

Changes:

-   Renamed the `SchText` element and type to `ZSchText` and added new abstract element and type
    `SchText`. The element `ZSchText` is declared to be in the substitution group of (the new
    abstract) element `SchText`. This makes it possible to define new kinds of schema texts by
    providing new elements that are in the substitution group of `SchText` like, for example,
    jokers (metavariables) as used in Cadiz's tactic language.
-   Renamed the `DeclName` element and type to `ZDeclName` and added new abstract element and type
    `DeclName`. The element `ZDeclName` is declared to be in the substitution group of (the new
    abstract) element `DeclName`.
-   Renamed the `RefName` element and type to `ZRefName` and added new abstract element and type
    `RefName`. The element `ZRefName` is declared to be in the substitution group of (the new
    abstract) element `RefName`.
-   Deleted abstract element and type `Name` since it is no longer used.
-   Added new element and type `Numeral` (abstract) and `ZNumeral` and use it in `NumExpr` and
    `TupleSelExpr`.
-   Added new elements and types for lists:
    
    -   `BranchList` (abstract) and `ZBranchList`,
    -   `DeclList` (abstract) and `ZDeclList`,
    -   `DeclNameList` (abstract) and `ZDeclNameList`,
    -   `ExprList` (abstract) and `ZExprList`,
    -   `FreetypeList` (abstract) and `ZFreetypeList`,
    -   `ParaList` (abstract) and `ZParaList`,
    -   `RefNameList` (abstract) and `ZRefNameList`,
    -   `RenameList` (abstract) and `ZRenameList`,
    -   `StrokeList` (abstract) and `ZStrokeList`.
    
    Those are now used instead of sequences defined via `minOccurs` and `maxOccurs` elements.
-   Removed element and type `NameExprPair` since it is not used any more.
-   Removed element and type `TypeEnvAnn` since it is not used. Use `Signature` instead.
-   Rename `NameNamePair` as `NewOldPair` and use Z ordering of the names.
-   Rename `Number` as `Digit` to distinguish it from `Numeral`.
-   Rename type `TermA` as `Term` and let all other types extend from `Term`.
    Now all elements can have annotations.
-   Added new attribute `Explicit` to `RefExpr`. It is used to distinguish whether the
    instantiating expressions are explicitly given in the specification (`explicit` is `true`) or
    whether they were inferred by the typechecker (`explicit` is `false`).
-   Added new element/type `Ann`, an abstract base class for all annotations.
    This is mostly for consistency with our other complex type hierarchies.
-   Added new attributes `Start` and `Length` to `LocAnn`.
-   Improved some documentation.


## ZML 1.4

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_1_4.xsd`](Z_1_4.xsd)
-   CVS revision: 1.71

Changes:

-   Added new elements/types for `SignatureAnn` to be used by the typechecker.


## ZML 1.3

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_1_3.xsd`](Z_1_3.xsd)
-   CVS revision: 1.69

Changes:

-   Added new elements/types `LatexMarkupPara` and `Directive` to support storing the LaTeX markup
    function in the AST.
-   Added new elements/types `GenericType` and `Type2` to reflect the grammar for types given in
    the ISO Standard for Z.
-   Renamed `GenType` to `GenParamType` to avoid confusion with `GenericType`. 
-   Changed attribute `Loc` in `LocAnn` to be optional. 
-   Changed attribute `Prec` in `OptempPara` to be optional. This can be used by, for instance,
    prefix templates, which do not have a precedence value. 
-   Remove the default value for the `Assoc` attribute. Not setting this attribute can be used by,
    for instance, prefix templates, which do not have an associativity. 
-   Changed element `Oper` to be abstract. 
-   Improved documentation.


## ZML 1.2

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_1_2.xsd`](Z_1_2.xsd)
-   CVS revision: 1.55

Changes:

-   Changed operator templates to use an inheritance hierarchy for `Operator` and `Operand`.
    This is more consistent with other parts of the schema, and allows stronger typing within the
    Java AST. This has changed the XML format slightly from:

    ```xml
    <OptempPara ...>
      <Operand/>
      <Word>*</Word>
      <Operand/>
    </OptempPara>
    ```

    to

    ```
    <OptempPara ...>
      <Operand/>
      <Operator><Word>*</Word></Operator>
      <Operand/>
    </OptempPara>
    ```

## ZML 1.1

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_1_1.xsd`](Z_1_1.xsd)
-   CVS revision: 1.39

Changes:

-   Changed namespace and schemaLocation to czt.sourceforge.net.
-   Added `version`/`author`/`date`/`source-location` attributes to `<Spec>`.
-   Changed operator templates slightly, so that they now contain a (alternating) sequence of
    `<Word>` and `<Operand>` tags, where `<Operand>` may add the attribute `List="true"`
    to indicate an sequence of operands.
-   Renamed `FreeType` to `Freetype` to conform to the Z standard.
-   Added a tag around rename pairs, for consistency with other pairs and triples.
    Also swapped the order of `NewName` and `OldName` within these pairs, to reflect the
    functional nature (domain &rarr; range) of the renaming.
-   Removed `##other` from `Section` and `Paragraph` because it causes ambiguity when extending
    the schema. This makes the schema more strict, because standard XML validators will now
    **REQUIRE** Z extensions to have a schema.


## ZML 1.0

-   Location: [`http://czt.sourceforge.net/zml/zml/Z_1_0.xsd`](Z_1_0.xsd)
-   CVS revision: 1.16

This version was described in the [ZB2003 paper][zml-paper] and used by several projects at the
National University of Singapore. If `<Spec>` has no version attribute, this version is used.

[zml-paper]: http://dx.doi.org/10.1007/3-540-44880-2_26


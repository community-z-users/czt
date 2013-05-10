# CZT Corejava

Corejava is part of the [CZT][czt] project that aims at providing a framework for building
formal methods tools, especially for the Z specification language.  This subproject provides
AST (Annotated Syntax Tree) classes for Z and its extensions, written in Java.

If you are a Z user and you are looking for existing Z tools, you might be more interested
in other, more user oriented subprojects of CZT (which often use the classes provided here).
If you are a developer of Z tools, this might be exactly what you are looking for.

Features are:

-   AST interfaces and classes for standard Z, Object Z, Circus, and other extensions.
-   Support for the visitor design pattern that allows tools to traverse the AST.
-   XML reader and writer to serialise AST structure to corresponding ZML files.

[czt]: http://czt.sourceforge.net


## Dialects

CZT provides tools for Z specification language and its extensions.
The ASTs of Z extensions supplement the AST of core Z language. To provide modularity, each
dialect gets its own Corejava project with appropriate dependencies between them.
For your projects, select just the dialects you need as your dependencies:

-   [**Z** (core): `corejava-z`](corejava-z/)
-   [**Z Pattern** extension: `corejava-zpatt`](corejava-zpatt/)
-   [**Z/EVES** extension: `corejava-zeves`](corejava-zeves/)
-   [**Object-Z** extension: `corejava-oz`](corejava-oz/)
-   [**Circus** extension: `corejava-circus`](corejava-circus/)
-   [**Circus Pattern** extension: `corejava-circuspatt`](corejava-circuspatt/)
-   [**Circus Time** extension: `corejava-circustime`](corejava-circustime/)


## Visitor support in Corejava

Corejava provides a variant of the [default visitor][visitor-paper] introduced by
Martin E. Nordberg III. The default visitor adds another level of inheritance to the visitor
pattern. It provides the possibility to implement default behaviour by taking advantage of the
inheritance relationship of the classes to be visited.

[visitor-paper]: http://www.ccs.neu.edu/research/demeter/adaptive-patterns/visitor-usage/papers/plop96/variations-visitor-nordberg.ps

Nordberg achieves this by deriving the default visitor from the standard visitor, adding visit
methods for each abstract AST class, and implementing the visit methods in such a way that the
visit method for a class `Foo` calls the visit method for class `Bar` where `Bar` is the base
class of `Foo`.

The CZT AST classes already support visit methods for abstract classes.
Each AST class `Foo`, concrete as well as abstract, has a corresponding `FooVisitor` interface
defining the `visitFoo()` method. A visitor may or may not implement this particular interface.
If an instance of class `Foo` accepts a visitor, it checks whether the visiting visitor implements
`FooVisitor`.  If this is the case, this method is called.  However, if the accepted visitor does
not implement `FooVisitor`, it is checked whether it implements `BarVisitor` where `Bar` is the
base class of `Foo`, etc. This way, the AST classes itself take care of calling the closest
(with respect to inheritance hierarchy) visit method implemented by the visitor.

This makes it very easy to implement a visitor that visits each element of an AST without being
forced to implement all visit methods for concrete classes:

```java
public SimpleVisitor implements TermVisitor
{
  public Object visitTerm(Term term)
  {
    for (Object arg : term.getChildren()) {
      if (arg instanceof Term) {
        ((Term) arg).accept(this);
      }
      else if (arg instanceof List<?>) {
        // handle lists ...
      }
    }
    return null;
  }
}
```

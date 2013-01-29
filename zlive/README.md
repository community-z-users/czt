# ZLive animator

The ZLive animator allows evaluating Z expressions, predicates and schemas.
It can be used to execute some schemas, to test that given values satisfy a schema, or to generate
all solutions of a set or schema.

ZLive provides a simple textual user interface that handles Z in LaTeX and Unicode markup.
Also, ZLive is the evaluation engine behind the experimental [Gaffe2][gaffe2] user interface
builder. The aim is to allow customised graphical interfaces to be built for the animation of a
given Z specification.

Here is a simple example of using the text interface of ZLive (not fully implemented yet!):

```
ZLive (C) Mark Utting
Z> eval 4 \upto 6 \cup 1 \upto 2
\{ 1, 2, 4, 5, 6 \}
Z> eval \{ a,b:0 \upto 100 | a*b = 20 \}
\{ (1,20), (2,10), (4,5), (5,4), (10,2), (20,1) \}
Z> exit
```

[czt]: http://czt.sourceforge.net
[gaffe2]: ../gaffe2/

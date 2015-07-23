# ZLive animator

The ZLive animator allows evaluating Z expressions, predicates and schemas.
It can be used to execute some schemas, to test that given values satisfy a schema, or to generate
all solutions of a set or schema.

ZLive provides a simple textual user interface that handles Z in LaTeX and Unicode markup.
Also, ZLive is the evaluation engine behind the experimental [Gaffe2][gaffe2] user interface
builder. The aim of Gaffe2 is to allow customised graphical interfaces to be built for the
animation of a given Z specification.

Here is a simple example of using the text interface of ZLive (TextUI.main()):
(This text-based interface to ZLive is also available via the CZT User
Interface: java -jar czt.jar, then use the 'Animate' menu).

```
$ java -jar czt.jar zlive
ZLiveversion 1.6 (C) 2006 Mark Utting
ZLiveDefault> eval (4 \upto 6) \cup (1 \upto 2)
\{ 1, 2, 4, 5, 6 \}                         %% the display order may vary
ZLiveDefault> eval \{ a,b:0 \upto 100 | a*b = 20 \}
\{ (1,20), (2,10), (4,5), (5,4), (10,2), (20,1) \}
ZLiveDefault> load examples/calc.czt
Loading section Specification
Setting section to Specification            %% an unnamed Z section is called 'Specification'
Specification> do Init
1: \lblot curr' == 0 , prev' == 0 \rblot    %% the first (and only) solution
Specification> ; [Add | value? = 3]         %% compose the current state with an Add schema
1: \lblot curr == 0 , prev == 0 , curr' == 3 , prev' == 0 , value? == 3 \rblot
Specification> next                         %% see if there are any more solutions?
no more solutions
Specification> ; Negate                     %% compose the current state with the Negate schema
1: \lblot curr == 3 , prev == 0 , curr' ==~-3 , prev' == 3 \rblot
Specification> exit
```

<<User help:>> You can run ZLive with the '--help' argument to see command line arguments.
Within the text interface of ZLive, you can type 'help' to see the available commands,
and the 'set' command shows all the current settings.  More documentation is needed.
We really need a tutorial...

<<Developer help:>> As well as over 200 unit tests, ZLive has a comprehensive
suite of over 700 system tests, which are driven by Z specifications in the
src/tests/resources/animate*.tex input files.
These do not all pass yet, since some of them test features of Z that are not yet supported.
The current (and historic) coverage is recorded in tests/UserTest-Statistics.xls.
You can use 'ant' to run the system tests, compare the results before and after a change, etc.
Change directory into the tests directory and run 'ant -p' to see the available commands.
(You might need to download and install the 'Maven Ant Tasks' jar first).
You should also read the README.txt file there.



[czt]: http://czt.sourceforge.net
[gaffe2]: ../gaffe2/

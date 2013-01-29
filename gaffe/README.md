# CZT Gaffe animator GUI

Gaffe stands for (G)raphical (A)nimator (F)ront(E)nd.
It provides a customisable GUI front-end to a [Z animator][zlive].

Gaffe provides three main functions:

-   Gaffe **generator** automatically creates a custom user interface to use with a
    Z specification provided to it.
-   Gaffe **designer** provides a graphical interface builder for creating or modifying the custom
    user interface.
-   Gaffe **animator** attaches to the Z animator and allows the custom interfaces created with
    the generator and designer to be used to test a Z specification.

[zlive]: ../zlive/


## Documentation

Gaffe was initially created as part of the Master's thesis by Nicholas Daley. The thesis describing
the project and associated documents are available:

-   Nicholas Daley. [_Gaffe: Graphical Front-ends for Z Animation_][gaffe-thesis]. Master's thesis,
    University of Waikato, New Zealand, 2003.
-   [_Quick Guide to the Gaffe Designer_][gaffe-guide]
-   [Gaffe evaluation exercises][gaffe-exercises]

[gaffe-thesis]: thesis.pdf
[gaffe-guide]: guide.pdf
[gaffe-exercises]: exercises.pdf


### Configuration

The `DesignerCore` runs a configuration script when it starts.
Extra or replacement scripts can be configured on a per system/per user basis. The ability to
configure this will be added to the GUI, but at present anyone wishing to do this will
have to find an alternative way to configure this into `java.util.prefs`' persistent store.


### License of Gaffe-created interfaces

Are interfaces created using Gaffe derivative works under the GPL?
:   Interface files created by the Gaffe designer, or the generator should be considered exempt
    from the GPL's restrictions on derivative works.

    This means is that the files you create are not automatically GPLed, and you may attach any
    license you wish to them.

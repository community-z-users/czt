Translator from Z to a B abstract machine (*.mch ascii syntax)

The B notation was designed by J.R. Abrial, who was also one of
the designers of Z.  Their mathematical toolkits are very similar,
but B has more support for modularity and refinement (including
an executable sublanguage).
The standard reference is "The B-Book: Assigning Programs to Meanings",
by J-R. Abrial, Cambridge University Press, 1996, ISBN 0 521 49619 5.

This translator converts a Z specification (which currently must
contain just one section) into the ASCII (*.mch) syntax used by the B
tools (Atelier B and the B toolkit).  The goal of the translator is
to give Z users access to the refinement and proof tools of B,
and also to give Z users access to the animation and test generation
tools of the BZ-TT (BZ Testing Tools) environment.

BZ-TT (BZ Testing Tools) is a suite of tools for animating and
generating tests from formal specifications, such as B (and now Z),
Statecharts, and soon UML+OCL and JML.
See the following websites for more details and publications:

    http://www.lifc.univ-fcomte.fr/~bztt
    http://www.leirios.com


TODO:
* check that numbers are in the range allowed by B (0..2^32-1)
* convert all set names to all upper case.

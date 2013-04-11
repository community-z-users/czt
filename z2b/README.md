# Translator from Z to B

This project provides a translator from Z specifications to B abstract machines.

The B notation was designed by J.R. Abrial, who was also one of the designers of Z notation.
Their mathematical toolkits are very similar, but B has more support for modularity and
refinement (including an executable sublanguage). The standard reference for B method is
_"The B-Book: Assigning Programs to Meanings"_, by J-R. Abrial, Cambridge University Press,
1996, ISBN 0 521 49619 5.

This translator converts a Z specification (which currently must contain just one section)
into the ASCII (_*.mch_) syntax used by the B tools (Atelier B and the B toolkit). 
The goal of the translator is to give Z users access to the refinement and proof tools of B,
and also to give Z users access to the animation and test generation tools of the
BZ-TT (BZ Testing Tools) environment.

BZ-TT (BZ Testing Tools) is a suite of tools for animating and generating tests from formal
specifications, such as B (and now Z), Statecharts, and soon UML+OCL and JML.
See the [Leirios][leirios] websites for more details and publications.

[leirios]: http://www.leirios.com


## Known issues and improvements

Below is a list of known issues and things to do for the Z to B translation.

-   Check that numbers are in the range allowed by B (0..2^32-1)
-   Convert all set names to all upper case.
-   Optimize the operations so that unmodified state vars are not assigned.
-   Improve the separation of precondition from postcondition (currently the
    precondition is just all the conjuncts with no `'` or `!` decorations).
-   Integrate the parser, so that it handles more than just _.xml_ input.
-   implement more kinds of expressions.
-   Trap unimplemented expressions so that warnings/errors are given.

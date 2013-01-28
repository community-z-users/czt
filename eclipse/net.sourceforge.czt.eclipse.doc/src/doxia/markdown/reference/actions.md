# CZT Editor Actions

This page describes the CZT-specific actions available in the CZT editors.

## Edit Menu Actions

Go To Declaration
:   _Ctrl+Shift+G_
:   Navigate to the declaration of a Z name

Highlight
:   _Ctrl+Shift+Arrow Keys_
:   -   Enclosing Term - Highlight the term containing the current cursor position. If a term is
        already highlighted, it highlights the enclosing term of the highlighted term. (Arrow Up)
    -   Restore Last Highlight - Highlight the term that is previously highlighted. If no term is
        highlighted or the highlighted term is the smallest term being highlighted, it does
        nothing. (Arrow Down)

Convert To
:   _Ctrl+Shift+(L, O, U or X)_
:   -   LaTeX - Convert current Unicode specification to a LaTeX specification. (L)
    -   Old LaTeX - Convert current Unicode specification to a Old LaTeX specification. (Spivey Z,
        which preceded the ISO Z Standard). (O)
    -   Unicode - Convert current LaTeX specification to a Unicode specification. (U)
    -   XML - Convert current specification to an XML specification. (X)

# CZT ZSideKick plugin for jEdit

The ZSideKick plugin is an extension of the [SideKick plugin][sidekick] that allows
specifications written in Z notation or its extensions to be parsed and typechecked automatically.

![CZT ZSideKick plugin for jEdit](images/czt-jedit-zsidekick.png)

## Usage

Any errors found are reported to the [ErrorList plugin][errorlist], which means that they
are displayed in the ErrorList plugin window and highlighted in the text area. Also supported
are the selection of well formed formulae and actions based on this selection like jumping to the
definition of a referencing name.

The ZSideKick plugin shares its view with other SideKick plugins through the
SideKick Structure Browser. It is most convenient to dock the Structure Browser on the left
or right. In the Structure Browser, a tree view for the sections and paragraphs of a
specification is shown. A mouse click on one of the nodes in the tree will highlight the line
in the jEdit buffer where that item begins. Shift-click on a node will select that node in the
buffer. The tree will also follow the cursor in the buffer, that is, the selected node in the tree
will change depending on the cursor position.

The parser used for a particular buffer depends on the mode. By default the following mode
associations are set:

-   **`z`** - Unicode Z parser
-   **`oz`** - Unicode Object-Z parser
-   **`circus`** - Unicode Circus parser
-   **`zeves`** - Unicode Z/EVES parser
-   **`zlatex`** - LaTeX Z parser
-   **`ozlatex`** - LaTeX Object-Z parser
-   **`circuslatex`** - LaTeX Circus parser
-   **`zeveslatex`** - LaTeX Z/EVES parser

These associations can be customised in the SideKick options dialog. It is also possible to
associate files or file endings to particular modes by modifying the jEdit `catalog` file.
See the [jEdit documentation][jedit-doc] on how to install edit modes and other information.

[sidekick]: http://plugins.jedit.org/plugins/?SideKick
[errorlist]: http://plugins.jedit.org/plugins/?ErrorList
[jedit-doc]: ../

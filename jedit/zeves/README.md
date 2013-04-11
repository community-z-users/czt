# CZT Z/EVES plugin for jEdit

The Z/EVES plugin is an embedding of Z/EVES, a Z theorem prover for Z, in the jEdit
[Console plugin][console].

## Usage

The Z/EVES plugin is an extension of the [Console][console] and [CZT ZSideKick plugin][zsidekick],
so these plugins must be installed as well in order to be able to use it. 

The Z/EVES plugin can be accessed by starting the Console plugin and choosing the `zeves` shell from
the drop-down list at the top left corner of the Console plugin interface. Z/EVES commands can now
be typed into the text field provided by the Console plugin interface. When the Enter key or "Run"
button is pressed, the given command is interpreted by Z/EVES and the result is printed in the
Console window.

Refer to Z/EVES documentation for details on using Z/EVES theorem prover via command-line.

[console]: http://plugins.jedit.org/plugins/?Console
[zsidekick]: ../ZSideKick/

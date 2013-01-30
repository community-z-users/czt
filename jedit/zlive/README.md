# CZT ZLive plugin for jEdit

The ZLive plugin is an embedding of ZLive, a Z animator for Z, in the jEdit
[Console plugin][console].

## Usage

The ZLive plugin is an extension of the [Console][console] and [CZT ZSideKick plugin][zsidekick],
so these plugins must be installed as well in order to be able to use it. 

The ZLive plugin can be accessed by starting the Console plugin and choosing the `zlive` shell from
the drop-down list at the top left corner of the Console plugin interface. ZLive commands can now
be typed into the text field provided by the Console plugin interface. When the Enter key or "Run"
button is pressed, the given command is interpreted by ZLive and the result is printed in the
Console window.

Refer to [ZLive documentation][zlive] for details on using ZLive animator.

[console]: http://plugins.jedit.org/plugins/?Console
[zsidekick]: ../ZSideKick/
[zlive]: ../../zlive/

# CZT font

The CZT font has been developed to ensure correct support of all Z unicode symbols. Download the following font and install it to your system to display Z unicode specifications in Community Z Tools and IDEs.

-   [Download **CZT Sans** font](CZTSans.ttf)

The _CZT Sans_ font is derived from the _Bitstream Vera Sans_ font (about 120 Z characters were added), and is distributed under the original [Bitstream Vera Copyright](http://www.gnome.org/fonts/).


## Installing CZT font

Refer to the documentation of your operating system on installing fonts.


## Selecting the CZT font within jEdit

After installing the font, we can use the CZT font in jEdit. The following steps give a quick outline:

1.  Open jEdit global settings (**Utilities > Options > Global Options** in the menu).
2.  Select **Text Area** pane.
3.  Set **Text Font** to be CZT (click the existing font and select **CZT** family in the dialog).
4.  Enable **Smooth Text** and **Fractional Font Metrics** to turn on anti-aliasing of fonts if you want to.
5.  Restart jEdit if the CZT plugins are not displaying the characters correctly. The font in CZT plugins does not change dynamically.

After doing these steps, you should see all the Z characters in the CZT plugins (no little square boxes, which mean a missing symbol in the font).

## Using the CZT font within CZT Eclipse

[CZT Eclipse plugins][czt-eclipse] load the CZT font automatically if it is not available on the user's system. So when using CZT Eclipse, you do not need to install CZT font.

You can adjust the font size for CZT Eclipse in preferences: **Preferences > General > Appearance > Colors and Fonts >> CZT > Unicode Z Editor Font**.

[czt-eclipse]: ../eclipse

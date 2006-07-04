                    Installing the CZT font
                    =======================

We are not experts in installing fonts, so please check the
documentation of your operating system how fonts are installed. The
following summarises our experiences with installing the font on
Windows XP and Linux. 

Windows XP
**********

Go into Start/Control Panel, then into the "Fonts" program. (If you
are using the new XP categories, you need to select "Appearance and
Themes" first, then the "Fonts" link will appear in the left-hand
sidebar). Once you are in the "Fonts" program, use the "File/Install
new font" menu entry, then browse to the fonts/ttf subdirectory and
add the "CZT Sans" font.

Linux
*****

Executing the following commands worked for me on gentoo (without
having root privileges):

  cd fonts/ttf
  ttmkfdir > fonts.scale
  mkfontdir
  xset fp+ `pwd`
  xset fp rehash

More information can be obtained from:

* The Font HOWTO http://www.linux.org/docs/ldp/howto/Font-HOWTO/
* The Malta Linux User Group http://linux.org.mt/article/ttfonts


Selecting the CZT font within jEdit
***********************************

After installing the font, we must tell jEdit to use that font in all
its buffers. To do this, go into the jEdit global settings panel (you
can use the "Utilities/Global Options" menu to open this panel), then
into the "Text Area" pane and set the "Text Font" to be CZT (clicking
on the existing font name will open a requestor, then you can scroll
down the left-hand column to select the "CZT" family). You might also
like to enable the "Smooth Text" and "Fractional Font Metrics" on this
"Text Area" pane, to turn on anti-aliasing of fonts.

You need to restart jEdit to see the font in the CZT plugin as well,
since the font in the CZT plugin cannot yet be set dynamically. After
you have done this, you should see all the Z characters in the CZT
plugin (no little square boxes, which mean a missing symbol in the
font).

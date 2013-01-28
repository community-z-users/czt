# Basic Editor Preferences

The **CZT > Editor** preference page offers the general settings for the CZT editor.

![CZT Editor Preference Page](../../images/pref_editor.png)

The following properties can be set in this page:

## Parsing

Enable parsing
:   _Default: On_
:   Enables the background parsing. If it is enabled, the parser runs constantly in the background
    each time a file is opened or the text in the editor is changed.  If it is disabled, then
    those parser-dependent features, for example the content outline and hover messages, will be
    unavailable.

Report problems when saving
:   _Default: Off_
:   The editor reports problems found by the background parser when the editor is saved.

Report problems while editing
:   _Default: On_
:   The editor reports problems found by the background parser as the user is editing the
    specification

## Matching Brackets

Highlight Matching Brackets
:   _Default: On_
:   Whether the matching brackets are highlighted in the editor.

Matching Brackets Color
:   _Default: Gray (RGB 192,192,192)_
:   The color used for highlighting the matching bracket.

### General Settings

Synchronize Outline selection when the cursor moves
:   _Default: On_
:   The selection in the editor synchronizes with the selection in the Outline view.

Show text hover
:   _Default: On_
:   The editor displays hover message when the mouse is hovering inside the editor.

Mark Occurrences
:   _Default: On_
:   The editor highlights all occurrences of a Z name when the cursor within it.

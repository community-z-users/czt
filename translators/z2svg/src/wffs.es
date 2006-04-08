// This file is an example SVG+JavaScript document for displaying
// a Z paragraph in which well-formed formulae can be selected by
// clicking the mouse.  Contributed to CZT by Ian Toyn and Petra Malik.

// Global state:
var curWff = null;		// The currently selected well-formed formula

// init -- initialisation of global state.
// This is the handler for event onload.
function init()
{
}

// inSelected -- is the given wff in the current wff?
function inSelected(wff)
{
	if (wff.getAttributeNS(null, "id") == "wff_root" || curWff == null) {
		return (false);
	} else if (wff == curWff) {
		return (true);
	} else {
		return (inSelected(wff.parentNode));
	}
}

// deselect -- make there be no current selection.
// This is the handler for event onclick on the background rect.
function deselect()
{
	if (curWff != null) {
		curWff.removeAttributeNS(null, "fill");
	}
	curWff = null;
}

// select -- adjust the current selection appropriately.
// This is the handler for event onclick on a text.
function select(evt)
{
	var selText = evt.target;
	if (curWff != null) {
		curWff.removeAttributeNS(null, "fill");
	}
	if (inSelected(selText.parentNode) && curWff.parentNode != null) {
		do {
			curWff = curWff.parentNode;
		} while (curWff.getAttributeNS(null, "sel") != "true");
	} else {
		curWff = selText.parentNode;
	}
	curWff.setAttributeNS(null, "fill", "white");
}

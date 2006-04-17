// This file contains JavaScript for operations on well-formed formulae (wffs)
// represented by SVG objects.  The operations include:
// select() -- for selecting a wff, highlighting it in the window;
// pretty() -- for laying out the wffs within the (resized) window.
// Contributed to CZT by Ian Toyn and Petra Malik.

// Assumption: only one root wff (BUG: this is unacceptable)
// Assumption: root wffs are selectable (this seems acceptable)

// Wff representation:
// Elements:
// <text> -- a string of text
// <line> -- a single line
// <g> -- a wff
// Attributes:
// <g sel="true" or sel="false"> -- whether wff is selectable
// <* break="yes" or break="maybe" or omitted> -- whether to precede with NL
// <text space="42"> -- pixels of space to insert if not after NL
// <* break="*" indent="42"> -- pixels to indent if preceded by NL

// Global state:
var curWff = null;		// The currently selected wff
var rootWff;			// The root wff

// init -- initialisation of global state.
// This is the handler for event onload.
function init()
{
	rootWff = document.getElementById("wff_root");
	calcwidth (rootWff);
	pretty();
	window.onresize = pretty;
}

//////////////////////////////////////////////////////////////////////////
// Selection determines the current wff.  It happens in response to
// onclick events on individual SVG objects.  All SVG objects that are
// part of a wff (texts) should be declared with attribute
// onclick="select(evt)", and all SVG objects that are not part of a wff
// (lines and background rect) should be declared with attribute
// onclick="deselect()" (and <g> doesn't need one).

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
	if (inSelected(selText.parentNode)) {
		curWff = curWff.parentNode;
	} else {
		curWff = selText;
	}
	while (curWff.getAttributeNS(null, "sel") != "true") {
		curWff = curWff.parentNode;
	}
	curWff.setAttributeNS(null, "fill", "white");
}

//////////////////////////////////////////////////////////////////////////
// Prettyprinting is inspired by Oppen's algorithm (TOPLAS 1980),
// but changed to work on the in-memory tree of SVG objects.
// The <g> elements take the place of Oppen's begin/end bracket tokens.
// The break and space attributes separate two roles of Oppen's blank token.

// calcwidth -- given a wff, annotate each of its elements with its width.
// The calculation includes spaces; if those spaces are omitted in a
// particular layout, then the subsequent user of the width figure will
// do the relevant subtraction.  Results are saved in "need" attributes.
// This is analogous to Oppen's scan() operation, but instead of looking-ahead,
// calcwidth() traverses the in-memory wff tree in reverse in-order, ie R-to-L.
function calcwidth(wff)
{
	var need;
	if (wff.tagName == "g") {
		var children = wff.childNodes;
		need = 0;
		for (var i = children.length; i > 0; i--) {
			var child = children.item(i-1);
			if (child.tagName == "text"
			 || child.tagName == "line"
			 || child.tagName == "g") {
				need = need+calcwidth(child);
			}
		}
	} else {
		need = wff.getBBox().width;
	}
	if (wff.hasAttributeNS(null, "space")) {
		need = need+parseFloat(wff.getAttributeNS(null, "space"));
	}
	wff.setAttributeNS (null, "need", need);
	return (need);
}

// windowWidth -- return width of window.
function windowWidth()
{
	if (window.innerWidth) {
		return (window.innerWidth);
	} else {
		return (svgroot.viewport.width);
	}
}

// pretty -- set the positions of all the SVG objects in the window.
// This is the handler for event onresize.
function pretty()
{
	prettyWff (rootWff, 30, 30, 30, 0);
}

// prettyWff -- given a wff, the position at which to start positioning its
// elements, the indentation at which to resume after a line break, and the
// maximum height of elements already positioned on the current line,
// position the elements of the wff, then return the final position and the
// maximum height of elements positioned on its last line.
// Oppen's stack of indents is implicit in the indent arguments of recursive
// calls to prettyWff().
function prettyWff(wff, x, y, indent, maxheight)
{
	var tuple = new Object();
	var space;
	var advance;
	if (wff.tagName == "text"
	 || wff.tagName == "line"
	 || wff.tagName == "g") {
		if (wff.hasAttributeNS(null, "break")) {
			if (wff.getAttributeNS(null, "break") == "yes"
			 || wff.getAttributeNS(null, "need") > windowWidth()-x) {
				if (wff.hasAttributeNS(null, "indent")) {
					indent = indent+parseFloat(wff.getAttributeNS(null, "indent"));
				}
				x = indent;
				y = y+maxheight+4;
			}
		}
		if (wff.tagName == "g") {
			var children = wff.childNodes;
			for (var i = 0; i < children.length; i++) {
				var child = children.item(i);

				if (child.tagName != "") {
					tuple = prettyWff(child, x, y, indent, maxheight);
					x = tuple.x;
					y = tuple.y;
					if (tuple.height > maxheight) {
						maxheight = tuple.height;
					}
				}
			}
		} else if (wff.tagName == "line" && wff.getBBox().height > 0) {
			// Not horizontal, so can't be laid out with text.
		} else {
			advance = parseFloat(wff.getAttributeNS(null, "need"));
			if (wff.hasAttributeNS(null, "space")) {
				space = parseFloat(wff.getAttributeNS(null, "space"));
				if (x == indent) {
					advance = advance-space;
					space = 0;
				}
			} else {
				space = 0;
			}
			if (wff.tagName == "text") {
				wff.setAttributeNS (null, "x", x+space);
				wff.setAttributeNS (null, "y", y);
				x = x+advance;
				if (wff.getBBox.height > maxheight) {
					maxheight = wff.getBBox().height;
				}
			} else {	// Horizontal line
				wff.setAttributeNS (null, "x1", x+space);
				wff.setAttributeNS (null, "y1", y);
				wff.setAttributeNS (null, "y2", y);
				x = x+advance;
				wff.setAttributeNS (null, "x2", x);
			}
		}
	}
	tuple.x = x;
	tuple.y = y;
	tuple.height = maxheight;
	return (tuple);
}

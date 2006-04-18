// This file contains JavaScript for operations on well-formed formulae (wffs)
// represented by SVG objects.  The operations include:
// select() -- for selecting a wff, highlighting it in the window;
// pretty() -- for laying out the wffs within the (resized) window.
// Contributed to CZT by Ian Toyn and Petra Malik.

// Assumption: only one root wff (BUG: this is unacceptable)
// Assumption: root wffs are selectable (this seems acceptable)

// Wff representation:
// A text element whose text is hierarchically decomposed using tspans
// according to the structure of its well-formed formulae.
// Added tspan attributes:
// sel="true" or sel="false" or omitted -- whether wff is selectable
// break="yes" or break="maybe" or omitted -- whether to precede with NL
// indent="42" -- (must be a break attr too) pixels to indent if preceded by NL
// space="42" -- pixels of space to insert if not after NL

// Global state:
var curWff = null;   // The currently selected wff
var rootWff;         // The root wff

// init -- initialisation of global state.
// This is the handler for event onload.
function init()
{
  rootWff = document.getElementById("wff_root");
  calcwidth(rootWff);
  pretty();
  window.onresize = pretty;
}

//////////////////////////////////////////////////////////////////////////
// Selection determines the current wff.  It happens in response to
// onclick events on individual SVG objects.  Leaf tspans should have
// onclick="select(evt)".  Branch tspans should have no onclick.
// Other elements (lines and background rect) should have onclick="deselect()".

// inSelected -- is the given wff in the current wff?
function inSelected(wff)
{
  if (wff.getAttributeNS(null, "id") == "wff_root" || curWff == null) {
    return (false);
  }
  else if (wff == curWff) {
    return (true);
  }
  else {
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
  }
  else {
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
// The branching tspans take the place of Oppen's begin/end bracket tokens.
// The break and space attributes separate two roles of Oppen's blank token.

// calcwidth -- given a wff, annotate each of its elements with its width.
// The calculation includes spaces; if those spaces are omitted in a
// particular layout, then the subsequent user of the width figure will
// do the relevant subtraction.  Results are saved in "need" attributes.
// This is analogous to Oppen's scan() operation, but instead of looking-ahead,
// calcwidth() traverses the in-memory wff tree in reverse in-order, ie R-to-L.
function calcwidth(wff)
{
  var need = 0;
  var children = wff.childNodes;
  var found = false;
  for (var i = children.length; i > 0; i--) {
    var child = children.item(i-1);
    if (child.tagName == "tspan") {
      need = need+calcwidth(child);
      found = true;
    }
  }
  if (found == false) {
    need = wff.getComputedTextLength();
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
  var children = wff.childNodes;
  var found = false;
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
  for (var i = 0; i < children.length; i++) {
    var child = children.item(i);

    if (child.tagName == "tspan") {
      tuple = prettyWff(child, x, y, indent, maxheight);
      x = tuple.x;
      y = tuple.y;
      if (tuple.height > maxheight) {
	maxheight = tuple.height;
      }
      found = true;
    }
  }
  if (found == false) {
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
    wff.setAttributeNS (null, "x", x+space);
    wff.setAttributeNS (null, "y", y);
    x = x+advance;
    //alert ("wff="+wff);
    //alert("wff.getExtentOfChar="+wff.getExtentOfChar(1));
    //r = wff.getExtentOfChar(1);
    //if (r.y2-r.y1 > maxheight) {
    //maxheight = r.y2-r.y1;
    //}
    maxheight = 12;//BUG: Want actual height
  }
  tuple.x = x;
  tuple.y = y;
  tuple.height = maxheight;
  return (tuple);
}

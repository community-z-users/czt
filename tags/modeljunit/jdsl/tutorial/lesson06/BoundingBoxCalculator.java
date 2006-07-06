import jdsl.core.algo.traversals.*;
import jdsl.core.api.*;
import java.awt.*;
import java.awt.geom.*;

/** 
 * The first step in drawing the tree. The tree is drawn so:
 *   - Edges are straight lines
 *   - nodes are centered above the drawings of their children
 *   - bounding boxes of the drawings of subtrees rooted at siblings are drawn
 *     adjacent.
 *   - The width of a bounding box is the maximum of the label width and the
 *     sum of the bounding boxes of the children.
 *
 * @author Lucy Perry (lep)
 * @version JDSL 2
*/
public class BoundingBoxCalculator extends EulerTour {
  
  /* ************************************ */ 
  /* The members described in the lesson. */
  /* ************************************ */ 
  //b6.4
  protected int offset = 50;        // size of the grid squares
  protected int width  = 0;         // a running total width of the explored tree drawing

  protected int depth = 0;          // a running total depth of the explored tree drawing
  protected Graphics g;             // the graphics object where the tree will be drawn
  protected FontMetrics fm;         // the fontMetrics object for g
  //e6.4
  
  /**
   * When a node is visited first in the Euler Tour we know the upper-left hand 
   * corner of its bounding box, which we store as decorations.
   */
  //b6.5
  protected void visitFirstTime(Position pos){
    pos.set("y", new Integer(depth));
    pos.set("x", new Integer(width));
    depth += offset;
  }
  //e6.5
  
  /**
   * When a node is visited last in the Euler Tour we know the width 
   * of its bounding box, which we store as a decoration.
   */
  //b6.6
  protected void visitLastTime(Position pos){
    int textWidth = textWidth(pos);
    int shift = 0;
    int x = ((Integer)pos.get("x")).intValue();
    int boxWidth = width-x;
    if (textWidth>boxWidth) {
      int delta = textWidth-boxWidth;
      boxWidth = textWidth;
      width += delta;
      shift = delta/2;
    }
    pos.set("width", new Integer(boxWidth));
    // The distance that the children's bounding boxes need to
    // be shifted in the drawing.
    pos.set("shift", new Integer(shift));
    depth -= offset;
  }
  //e6.6
  
  /* 
   * Sets all attributes for an external node
   */
  //b6.7 
  protected void visitExternal( Position pos ) { 
    pos.set("y", new Integer(depth));
    pos.set("x", new Integer(width));
    int textWidth = textWidth(pos);
    width+=textWidth;
    pos.set("width", new Integer(textWidth));
    pos.set("shift", new Integer(0));
  } 
  //e6.7

  /* ************************************ */ 
  /* Members not described in the lesson. */
  /* ************************************ */ 
      
  protected int pad=5;              // the distance to separate bounding boxes;
  
  public BoundingBoxCalculator(Graphics gg) {
    g=gg;
    fm = g.getFontMetrics();
  }
  
  /**
   * Calculates the width of the drawing of the node label.  Stores 
   * the attributes needed to calculate the exact position to draw the
   * label.
   */
  protected int textWidth(Position pos) {
    String str=pos.element().toString();
    Rectangle2D bounds = fm.getStringBounds(str,g);
    pos.set("bounds", bounds);
    pos.set("ascent", new Integer(fm.getMaxAscent()));
    pos.set("descent", new Integer(fm.getMaxDescent()));
    return (int)bounds.getWidth()+pad;
  }
}

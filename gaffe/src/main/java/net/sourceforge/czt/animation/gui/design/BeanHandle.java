/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.design;

import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Cursor;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;

import javax.swing.BorderFactory;
import javax.swing.JPanel;
import javax.swing.event.MouseInputAdapter;

/**
 * The component that acts as a resizing/moving handle for each bean in the
 * FormDesign.
 * These handles are small squares that sit above the edges, corners, and center
 * of their matching bean.
 */
final class BeanHandle extends JPanel
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 3611505202192601073L;

/**
   * The component on the content pane this handle is matched to.
   */
  protected Component component_;

  /**
   * Which corner/edge this handle sits on.
   */
  protected final int corner_;

  private final FormDesign formDesign_;

  /**
   * Creates a BeanHandle without specifying which bean it is for.
   * @param corner The edge/corner to sit this handle on.
   */
  public BeanHandle(int corner, FormDesign formDesign)
  {
    this(null, corner, formDesign);
  };

  /**
   * Creates a BeanHandle for a particular component.
   * @param c the component to match this handle to.
   * @param corner The edge/corner to sit this handle on.
   */
  public BeanHandle(Component c, int corner, FormDesign formDesign)
  {
    setComponent(c);
    corner_ = corner;
    formDesign_ = formDesign;
    setCursor(new Cursor(corner_));
    setBorder(BorderFactory.createLineBorder(Color.black));
    DragListener dl = new DragListener();
    addMouseMotionListener(dl);
    addMouseListener(dl);
    setSize(10, 10);

    setLocation();
    component_.addComponentListener(new BoundsChangeListener());
    setBackground(Color.gray);

    invariant();
  };

  /**
   * Checks the invariant of this class.  That the corner has to be one of the
   * 8 compass directions specified in Cursor.
   * @see java.awt.Cursor
   */
  protected void invariant()
  {
    switch (corner_) {
      case Cursor.N_RESIZE_CURSOR :
      case Cursor.NW_RESIZE_CURSOR :
      case Cursor.NE_RESIZE_CURSOR :
      case Cursor.S_RESIZE_CURSOR :
      case Cursor.SW_RESIZE_CURSOR :
      case Cursor.SE_RESIZE_CURSOR :
      case Cursor.W_RESIZE_CURSOR :
      case Cursor.E_RESIZE_CURSOR :
      case Cursor.MOVE_CURSOR :
        break;
      default :
        throw new Error("Error: Invariant for BeanHandle broken "
            + "- corner_ must be one of the move or compass point "
            + "cursor numbers.");
    };
  };

  /**
   * Getter function for component_.
   */
  public Component getComponent()
  {
    return component_;
  };

  /**
   * Setter function for component_.
   */
  public void setComponent(Component c)
  {
    component_ = c;
  };

  /**
   * Listener used to resize/move the matching component whenever this handle is
   * dragged.
   */
  private class DragListener extends MouseInputAdapter
  {
    /**
     * The point where a drag started.
     */
    protected Point clickDownPoint_;

    /**
     * Resizes/moves the component. Inherited from MouseInputAdapter.
     */
    public synchronized void mouseDragged(MouseEvent e)
    {
      if ((e.getModifiers() & InputEvent.BUTTON1_MASK) == 0)
        return;
      Point mousePoint = e.getPoint();
      if (clickDownPoint_ == null) {
        System.err.println("### possible coding error###, "
            + "mouseDragged in BeanHandle without press first");
        clickDownPoint_ = mousePoint;
        return;
      };
      mousePoint.translate((int) -clickDownPoint_.x, (int) -clickDownPoint_.y);
      Rectangle newBounds = getComponent().getBounds();
      switch (corner_) {
        case Cursor.N_RESIZE_CURSOR :
        case Cursor.NW_RESIZE_CURSOR :
        case Cursor.NE_RESIZE_CURSOR :
          if (mousePoint.getY() > newBounds.getHeight())
            mousePoint.y = (int) newBounds.getHeight();
          newBounds.height -= mousePoint.getY();
        case Cursor.MOVE_CURSOR :
          newBounds.y += mousePoint.getY();
          break;
        case Cursor.S_RESIZE_CURSOR :
        case Cursor.SW_RESIZE_CURSOR :
        case Cursor.SE_RESIZE_CURSOR :
          if (-mousePoint.getY() > newBounds.getHeight())
            mousePoint.y = (int) -newBounds.getHeight();
          newBounds.height += mousePoint.getY();
          break;
        default : //do nothing
      };
      switch (corner_) {
        case Cursor.W_RESIZE_CURSOR :
        case Cursor.NW_RESIZE_CURSOR :
        case Cursor.SW_RESIZE_CURSOR :
          if (mousePoint.getX() > newBounds.width)
            mousePoint.x = (int) newBounds.getWidth();
          newBounds.width -= mousePoint.getX();
        case Cursor.MOVE_CURSOR :
          newBounds.x += mousePoint.getX();
          break;
        case Cursor.E_RESIZE_CURSOR :
        case Cursor.NE_RESIZE_CURSOR :
        case Cursor.SE_RESIZE_CURSOR :
          if (-mousePoint.getX() > newBounds.getWidth())
            mousePoint.x = (int) -newBounds.getWidth();
          newBounds.width += mousePoint.getX();
          break;
        default :
      };

      getComponent().setBounds(newBounds);
      if (getComponent() instanceof Container)
        ((Container) getComponent()).validate();
      //XXX use Robot to stop mouse moving?
    };

    /**
     * Sets the clickDownPoint.  Inherited from MouseInputAdapter.
     */
    public synchronized void mousePressed(MouseEvent e)
    {
      clickDownPoint_ = e.getPoint();
    };

    /**
     * Resets the clickDownPoint.  Inherited from MouseInputAdapter.
     */
    public synchronized void mouseReleased(MouseEvent e)
    {
      clickDownPoint_ = null;
    };
  };

  protected void setLocation()
  {
    Point newLocation = getComponent().getLocation();

    switch (corner_) {
      case Cursor.E_RESIZE_CURSOR :
      case Cursor.NE_RESIZE_CURSOR :
      case Cursor.SE_RESIZE_CURSOR :
        newLocation.x += getComponent().getWidth();
        break;
      case Cursor.N_RESIZE_CURSOR :
      case Cursor.S_RESIZE_CURSOR :
      case Cursor.MOVE_CURSOR :
        newLocation.x += getComponent().getWidth() / 2;
      default : //do nothing
    };
    switch (corner_) {
      case Cursor.S_RESIZE_CURSOR :
      case Cursor.SW_RESIZE_CURSOR :
      case Cursor.SE_RESIZE_CURSOR :
        newLocation.y += getComponent().getHeight();
        break;
      case Cursor.W_RESIZE_CURSOR :
      case Cursor.E_RESIZE_CURSOR :
      case Cursor.MOVE_CURSOR :
        newLocation.y += getComponent().getHeight() / 2;
      default : //do nothing
    };

    newLocation.x -= getWidth() / 2;
    newLocation.y -= getHeight() / 2;
    newLocation = formDesign_.translateCoordinateFromCSpace(newLocation,
        getComponent().getParent());
    setLocation(newLocation);
    formDesign_.repaint();
  };

  /**
   * Watches the attached component for changes in its bounds, and adjusts the
   * handle's location accordingly.
   */
  protected class BoundsChangeListener extends ComponentAdapter
  {
    public void componentMoved(ComponentEvent e)
    {
      setLocation();
    };

    public void componentResized(ComponentEvent e)
    {
      setLocation();
    };
  };
};

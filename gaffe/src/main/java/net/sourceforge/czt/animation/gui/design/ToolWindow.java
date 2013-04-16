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
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.MediaTracker;
import java.awt.Point;
import java.awt.Transparency;
import java.awt.event.ActionEvent;
import java.awt.event.MouseEvent;
import java.beans.BeanInfo;
import java.beans.Beans;
import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.io.IOException;
import java.util.ListIterator;
import java.util.Vector;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ActionMap;
import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.border.BevelBorder;
import javax.swing.border.Border;
import javax.swing.event.EventListenerList;

/**
 * The window that provides buttons for selecting tools.
 */
class ToolWindow extends JFrame
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -9136575187654875644L;

protected Vector<Tool> tools; //Vector<Tool> tools

  protected JPanel nonBeanToolPanel;

  protected JPanel beanToolPanel;

  private Tool currentTool;

  private final Tool defaultTool;

  private EventListenerList toolChangeListeners;

  public Tool getCurrentTool()
  {
    return currentTool;
  };

  protected void setCurrentTool(Tool t)
  {
    Tool oldTool = currentTool;
    currentTool = t;
    if (oldTool != null)
      oldTool.unselected();
    if (currentTool != null)
      currentTool.selected();
    fireToolChanged(currentTool, oldTool);
    if (currentTool != null && currentTool.isOneShot()
        && currentTool != defaultTool)
      setCurrentTool(defaultTool);
  };

  /**
   * Registers a <code>ToolChangeListener</code> with the
   * <code>ToolWindow</code>.
   * Note: it will send a toolChanged message to the listener (with the tool
   * and oldTool parameters equal) when it is registered.
   */
  public void addToolChangeListener(ToolChangeListener l)
  {
    toolChangeListeners.add(ToolChangeListener.class, l);
    l
        .toolChanged(new ToolChangeEvent(this, getCurrentTool(),
            getCurrentTool()));
  }

  /**
   * Unregisters a <code>ToolChangeListener</code> with the
   * <code>ToolWindow</code>.
   */
  public void removeToolChangeListener(ToolChangeListener l)
  {
    toolChangeListeners.remove(ToolChangeListener.class, l);
  }

  public ToolChangeListener[] getToolChangeListeners()
  {
    return (ToolChangeListener[]) toolChangeListeners
        .getListeners(ToolChangeListener.class);
  };

  protected void fireToolChanged(Tool tool, Tool oldTool)
  {
    final ToolChangeListener[] listeners = getToolChangeListeners();
    final ToolChangeEvent ev = new ToolChangeEvent(this, tool, oldTool);
    for (int i = 0; i < listeners.length; i++)
      listeners[i].toolChanged(ev);
  };

  Cursor crossCursor;

  private void setupCrossCursor()
  {
    MediaTracker mt = new MediaTracker(this);
    String cursorPath = "net/sourceforge/czt/animation/gui/design/XCursor.gif";
    Image baseCursorImage = getToolkit().getImage(
        ClassLoader.getSystemResource(cursorPath)).getScaledInstance(16, 16,
        Image.SCALE_DEFAULT);
    ;
    mt.addImage(baseCursorImage, 0);
    try {
      mt.waitForID(0);
    } catch (InterruptedException ex) {
      System.err.println("Interrupted"); //XXX
    };

    Dimension bestSize = getToolkit().getBestCursorSize(16, 16);
    Image cursorImage = getGraphicsConfiguration().createCompatibleImage(
        bestSize.width, bestSize.height, Transparency.BITMASK);
    mt.addImage(cursorImage, 1);
    cursorImage.getGraphics().drawImage(baseCursorImage, 0, 0, null);
    try {
      mt.waitForID(1);
    } catch (InterruptedException ex) {
      System.err.println("Interrupted"); //XXX
    };
    crossCursor = getToolkit().createCustomCursor(cursorImage, new Point(8, 8),
        "CrossCursor");
  };

  public ToolWindow(Class<?>[] beanTypes, ActionMap am)
  {
    setupCrossCursor();
    setTitle("GAfFE: Tool Window");
    toolChangeListeners = new EventListenerList();
    tools = new Vector<Tool>();
    Tool tool;
    tool = new SelectBeanTool(am);
    defaultTool = tool;
    setCurrentTool(tool);
    tools.add(tool);
    tool = new DeleteBeanTool();
    tools.add(tool);
    tool = new MakeEventLinkTool();
    tools.add(tool);
    tool = new DeleteEventLinkTool();
    tools.add(tool);

    getContentPane().setLayout(
        new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));

    nonBeanToolPanel = new JPanel();
    getContentPane().add(nonBeanToolPanel);
    Border nbtBorder = BorderFactory.createBevelBorder(BevelBorder.LOWERED);
    nonBeanToolPanel.setBorder(nbtBorder);
    nonBeanToolPanel.setLayout(new FlowLayout());

    beanToolPanel = new JPanel();
    getContentPane().add(beanToolPanel);
    Border btpBorder = BorderFactory.createBevelBorder(BevelBorder.LOWERED);
    beanToolPanel.setBorder(btpBorder); //XXX title border?
    beanToolPanel.setLayout(new FlowLayout());

    for (Tool t : tools) {
      nonBeanToolPanel.add(t.getButton());
    }
    for (int i = 0; i < beanTypes.length; i++)
      try {
        addBeanTool(beanTypes[i]);
      } catch (IntrospectionException ex) {
        //Do Nothing
      };
    //    setSize(200,200);
    pack();
    setVisible(true);
  };

  public void addBeanTool(Class<?> type) throws IntrospectionException
  {
    Tool tool = new PlaceBeanTool(type);
    tools.add(tool);
    beanToolPanel.add(tool.getButton());
  };

  public void removeBeanTool(Class<?> type)
  {
    for (ListIterator<Tool> i = tools.listIterator(); i.hasNext();) {
      Tool tool = i.next();
      if (tool instanceof PlaceBeanTool
          && ((PlaceBeanTool) tool).getType().equals(type)) {
        beanToolPanel.remove(tool.getButton());
        i.remove();
      }
    }
  };

  /**
   Superclass of all of the form design tools.
   */
  public abstract class Tool
  {
    /**
     * <code>Icon</code> to display in the <code>ToolWindow</code> for this
     * <code>Tool</code>.
     */
    private final Icon icon_;

    /**
     * Name of this tool.  Appears on the tool's button if there is no icon.
     */
    private final String name_;

    /**
     * Short description of this tool.
     */
    private final String description_;

    /**
     * Button to display in the <code>ToolWindow</code>.
     */
    private final JButton button_;

    private final Border buttonBorderSelected_;

    private final Border buttonBorderUnselected_;

    private final boolean oneShot_;

    protected Tool(Icon icon, String name, String description)
    {
      this(icon, name, description, false);
    };

    /**
     * Button is generated from the other information given.
     * @param icon Value for @{link #icon_ icon_}.
     * @param name Value for @{link #name_ name_}.
     * @param description Value for @{link #description_ description_}.
     */
    protected Tool(Icon icon, String name, String description, boolean oneShot)
    {
      icon_ = icon;
      name_ = name;
      description_ = description;
      oneShot_ = oneShot;
      Action action = new AbstractAction(getIcon() == null ? getName() : null,
          getIcon())
      {
        /**
		 * 
		 */
		private static final long serialVersionUID = -1600823966098229338L;

		public void actionPerformed(ActionEvent e)
        {
          if (getCurrentTool() == Tool.this)
            setCurrentTool(defaultTool);
          else
            setCurrentTool(Tool.this);
        };
      };
      action.putValue(Action.SHORT_DESCRIPTION, getDescription());
      button_ = new JButton(action);

      Border raisedBorder = BorderFactory.createBevelBorder(BevelBorder.RAISED);
      Border emptyBorder = BorderFactory.createEmptyBorder(5, 5, 5, 5);
      buttonBorderUnselected_ = BorderFactory.createCompoundBorder(
          raisedBorder, emptyBorder);
      Border loweredBorder = BorderFactory
          .createBevelBorder(BevelBorder.LOWERED);
      emptyBorder = BorderFactory.createEmptyBorder(5, 5, 5, 5);
      buttonBorderSelected_ = BorderFactory.createCompoundBorder(loweredBorder,
          emptyBorder);
      button_.setBorder(buttonBorderUnselected_);
    };

    /**
     * Getter function for {@link #button_ button_}.
     */
    public final JButton getButton()
    {
      return button_;
    };

    /**
     * Getter function for {@link #description_ description_}.
     */
    public final String getDescription()
    {
      return description_;
    };

    /**
     * Getter function for {@link #icon_ icon_}.
     */
    public final Icon getIcon()
    {
      return icon_;
    };

    /**
     * Getter function for {@link #name_ name_}.
     */
    public final String getName()
    {
      return name_;
    };

    public final boolean isOneShot()
    {
      return oneShot_;
    };

    /**
     * Called by the <code>ToolWindow</code> when the <code>Tool</code> is
     * selected.
     */
    public void selected()
    {
      getButton().setBorder(buttonBorderSelected_);
      getButton().setBackground(getButton().getBackground().darker());
      getButton().requestFocus();
    };

    /**
     * Called by the <code>ToolWindow</code> when a different <code>Tool</code>
     * is selected.
     */
    public void unselected()
    {
      getButton().setBorder(buttonBorderUnselected_);
      getButton().setBackground(getButton().getBackground().brighter());
    };

    /**
     * Called by the <code>FormDesign f</code> when the <code>Tool</code> is
     * selected.
     */
    public void selected(FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when a different
     * <code>Tool</code> is selected.
     */
    public void unselected(FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a
     * mouseClicked  event.
     */
    public void mouseClicked(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a
     * mousePressed event.
     */
    public void mousePressed(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a
     * mouseReleased event.
     */
    public void mouseReleased(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a
     * mouseEntered event.
     */
    public void mouseEntered(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a mouseExited
     * event.
     */
    public void mouseExited(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a
     * mouseDragged event.
     */
    public void mouseDragged(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code> when it experiences a mouseMoved
     * event.
     */
    public void mouseMoved(MouseEvent e, FormDesign f)
    {
    };

    /**
     * Called by the <code>FormDesign f</code>'s glass pane when it experiences
     * a paint event.
     */
    public void paint(Graphics g, FormDesign f)
    {
    };
  };

  //Not actually needed outside of PlaceBeanTool, but to be usable by
  //PlaceBeanTool's constructor it needs to be static which isn't possible
  //because PlaceBeanTool must be non-static!
  //XXX Is there a way around this? an ugly way around it could use an anonymous
  //inner class with this function.
  private static Icon getIconForType(Class<?> type) throws IntrospectionException
  {
    final BeanInfo bi = Introspector.getBeanInfo(type);
    //final BeanDescriptor bd = bi.getBeanDescriptor();

    Image icon;
    icon = bi.getIcon(BeanInfo.ICON_COLOR_32x32);
    if (icon == null)
      icon = bi.getIcon(BeanInfo.ICON_MONO_32x32);
    if (icon == null)
      icon = bi.getIcon(BeanInfo.ICON_COLOR_16x16);
    if (icon == null)
      icon = bi.getIcon(BeanInfo.ICON_MONO_16x16);
    if (icon == null)
      return null;
    else
      return new ImageIcon(icon);
  };

  /**
   * Tool for placing beans into a FormDesign.
   */
  protected class PlaceBeanTool extends Tool
  {
    protected final Class<?> type;

    protected final BeanInfo beanInfo;

    public PlaceBeanTool(Class<?> type) throws IntrospectionException
    {
      super(getIconForType(type), Introspector.getBeanInfo(type)
          .getBeanDescriptor().getDisplayName(), Introspector.getBeanInfo(type)
          .getBeanDescriptor().getShortDescription());
      beanInfo = Introspector.getBeanInfo(type);
      this.type = type;
    };

    public Class<?> getType()
    {
      return type;
    };

    protected Object beanInProgress = null;

    protected Component componentInProgress = null;

    public void mousePressed(MouseEvent e, FormDesign f)
    {
      if (!f.placementAllowed(e.getPoint(), type))
        return;
      try {
        beanInProgress = Beans.instantiate(null, type.getName());
      } catch (ClassNotFoundException ex) {
        System.err.println("Couldn't instantiate an object for "
            + type.getName());
        System.err.println(ex); //XXX do more reporting here
        return;
      } catch (IOException ex) {
        System.err.println("I/O error trying to load " + type.getName());
        System.err.println(ex); //XXX do more reporting here
        return;
      };
      try {
        componentInProgress = f.addBean(beanInProgress, e.getPoint());
      } catch (BeanOutOfBoundsException ex) {
        beanInProgress = null;
        componentInProgress = null;
        throw new Error("FormDesign.addBean threw BeanOutOfBoundsException "
            + "after bounds were checked.", ex);
      }
    };

    public void mouseDragged(MouseEvent e, FormDesign f)
    {
      if (beanInProgress == null)
        return;
      if (componentInProgress == null)
        System.err.println("EH WHAT!!, componentInProgress=null, but "
            + "beanInProgress doesn't!");

      Dimension newSize = new Dimension();
      newSize.width = e.getX()
          - f.componentLocationInBeanPaneSpace(componentInProgress).x;
      newSize.height = e.getY()
          - f.componentLocationInBeanPaneSpace(componentInProgress).y;
      if (newSize.getWidth() < 0)
        newSize.width = 0;
      if (newSize.getHeight() < 0)
        newSize.height = 0;
      componentInProgress.setSize(newSize);
      //XXX stop from resizing off side of parent?
    };

    public void mouseReleased(MouseEvent e, FormDesign f)
    {
      beanInProgress = componentInProgress = null;
      setCurrentTool(defaultTool);
    };

    public void mouseMoved(MouseEvent e, FormDesign f)
    {
      if (f.placementAllowed(e.getPoint(), type))
        f.setCursor(Cursor.getPredefinedCursor(Cursor.CROSSHAIR_CURSOR));
      else
        f.setCursor(crossCursor);
    };

    public void unselected()
    {
      super.unselected();
      beanInProgress = componentInProgress = null;
    };

    public void unselected(FormDesign f)
    {
      f.setCursor(Cursor.getDefaultCursor());
    };
  };

  /**
   * Tool for selecting a bean.
   */
  protected class SelectBeanTool extends Tool
  {
    //Just so we can open the properties window on a double click.
    //private final ActionMap actionMap;
    public SelectBeanTool(ActionMap am)
    {
      //XXX change to use javabeancontext's getSystemResource instead of
      //    ClassLoader's?
      super(new ImageIcon(getToolkit().getImage(
          ClassLoader.getSystemResource("net/sourceforge/czt/animation/gui/"
              + "design/selectIcon.gif"))), "Select", "Select Beans");
      //actionMap=am;
    };

    protected SelectBeanTool(Icon icon, String name, String description,
        ActionMap am)
    {
      super(icon, name, description);
      //actionMap=am;
    };

    //private Component lastSelected=null;
    public synchronized void mouseClicked(MouseEvent e, FormDesign f)
    {
      Component current = f.getCurrentBeanComponent();
      Point location = e.getPoint();
      if (current != null && current instanceof Container) {
        Point translatedLocation = f.translateCoordinateToCSpace(location,
            current);
        if (current.contains(translatedLocation)) {
          //XXX Double-click results in two events.
          //    So current bean changes too.
          //    Need to find a way of stopping that.
          //            if (e.getClickCount() == 2) {
          //              actionMap.get("Show Properties Window").
          //                actionPerformed(new ActionEvent(this,
          //                                                ActionEvent.ACTION_PERFORMED,
          //                                                "Show Properties Window"));
          //              return;
          //            }
          //lastSelected=current;
          if (current instanceof JScrollPane) {
            JScrollPane sp = (JScrollPane) current;
            f.setCurrentBeanComponent(sp.getViewport().getView());
            return;
          }
          Component c = current.getComponentAt(translatedLocation);
          if (c != current) {
            f.setCurrentBeanComponent(c);
            return;
          }
        }
      }
      Component c = f.getBeanPane().getComponentAt(e.getPoint());
      if (c != f.getBeanPane())
        f.setCurrentBeanComponent(c);
    };

  };

  /**
   * Tool for deleting the selected bean.
   */
  protected class DeleteBeanTool extends Tool
  {
    public DeleteBeanTool()
    {
      //XXX change to use javabeancontext's getSystemResource instead?
      super(new ImageIcon(getToolkit().getImage(
          ClassLoader
              .getSystemResource("net/sourceforge/czt/animation/gui/design/"
                  + "deleteIcon.gif"))), "Delete", "Delete Selected Bean", true);
    };

    public void selected(FormDesign f)
    {
      if (f.getCurrentBean() != null)
        if (!f.removeCurrentBean())
          getToolkit().beep();
    };
  };

  /**
   * Tool for making an event link to register listeners with beans.
   */
  protected class MakeEventLinkTool extends Tool
  {
    private BeanInfo sourceInfo_;

    private Component source_;

    private Object sourceBean_;

    //private BeanInfo listenerInfo_;
    private Component listener_;

    private Object listenerBean_;

    private Point lastMousePoint_;

    public MakeEventLinkTool()
    {
      //XXX change to use javabeancontext's getSystemResource instead?
      super(new ImageIcon(getToolkit().getImage(
          ClassLoader
              .getSystemResource("net/sourceforge/czt/animation/gui/design/"
                  + "eventIcon.gif"))), "Event",
          "Link a bean to a listener bean", false);
    };

    private void getSource(MouseEvent e, FormDesign f)
    {
      source_ = f.lowestComponentAt(e.getPoint());
      if (source_ == null) {
        sourceBean_ = null;
        sourceInfo_ = null;
        return;
      }

      sourceBean_ = BeanWrapper.getBean(source_);
      try {
        sourceInfo_ = Introspector.getBeanInfo(sourceBean_.getClass());
      } catch (IntrospectionException ex) {
        sourceInfo_ = null;
      }
    };

    private void getListener(MouseEvent e, FormDesign f)
    {
      listener_ = f.lowestComponentAt(e.getPoint());
      if (listener_ == null) {
        listenerBean_ = null;
        //listenerInfo_ = null;
        return;
      }

      listenerBean_ = BeanWrapper.getBean(listener_);
      /*try {
       listenerInfo_ = Introspector.getBeanInfo(listenerBean_.getClass());
       } catch (IntrospectionException ex) {
       listenerInfo_ = null;
       }*/
    };

    public void mouseMoved(MouseEvent e, FormDesign f)
    {
      getSource(e, f);
      lastMousePoint_ = e.getPoint();
      if (sourceInfo_ != null
          && sourceInfo_.getEventSetDescriptors().length > 0)
        f.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
      else
        f.setCursor(crossCursor);
    };

    public void mousePressed(MouseEvent e, FormDesign f)
    {
      getSource(e, f);
      lastMousePoint_ = e.getPoint();
    };

    public void mouseDragged(MouseEvent e, FormDesign f)
    {
      getListener(e, f);
      lastMousePoint_ = e.getPoint();
      f.repaint();
      if (sourceInfo_ != null && listenerBean_ != null) {
        EventSetDescriptor[] esds = sourceInfo_.getEventSetDescriptors();
        for (int i = 0; i < esds.length; i++) {
          Class<?> ltype = esds[i].getListenerType();
          if (ltype.isAssignableFrom(listenerBean_.getClass())) {
            f.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
            return;
          }
        }
      }
      f.setCursor(crossCursor);
    };

    public void mouseReleased(MouseEvent e, FormDesign f)
    {
      getListener(e, f);

      Vector<Class<?>> approvedListenerTypes = new Vector<Class<?>>();
      if (sourceInfo_ != null && listenerBean_ != null) {
        EventSetDescriptor[] esds = sourceInfo_.getEventSetDescriptors();
        for (int i = 0; i < esds.length; i++) {
          Class<?> ltype = esds[i].getListenerType();
          if (ltype.isAssignableFrom(listenerBean_.getClass())) {
            approvedListenerTypes.add(ltype);
          }
        }
      };
      if (approvedListenerTypes.size() == 0)
        getToolkit().beep();
      else {
        lastMousePoint_ = f.componentLocationInBeanPaneSpace(listener_);
        lastMousePoint_.translate(listener_.getWidth() / 2, listener_
            .getHeight() / 2);
        f.repaint();
        //XXX different dialog if there's only one approvedListenerType?
        //XXX highlight the two beans?
        Class<?> chosenListenerType = (Class<?>) JOptionPane.showInputDialog(f, //Parent window
            "Register listener as type:", //Message
            "Listener type selection", //Dialog title
            JOptionPane.QUESTION_MESSAGE, //Message type
            null, //icon
            approvedListenerTypes.toArray(), //options
            approvedListenerTypes.get(0)); //default option
        if (chosenListenerType != null)
          f.addEventLink(source_, listener_, chosenListenerType);
      }
      f.repaint();
      source_ = listener_ = null;
      sourceBean_ = listenerBean_ = null;
      sourceInfo_ /*= listenerInfo_*/= null;
      lastMousePoint_ = null;
      setCurrentTool(defaultTool);
    };

    public void unselected(FormDesign f)
    {
      f.setCursor(Cursor.getDefaultCursor());
    };

    public void paint(Graphics g, FormDesign f)
    {
      if (source_ == null)
        return;
      Point sp = f.componentLocationInBeanPaneSpace(source_);
      g.setColor(Color.green);
      g.drawLine(sp.x + source_.getWidth() / 2, sp.y + source_.getHeight() / 2,
          lastMousePoint_.x, lastMousePoint_.y);
    };
  };

  /**
   * Tool for deleting event links.
   * @see ToolWindow.MakeEventLinkTool
   */
  protected class DeleteEventLinkTool extends Tool
  {
    public DeleteEventLinkTool()
    {
      //XXX change to use javabeancontext's getSystemResource instead of
      //    ClassLoader's?
      super(new ImageIcon(getToolkit().getImage(
          ClassLoader
              .getSystemResource("net/sourceforge/czt/animation/gui/design/"
                  + "deleteEventIcon.gif"))), "Delete Event",
          "Delete an event link", false);
    };

    public void selected(FormDesign f)
    {
      f.setEventLinkHighlightingOverride(true);
    };

    public void mouseMoved(MouseEvent e, FormDesign f)
    {
      for (BeanLink bl : f.getEventLinks()) {
        if (f.getVisualLine(bl).ptSegDist(e.getPoint()) < 5) {
          f.setCursor(Cursor.getDefaultCursor());
          return;
        };
      }
      f.setCursor(crossCursor);
    };

    public void mouseClicked(MouseEvent e, FormDesign f)
    {
      for (BeanLink bl : f.getEventLinks()) {
        if (f.getVisualLine(bl).ptSegDist(e.getPoint()) < 5) {
          f.removeEventLink(bl);
          setCurrentTool(defaultTool);
          return;
        };
      }
      getToolkit().beep();
      setCurrentTool(defaultTool);
    };

    public void unselected(FormDesign f)
    {
      f.setEventLinkHighlightingOverride(false);
      f.setCursor(Cursor.getDefaultCursor());
    };
  };

};

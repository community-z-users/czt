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

import java.awt.AWTKeyStroke;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Cursor;
import java.awt.FocusTraversalPolicy;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GridLayout;
import java.awt.KeyboardFocusManager;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.awt.geom.AffineTransform;
import java.awt.geom.Line2D;
import java.beans.BeanDescriptor;
import java.beans.Beans;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.beans.beancontext.BeanContext;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ActionMap;
import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.ButtonGroup;
import javax.swing.InputMap;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JLayeredPane;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.KeyStroke;
import javax.swing.OverlayLayout;
import javax.swing.WindowConstants;
import javax.swing.border.BevelBorder;
import javax.swing.border.Border;
import javax.swing.border.TitledBorder;
import javax.swing.event.EventListenerList;
import javax.swing.event.MouseInputAdapter;

import net.sourceforge.czt.animation.gui.Form;
import net.sourceforge.czt.animation.gui.FormEvent;
import net.sourceforge.czt.animation.gui.FormListener;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * Window for designing a form.
 * This class manages the placement of beans into a form, configuration of
 * properties, and linking of beans with events.
 */
public class FormDesign extends JFrame implements ToolChangeListener
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -6363568716435250126L;

/**
   * The form being designed by this window.
   */
  protected Form form;

  protected EventListenerList beanSelectedListeners = new EventListenerList();

  public void addBeanSelectedListener(BeanSelectedListener l)
  {
    if (getCurrentBean() != null)
      l.beanSelected(new BeanSelectedEvent(this, getCurrentBean()));
    beanSelectedListeners.add(BeanSelectedListener.class, l);
  };

  public void removeBeanSelectedListener(BeanSelectedListener l)
  {
    beanSelectedListeners.remove(BeanSelectedListener.class, l);
  };

  public BeanSelectedListener[] getBeanSelectedListeners()
  {
    return (BeanSelectedListener[]) beanSelectedListeners
        .getListeners(BeanSelectedListener.class);
  };

  protected void fireBeanSelected(Object bean)
  {
    final BeanSelectedListener[] listeners = getBeanSelectedListeners();
    final BeanSelectedEvent ev = new BeanSelectedEvent(this, bean);
    for (int i = 0; i < listeners.length; i++)
      listeners[i].beanSelected(ev);
  };

  public Form getForm()
  {
    return form;
  };

  /*private Point getCenter(Component c)
   {
   Point cp = componentLocationInBeanPaneSpace(c);
   return new Point(cp.x + c.getWidth() / 2, cp.y + c.getHeight() / 2);
   };*/

  private class FDGlassPane extends JPanel
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -7503034169683032338L;

	private int eventLinkHighlightingStatus;

    private int beanHighlightingStatus;

    public FDGlassPane(final DesignerCore desCore)
    {
      super(null);
      beanHighlightingStatus = desCore.getBeanHighlightingStatus();
      eventLinkHighlightingStatus = desCore.getEventLinkHighlightingStatus();
      final PropertyChangeListener gpRepaintPCListener = new PropertyChangeListener()
      {
        public void propertyChange(PropertyChangeEvent ev)
        {
          if (ev.getPropertyName().equals("beanHighlightingStatus"))
            beanHighlightingStatus = ((Integer) ev.getNewValue()).intValue();
          if (ev.getPropertyName().equals("eventLinkHighlightingStatus"))
            eventLinkHighlightingStatus = ((Integer) ev.getNewValue())
                .intValue();
          repaint();
        };
      };
      desCore.addPropertyChangeListener("beanHighlightingStatus",
          gpRepaintPCListener);
      desCore.addPropertyChangeListener("eventLinkHighlightingStatus",
          gpRepaintPCListener);
      desCore.addFormDesignListener(new FormDesignListener()
      {
        public void formCreated(FormDesignEvent ev)
        {
        };

        public void formDeleted(FormDesignEvent ev)
        {
          if (ev.getFormDesign() != FormDesign.this)
            return;
          desCore.removePropertyChangeListener("beanHighlightingStatus",
              gpRepaintPCListener);
          desCore.removePropertyChangeListener("eventLinkHighlightingStatus",
              gpRepaintPCListener);
          desCore.removeFormDesignListener(this);
        };
      });

    };

    public String getToolTipText(MouseEvent event)
    {
      if (eventLinkHighlightingStatus != DesignerCore.ELHS_HIGHLIGHT_NO_LINKS) {
        for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
          BeanLink bl =  i.next();
          if ((eventLinkHighlightingStatus & DesignerCore.ELHS_HIGHLIGHT_CURRENT_ALL_LINKS) != 0
              && bl.listener == getCurrentBean()
              || eventLinkHighlightingStatus == DesignerCore.ELHS_HIGHLIGHT_ALL_LINKS) {
            if (getVisualLine(bl).ptSegDist(event.getPoint()) < 5)
              return bl.listenerType.getName();
          }
        }
      }
      return null;
    };

    public void highlight(Component c, Graphics2D g)
    {
      Rectangle r = c.getBounds();
      r.setLocation(componentLocationInBeanPaneSpace(c));
      g.setColor(Color.yellow);
      g.draw(r);
    };

    public void highlight(BeanLink bl, Color c, Graphics2D g)
    {
      final Line2D.Double line = (Line2D.Double) getVisualLine(bl);
      final double lineLength = line.getP1().distance(line.getP2());
      final double arrowHeadLength = Math.min(10, lineLength);
      final double arrowHeadRatio = arrowHeadLength / lineLength;

      //Calculate the transformations for the arrow head.
      AffineTransform transform = AffineTransform.getTranslateInstance(
          -line.x2, -line.y2);
      transform.preConcatenate(AffineTransform.getScaleInstance(arrowHeadRatio,
          arrowHeadRatio));
      transform.preConcatenate(AffineTransform.getTranslateInstance(line.x2,
          line.y2));

      g.setColor(c);
      g.draw(line);
      AffineTransform saveAT = g.getTransform();

      //Draw one side of arrow head
      g.transform(transform);
      g.transform(AffineTransform.getRotateInstance(Math.PI / 12, line.x2,
          line.y2));
      g.draw(line);
      g.setTransform(saveAT);

      //Draw the other
      g.transform(transform);
      g.transform(AffineTransform.getRotateInstance(-Math.PI / 12, line.x2,
          line.y2));
      g.draw(line);
      g.setTransform(saveAT);
    };

    public void paintComponent(Graphics g1)
    {
      Graphics2D g = (Graphics2D) g1;

      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.paint(g, FormDesign.this);
      //Highlighting beans
      if (beanHighlightingStatus != DesignerCore.BHS_HIGHLIGHT_NO_BEANS) {
        Object[] beans = getForm().getBeans();
        //          Component[] comps = getBeanPane().getComponents();
        if (beanHighlightingStatus != DesignerCore.BHS_HIGHLIGHT_NO_BEANS)
          for (int i = 0; i < beans.length; i++) {
            if (beans[i] instanceof Component) {
              if ((beanHighlightingStatus & DesignerCore.BHS_HIGHLIGHT_COMPONENT_BEANS) != 0)
                highlight((Component) beans[i], g);
            }
            else {
              if ((beanHighlightingStatus & DesignerCore.BHS_HIGHLIGHT_NONVISUAL_BEANS) != 0)
                highlight(BeanWrapper.getComponent(beans[i]), g);
            }
          }

        //          if ((beanHighlightingStatus
        //               & DesignerCore.BHS_HIGHLIGHT_NONVISUAL_BEANS) != 0)
        //            for (int i = 0; i < comps.length; i++)
        //              if (comps[i] instanceof BeanWrapper)
        //                highlight(comps[i], g);
        //          comps = getForm().getComponents();
        //          if ((beanHighlightingStatus
        //               & DesignerCore.BHS_HIGHLIGHT_COMPONENT_BEANS) != 0) {
        //            highlight(getForm(), g);
        //            for (int i = 0; i < comps.length; i++)
        //              if (!(comps[i] instanceof BeanWrapper))
        //                highlight(comps[i], g);
        //          }
      }

      if (eventLinkHighlightingStatus != DesignerCore.ELHS_HIGHLIGHT_NO_LINKS
          || eventLinkHighlightingOverride) {
        for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
          BeanLink bl =  i.next();
          if (eventLinkHighlightingStatus == DesignerCore.ELHS_HIGHLIGHT_ALL_LINKS
              || eventLinkHighlightingOverride)
            highlight(bl, Color.red, g);
          else if ((eventLinkHighlightingStatus & DesignerCore.ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS) != 0
              && bl.listener == getCurrentBean())
            highlight(bl, Color.red, g);
          else if ((eventLinkHighlightingStatus & DesignerCore.ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS) != 0
              && bl.source == getCurrentBean())
            highlight(bl, Color.blue, g);
        }
      }
    };
  };

  /**
   * Glass pane to catch mouse events.
   * The glass pane is used to block interaction with the beans/components
   * being placed, and to draw handles and other guides on top of the form being
   * designed.<br/>
   * <em>Note:</em> This glass pane is not the glass pane in this frame's root
   * window.  It is part of a layered panel placed inside the contentPane.  This
   * is done because we don't want the glass pane to go over the menu bar, tool
   * bar, status bar, etc.
   */
  protected final JPanel glassPane;

  protected boolean eventLinkHighlightingOverride = false;

  public void setEventLinkHighlightingOverride(boolean o)
  {
    eventLinkHighlightingOverride = o;
    glassPane.repaint();
  };

  public Line2D getVisualLine(BeanLink l)
  {
    Component lsource = BeanWrapper.getComponent(l.source);
    Component llistener = BeanWrapper.getComponent(l.listener);
    Point sp = componentLocationInBeanPaneSpace(lsource);
    Point lp = componentLocationInBeanPaneSpace(llistener);
    return new Line2D.Double(sp.getX() + lsource.getWidth() / 2, sp.getY()
        + lsource.getHeight() / 2, lp.getX() + llistener.getWidth() / 2, lp
        .getY()
        + llistener.getHeight() / 2);
  };

  //XXX Should this be a set instead?
  protected Vector<BeanLink> eventLinks = new Vector<BeanLink>();

  public Vector<BeanLink> getEventLinks()
  {
    return new Vector<BeanLink>(eventLinks);
  };

  private void addEventLink(BeanLink bl)
  {
    if (!bl.listenerType.isInstance(bl.listener))
      throw new ClassCastException();
    if (!eventLinks.contains(bl)) //If it's already registered, don't add it.
      eventLinks.add(bl);
  };

  public void addEventLink(Component source, Component listener,
      Class<?> listenerType)
  {
    addEventLink(new BeanLink(BeanWrapper.getBean(source), BeanWrapper
        .getBean(listener), listenerType));
  };

  /**
   *
   * @param bl A BeanLink describing the link to remove.
   * @param i An iterator that has just read bl from eventLinks, or null if it
   *          wasn't reached via an iterator.  This is to get around the pesky
   *          <code>ConcurrentModificationException</code>.
   */
  private void removeEventLink(BeanLink bl, Iterator<?> i)
  {
    //Object sourceBean = bl.source;
    Object listenerBean = bl.listener;
    if (!bl.listenerType.isInstance(listenerBean))
      throw new ClassCastException();
    if (i == null)
      eventLinks.remove(bl);
    else
      i.remove();
  };

  public void removeEventLink(BeanLink bl)
  {
    removeEventLink(bl, null);
  };

  public void removeEventLinksToFrom(Object obj)
  {
    removeEventLinksTo(obj);
    removeEventLinksFrom(obj);
  };

  public void removeEventLinksTo(Object listener)
  {
    for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
      BeanLink bl = i.next();
      if (bl.listener == listener) {
        removeEventLink(bl, i);
      }
    };
  };

  public void removeEventLinksFrom(Object source)
  {
    for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
      BeanLink bl = i.next();
      if (bl.source == source) {
        removeEventLink(bl, i);
      }
    }
  };

  public void removeEventLinksTo(Object listener, Class<?> listenerType)
  {
    for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
      BeanLink bl = i.next();
      if (bl.listener == listener && bl.listenerType == listenerType) {
        removeEventLink(bl, i);
      }
    }
  };

  public void removeEventLinksFrom(Object source, Class<?> listenerType)
  {
    for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();) {
      BeanLink bl = i.next();
      if (bl.source == source && bl.listenerType == listenerType) {
        removeEventLink(bl, i);
      }
    }
  };

  /**
   * Action that makes visible, and raises a FormDesign window to the front.
   * Used by the entries in the Window menu.
   */
  private static class RaiseAction extends AbstractAction
      implements
        PropertyChangeListener
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 5105614330565272103L;
	private FormDesign fd_;

    public RaiseAction(FormDesign fd)
    {
      super(fd.getForm().getName());
      fd_ = fd;
      setValues();
      fd_.getForm().addPropertyChangeListener("name", this);
    };

    private void setValues()
    {
      putValue(Action.NAME, fd_.getForm().getName());
      putValue(Action.SHORT_DESCRIPTION, fd_.getForm().getName());
      putValue(Action.LONG_DESCRIPTION, fd_.getForm().getName());
    };

    public void actionPerformed(ActionEvent e)
    {
      fd_.setVisible(true);
      fd_.toFront();
    };

    public void propertyChange(PropertyChangeEvent evt)
    {
      setValues();
    };

    public boolean equals(Object obj)
    {
      if (obj instanceof RaiseAction)
        return ((RaiseAction) obj).fd_ == fd_;
      return false;
    };

    @SuppressWarnings("unused")
	public int hashCode(Object obj)
    {
      return fd_.hashCode();
    };
  };

  private final Action raiseAction;

  public Action getRaiseAction()
  {
    return raiseAction;
  };

  /**
   * The bean pane is used to contain the form being designed, and any beans
   * (wrapped) that do not visually appear within the form.
   */
  protected JPanel beanPane;

  public JPanel getBeanPane()
  {
    return beanPane;
  };

  /**
   * The actions provided by the user interface in this window.
   */
  protected final ActionMap actionMap = new ActionMap();

  /**
   * A map from key strokes to action keys for this window.
   */
  protected final InputMap inputMap = new InputMap();

  /**
   * Status bar for the FormDesign window.
   * Displays the selected bean name and class, and the current tool.
   */
  protected static class StatusBar extends JPanel
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -4334194925101490436L;
	private JLabel beanLabel_, toolLabel_;

    public StatusBar()
    {
      this(null, null);
    }

    public StatusBar(Object bean, ToolWindow.Tool tool)
    {
      setLayout(new GridLayout(1, 2));

      beanLabel_ = new JLabel();
      add(beanLabel_);
      Border blBorder = BorderFactory.createBevelBorder(BevelBorder.LOWERED);
      beanLabel_.setBorder(blBorder);

      toolLabel_ = new JLabel();
      add(toolLabel_);
      Border tlBorder = BorderFactory.createBevelBorder(BevelBorder.LOWERED);
      toolLabel_.setBorder(tlBorder);

      setBean(bean);
      setTool(tool);
    };

    public void setBean(Object bean)
    {
      String beanName;
      String beanTypeName;
      if (bean == null)
        beanName = beanTypeName = "(none)";
      else {
        if (IntrospectionHelper.beanHasReadableProperty(bean, "name")) {
          beanName = (String) IntrospectionHelper.getBeanProperty(bean, "name");
          if (beanName == null)
            beanName = "(unnamed)";
        }
        else
          beanName = "(unnamed)";
        Class<?> beanClass = bean.getClass();
        try {
          BeanDescriptor bd = Introspector.getBeanInfo(beanClass)
              .getBeanDescriptor();
          beanTypeName = bd.getDisplayName();
        } catch (IntrospectionException e) {
          beanTypeName = beanClass.getName();
        };
      }

      beanLabel_.setText("Current bean: " + beanName + " (" + beanTypeName
          + ")");
    };

    public void setTool(ToolWindow.Tool tool)
    {
      if (tool == null)
        toolLabel_.setText("Current tool: (none)");
      else
        toolLabel_.setText("Current tool: " + tool.getName());
    };
  };

  protected final StatusBar statusBar = new StatusBar();

  /**
   * The currently selected bean.
   */
  protected Object currentBean = null;

  protected Component currentComponent = null;

  public void unselectBean()
  {
    setCurrentBeanComponent(null);
  };

  protected PropertyChangeListener beanNameChangeListener = new PropertyChangeListener()
  {
    public void propertyChange(PropertyChangeEvent evt)
    {
      if (evt.getPropertyName().equals("name"))
        statusBar.setBean(getCurrentBean());
    };
  };

  /**
   * Setter method for the currentBean property.  Sets the currentBean property,
   * makes the resize handles visible for only the current bean.
   */
  public void setCurrentBeanComponent(Component t)
  {
    Object oldBean = currentBean;
    Component oldComponent = currentComponent;
    if (oldBean != null)
      IntrospectionHelper.removeBeanListener(oldBean,
          PropertyChangeListener.class, beanNameChangeListener);
    currentComponent = t;
    currentBean = BeanWrapper.getBean(currentComponent);

    if (currentBean != null) {
      fireBeanSelected(currentBean);
      IntrospectionHelper.addBeanListener(currentBean,
          PropertyChangeListener.class, beanNameChangeListener);
    }

    HandleSet hs;
    if (oldComponent != null) {
      hs = (HandleSet) handles.get(oldComponent);
      if (hs != null)
        hs.setBeanHandlesVisible(false);
    }
    if (currentComponent != null) {
      hs = (HandleSet) handles.get(currentComponent);
      hs.setLocation();
      if (hs != null)
        hs.setBeanHandlesVisible(true);
    }
    statusBar.setBean(getCurrentBean());
  };

  /**
   * Getter method for the currentBean property.
   */
  public Object getCurrentBean()
  {
    return currentBean;
  };

  public final boolean placementAllowed(Point location, Class<?> type)
  {
    return getForm().getBounds().contains(location) == Component.class
        .isAssignableFrom(type);
  };

  /**
   * @return the component associated with the created bean.
   */
  public Component addBean(Object bean, Point location)
      throws BeanOutOfBoundsException
  {
    if (!placementAllowed(location, bean.getClass()))
      throw new BeanOutOfBoundsException(bean.getClass(), location, form
          .getBounds());
    Component component = null;
    if (Beans.isInstanceOf(bean, Component.class)) {
      Component parent;
      component = (Component) bean;
      parent = lowestComponentAt(location);
      if (!(parent instanceof Container))
        parent = parent.getParent();
      location = translateCoordinateToCSpace(location, parent);
      component.setLocation(location);
      form.addBean((Component) bean, (Container) parent);
    }
    else {
      component = new BeanWrapper(bean);
      component.setLocation(location);
      getBeanPane().add(component);
      form.addBean(bean);
    }
    new HandleSet(component);
    setCurrentBeanComponent(component);
    return component;
  };

  public boolean removeCurrentBean()
  {
    return removeBean(getCurrentBeanComponent());
  };

  public boolean removeBean(Component beanComponent)
  {
    if (beanComponent == null)
      return false;
    if (beanComponent == getForm())
      return false;
    Object beanObject = BeanWrapper.getBean(beanComponent);
    if (beanComponent.getParent() == getBeanPane()) {
      getBeanPane().remove(beanComponent);
    }
    boolean result = getForm().removeBean(beanObject);
    //if (beanComponent==getCurrentBeanComponent())
    //  setCurrentBeanComponent(getForm());
    return result;
  };

  private final FormListener removalListener = new FormListener()
  {
    public void beanAdded(FormEvent e)
    {
    };

    public void beanRemoved(FormEvent e)
    {
      removeEventLinksToFrom(e.getBean());
      if (getCurrentBean() == e.getBean())
        setCurrentBeanComponent(getForm());
    };
  };

  /**
   * Getter method for the currentComponent property.
   * The currentComponent property is equal to the currentBean property if the
   * currentBean is a <code>Component</code>, otherwise it is a BeanWrapper
   * wrapping the currentBean.
   * @see net.sourceforge.czt.animation.gui.design.BeanWrapper
   */
  public Component getCurrentBeanComponent()
  {
    return currentComponent;
  };

  /**
   * The currently selected tool.  It is a BeanInfo describing the bean type to
   * place.
   */
  protected ToolWindow.Tool currentTool = null;

  public void toolChanged(ToolChangeEvent ev)
  {
    if (currentTool != null)
      currentTool.unselected(this);
    currentTool = ev.getTool();
    if (currentTool != null)
      currentTool.selected(this);
    statusBar.setTool(ev.getTool());
  };

  /**
   * Getter method for the currentTool property.
   */
  public ToolWindow.Tool getCurrentTool()
  {
    return currentTool;
  };

  private void registerAction(Action action, String name, KeyStroke key)
  {
    action.putValue(Action.NAME, name);
    action.putValue(Action.SHORT_DESCRIPTION, name);
    action.putValue(Action.LONG_DESCRIPTION, name);
    //XXX action.putValue(Action.SMALL_ICON,...);
    //XXX action.putValue(Action.ACTION_COMMAND_KEY,...);
    action.putValue(Action.ACCELERATOR_KEY, key);
    //XXX action.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put(name, action);
    inputMap.put(key, name);
  };

  protected void setupActions(ActionMap am, InputMap im,
      final DesignerCore desCore)
  {
    actionMap.setParent(am);
    inputMap.setParent(im);

    Action action_delete_form;
    action_delete_form = new AbstractAction("Delete Form")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 3903403283659546338L;

	public void actionPerformed(ActionEvent e)
      {
        int result = JOptionPane.showConfirmDialog(null,
            "This action will delete the current " + "form.\n"
                + "Are you sure you want to do this?",
            "Confirm delete this form.", JOptionPane.YES_NO_OPTION);
        if (result == JOptionPane.NO_OPTION)
          return;
        desCore.removeForm(FormDesign.this); //XXX prompt confirmation?
      };
    };
    registerAction(action_delete_form, "Delete Form", KeyStroke
        .getKeyStroke("control #")); //XXX

    Action action_delete_bean;
    action_delete_bean = new AbstractAction("Delete Current Bean")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 2995505038301887588L;

	public void actionPerformed(ActionEvent e)
      {
        if (getCurrentBean() != null)
          if (!removeCurrentBean())
            getToolkit().beep();
      };
    };
    registerAction(action_delete_bean, "Delete Current Bean", KeyStroke
        .getKeyStroke("DELETE"));

    Action action_down_bean;
    action_down_bean = new AbstractAction("Down Bean")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -2583484566930557210L;

	public void actionPerformed(ActionEvent e)
      {
        Container bp = getBeanPane();
        if (bp.getComponentCount() == 0) {
          setCurrentBeanComponent(null);
        }
        else if (getCurrentBeanComponent() == null) {
          setCurrentBeanComponent(bp.getComponent(0));
        }
        else {
          Component comp = getCurrentBeanComponent();
          if (comp instanceof Container
              && ((Container) comp).getComponentCount() > 0)
            setCurrentBeanComponent(((Container) comp).getComponent(0));
          else
            setCurrentBeanComponent(bp.getComponent(0));
        }
      };
    };
    registerAction(action_down_bean, "Down Bean", KeyStroke
        .getKeyStroke("SPACE"));
    inputMap.put(KeyStroke.getKeyStroke("control SPACE"), "Down Bean");

    Action action_up_bean;
    action_up_bean = new AbstractAction("Up Bean")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 5080644801640953278L;

	public void actionPerformed(ActionEvent e)
      {
        Container bp = getBeanPane();
        if (bp.getComponentCount() == 0) {
          setCurrentBeanComponent(null);
        }
        else if (getCurrentBeanComponent() == null) {
          setCurrentBeanComponent(bp.getComponent(0));
        }
        else {
          Container cont = getCurrentBeanComponent().getParent();
          if (cont != bp)
            setCurrentBeanComponent(cont);
        }
      };
    };
    registerAction(action_up_bean, "Up Bean", KeyStroke
        .getKeyStroke("shift SPACE"));
    inputMap.put(KeyStroke.getKeyStroke("control shift SPACE"), "Up Bean");

    Action action_next_bean;
    action_next_bean = new AbstractAction("Next Bean")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -3161253664494362266L;

	public void actionPerformed(ActionEvent e)
      {
        Container bp = getBeanPane();
        if (bp.getComponentCount() == 0) {
          setCurrentBeanComponent(null);
        }
        else if (getCurrentBeanComponent() == null) {
          setCurrentBeanComponent(bp.getComponent(0));
        }
        else {
          bp = getCurrentBeanComponent().getParent();
          for (int i = 0; i < bp.getComponentCount(); i++) {
            if (bp.getComponent(i) == getCurrentBeanComponent()) {
              setCurrentBeanComponent(bp.getComponent((i + 1)
                  % bp.getComponentCount()));
              break;
            }
          }
        }
      };
    };
    registerAction(action_next_bean, "Next Bean", KeyStroke.getKeyStroke("TAB"));
    inputMap.put(KeyStroke.getKeyStroke("control TAB"), "Next Bean");

    Action action_previous_bean;
    action_previous_bean = new AbstractAction("Previous Bean")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -3188247410256181475L;

	public void actionPerformed(ActionEvent e)
      {
        Container bp = getBeanPane();
        if (bp.getComponentCount() == 0) {
          setCurrentBeanComponent(null);
        }
        else if (getCurrentBeanComponent() == null) {
          setCurrentBeanComponent(bp.getComponent(0));
        }
        else {
          bp = getCurrentBeanComponent().getParent();
          for (int i = 0; i < bp.getComponentCount(); i++) {
            if (bp.getComponent(i) == getCurrentBeanComponent()) {
              int nextComponentNumber = (i + bp.getComponentCount() - 1)
                  % bp.getComponentCount();
              setCurrentBeanComponent(bp.getComponent(nextComponentNumber));
              break;
            }
          }
        }
      };
    };
    registerAction(action_previous_bean, "Previous Bean", KeyStroke
        .getKeyStroke("shift TAB"));
    inputMap.put(KeyStroke.getKeyStroke("control shift TAB"), "Previous Bean");
  };

  /**
   * Sets up the layering of {@link #glassPane glassPane} and
   * {@link #beanPane beanPane}.
   * Called once only from the constructor.
   */
  protected void setupLayeredPanes()
  {
    JLayeredPane layeredPane = new JLayeredPane();
    layeredPane.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    //layeredPane.setBorder(BorderFactory.createLineBorder(Color.black));
    layeredPane.setLayout(new OverlayLayout(layeredPane));

    //The input map attached to layeredPane will handle everything, so we don't
    //want focus to change to anything else.
    layeredPane.setFocusTraversalKeys(
        KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS,
        new HashSet<AWTKeyStroke>());
    layeredPane.setFocusTraversalKeys(
        KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS,
        new HashSet<AWTKeyStroke>());
    layeredPane.setFocusTraversalKeys(
        KeyboardFocusManager.UP_CYCLE_TRAVERSAL_KEYS,
        new HashSet<AWTKeyStroke>());
    layeredPane.setFocusTraversalPolicy(new FocusTraversalPolicy()
    {
      public Component getComponentAfter(Container focusCycleRoot,
          Component aComponent)
      {
        return null;
      };

      public Component getComponentBefore(Container focusCycleRoot,
          Component aComponent)
      {
        return null;
      };

      public Component getFirstComponent(Container focusCycleRoot)
      {
        return null;
      };

      public Component getLastComponent(Container focusCycleRoot)
      {
        return null;
      };

      public Component getDefaultComponent(Container focusCycleRoot)
      {
        return null;
      };

      public Component getInitialComponent(Window window)
      {
        return null;
      }
    });

    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(layeredPane, BorderLayout.CENTER);

    beanPane = new JPanel(null);
    beanPane.setFocusable(false);
    layeredPane.add(beanPane, new Integer(0));

    glassPane.setFocusable(false);
    glassPane.setOpaque(false);
    layeredPane.add(glassPane, new Integer(1));

    GPMouseListener gpml = new GPMouseListener();
    glassPane.addMouseListener(gpml);
    glassPane.addMouseMotionListener(gpml);

    layeredPane.setActionMap(actionMap);
    layeredPane.setInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,
        inputMap);
    layeredPane.setFocusable(true);
    layeredPane.requestFocusInWindow();
  };

  /**
   * Sets up the menu bar.  Called once only from the constructor.
   */
  protected void setupMenus(JMenu window)
  {
    JMenuBar mb = new JMenuBar();
    JMenu file = new JMenu("File");
    file.setMnemonic(KeyEvent.VK_F);
    file.add(new JMenuItem(actionMap.get("New Form")));
    file.add(new JMenuItem(actionMap.get("Delete Form")));
    file.addSeparator();
    file.add(new JMenuItem(actionMap.get("Save...")));
    file.add(new JMenuItem(actionMap.get("Open...")));
    file.add(new JMenuItem(actionMap.get("Import...")));
    file.addSeparator();
    file.add(new JMenuItem(actionMap.get("Quit")));
    JMenu edit = new JMenu("Edit");
    edit.setMnemonic(KeyEvent.VK_E);
    edit.add(new JMenuItem(actionMap.get("Delete Current Bean")));
    edit.add(new JMenuItem(actionMap.get("Show Properties Window")));
    JMenu view = new JMenu("View");
    view.setMnemonic(KeyEvent.VK_V);

    JMenu view_highlight_beans_menu = new JMenu("Highlight Beans");
    ButtonGroup view_highlight_beans = new ButtonGroup();
    JRadioButtonMenuItem rbmi = new JRadioButtonMenuItem(actionMap
        .get("Highlight All Beans"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight Components"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight Non-visual Beans"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Don't Highlight Beans"));
    rbmi.setSelected(true);
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    view.add(view_highlight_beans_menu);

    JMenu view_highlight_links_menu = new JMenu("Highlight Event Links");
    ButtonGroup view_highlight_links = new ButtonGroup();
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight All Event Links"));
    rbmi.setSelected(true);
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's "
        + "Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's "
        + "Incoming Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's "
        + "Outgoing Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi = new JRadioButtonMenuItem(actionMap
        .get("Don't Highlight Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    view.add(view_highlight_links_menu);

    JMenu help = new JMenu("Help");
    help.setMnemonic(KeyEvent.VK_H);
    help.add(new JMenuItem(actionMap.get("About...")));
    help.add(new JMenuItem(actionMap.get("License...")));
    mb.add(file);
    mb.add(edit);
    mb.add(view);
    mb.add(window);
    mb.add(Box.createHorizontalGlue());
    mb.add(help);
    setJMenuBar(mb);
  };

  /**
   * Sets up the status bar.  Called once only from the constructor.
   */
  protected void setupStatusBar()
  {
    statusBar.setFocusable(false);
    getContentPane().add(statusBar, BorderLayout.SOUTH);
  };

  /**
   * Creates a new Form designer.
   */
  public FormDesign(ActionMap am, InputMap im, JMenu wm, DesignerCore dc)
  {
    this("Main", am, im, wm, dc);
  };

  public FormDesign(String name, ActionMap am, InputMap im, JMenu windowMenu,
      DesignerCore desCore)
  {
    this(new Form(name), am, im, windowMenu, desCore);
    form.setBounds(5, 5, 100, 100);
  };

  public FormDesign(Form _form, ActionMap am, InputMap im, JMenu windowMenu,
      final DesignerCore desCore)
  {
    super("Design Mode: " + _form.getName());
    setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);

    glassPane = new FDGlassPane(desCore);
    //Necessary because getToolTipText(MouseEvent) won't be used otherwise
    glassPane.setToolTipText("");

    setupActions(am, im, desCore);
    setupLayeredPanes();
    setupMenus(windowMenu);
    setupStatusBar();
    handles = new HashMap<Object, HandleSet>();

    form = _form;
    form.addPropertyChangeListener("name", new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent evt)
      {
        setTitle("Design Mode: " + form.getName());
      };
    });

    Border lineBorder = BorderFactory.createLineBorder(Color.black);
    form
        .setBorder(BorderFactory.createTitledBorder(lineBorder, form.getName()));
    form.addPropertyChangeListener("name", new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent evt)
      {
        //XXX It seems that Component/JComponent etc, don't send an event when
        //    'name' changes!  Should find a solution that will work.  At
        //    present it is fixed with a nasty hack in PropertiesWindow.java
        //    that sends the PropertyChangeEvents on behalf of the Component
        TitledBorder border = (TitledBorder) ((Form) evt.getSource())
            .getBorder();
        border.setTitle((String) evt.getNewValue());
        //XXX could this be narrowed to just repaint the border?
        ((Form) evt.getSource()).repaint();
      };
    });
    form.addFormListener(removalListener);

    getBeanPane().add(form);
    new HandleSet(form);
    setCurrentBeanComponent(form);
    raiseAction = new RaiseAction(this);
  };

public static FormDesign loadDesign(XMLDecoder decoder, ActionMap am,
      InputMap im, JMenu windowMenu, DesignerCore desCore)
  {
    Form form;
    form = (Form) decoder.readObject();
    @SuppressWarnings("unchecked")
	Vector<BeanWrapper> beanWrappers = (Vector<BeanWrapper>) decoder.readObject();
    @SuppressWarnings("unchecked")
    Vector<BeanLink> eventLinks = (Vector<BeanLink>) decoder.readObject();

    FormDesign fd = new FormDesign(form, am, im, windowMenu, desCore);

    for (@SuppressWarnings("unchecked")
	Iterator<? extends Component> it = ((BeanContext) form.getBeanContextProxy()).iterator(); it
        .hasNext();)
      try { //Add handle sets for all of the beans already added into the form.
        fd.newHandleSet(it.next());
      } catch (ClassCastException ex) {
        //Ignore exceptions from trying to cast for non-component beans.
      };

    for (Iterator<BeanLink> i = eventLinks.iterator(); i.hasNext();)
      fd.addEventLink( i.next());
    for (Iterator<BeanWrapper> i = beanWrappers.iterator(); i.hasNext();) {
      BeanWrapper bw = i.next();
      fd.getBeanPane().add(bw);
      fd.newHandleSet(bw);
    };
    fd.setVisible(form.getStartsVisible());
    return fd;
  };

  public void saveDesign(XMLEncoder encoder)
  {
    encoder.writeObject(form);

    Component[] components = getBeanPane().getComponents();
    Vector<Component> beanWrappers = new Vector<Component>();
    for (int i = 0; i < components.length; i++)
      if (components[i] instanceof BeanWrapper)
        beanWrappers.add(components[i]);
    encoder.writeObject(beanWrappers);
    encoder.writeObject(eventLinks);
  };

  /**
   * Mapping from beans in the design to their set of handles.
   */
  protected Map<Object, HandleSet> handles; //from bean to handles

  private void newHandleSet(final Component bean)
  {
    new HandleSet(bean);
  };

  /**
   * Class collecting together the eight resize handle, and one move handle
   * belonging to a bean.
   */
  protected class HandleSet
  {
    /**
     * The corner and edge resize handles.  These appear as squares on the
     * corners and edges of a bean.
     */
    public BeanHandle n, ne, e, se, s, sw, w, nw, move;

    /**
     * Creates a HandleSet, all of the handles that go in it, and a mouse
     * adapter that sets the current bean when it is clicked on.
     */
    public HandleSet(final Component bean)
    {
      se = new BeanHandle(bean, Cursor.SE_RESIZE_CURSOR, FormDesign.this);
      s = new BeanHandle(bean, Cursor.S_RESIZE_CURSOR, FormDesign.this);
      e = new BeanHandle(bean, Cursor.E_RESIZE_CURSOR, FormDesign.this);
      sw = new BeanHandle(bean, Cursor.SW_RESIZE_CURSOR, FormDesign.this);
      ne = new BeanHandle(bean, Cursor.NE_RESIZE_CURSOR, FormDesign.this);
      n = new BeanHandle(bean, Cursor.N_RESIZE_CURSOR, FormDesign.this);
      w = new BeanHandle(bean, Cursor.W_RESIZE_CURSOR, FormDesign.this);
      nw = new BeanHandle(bean, Cursor.NW_RESIZE_CURSOR, FormDesign.this);
      move = new BeanHandle(bean, Cursor.MOVE_CURSOR, FormDesign.this);
      glassPane.add(se);
      glassPane.add(s);
      glassPane.add(e);
      glassPane.add(sw);
      glassPane.add(ne);
      glassPane.add(n);
      glassPane.add(w);
      glassPane.add(nw);
      glassPane.add(move);
      handles.put(bean, this);
      setBeanHandlesVisible(false);
    };

    /**
     * Calls setVisible on all of the BeanHandles.
     */
    public void setBeanHandlesVisible(boolean b)
    {
      n.setVisible(b);
      ne.setVisible(b);
      e.setVisible(b);
      se.setVisible(b);
      s.setVisible(b);
      sw.setVisible(b);
      w.setVisible(b);
      nw.setVisible(b);
      move.setVisible(b);
    };

    public void setLocation()
    {
      n.setLocation();
      ne.setLocation();
      e.setLocation();
      se.setLocation();
      s.setLocation();
      sw.setLocation();
      w.setLocation();
      nw.setLocation();
      move.setLocation();
    };
  };

  /**
   * Mouse listener for the {@link #glassPane glass pane}.
   * Used mostly for creation of beans when the user clicks or drags directly
   * on the glass pane.
   */
  protected class GPMouseListener extends MouseInputAdapter
  {
    public void mouseClicked(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseClicked(e, FormDesign.this);
    };

    public void mousePressed(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mousePressed(e, FormDesign.this);
    };

    public void mouseReleased(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseReleased(e, FormDesign.this);
    };

    public void mouseEntered(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseEntered(e, FormDesign.this);
    };

    public void mouseExited(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseExited(e, FormDesign.this);
    };

    public void mouseDragged(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseDragged(e, FormDesign.this);
    };

    public void mouseMoved(MouseEvent e)
    {
      ToolWindow.Tool t = getCurrentTool();
      if (t != null)
        t.mouseMoved(e, FormDesign.this);
    };
  };

  /**
   * Translates a coordinate described in a coordinate space that is a
   * descendant of this <code>FormDesign</code> to the same coordinate relative
   * to the <code>beanPane</code>'s coordinate space.
   * @param oldPoint the coordinate to translate.
   * @param initialCSpace container with coordinate space to which
   *                      <code>point</code> is relative.
   * @return the transformed coordinate.
   *         <code>null</code> if initialCSpace is not a
   *         descendant of <code>beanPane</code>.
   */
  public Point translateCoordinateFromCSpace(Point oldPoint,
                                             Component initialCSpace)
  {
    Point point = new Point(oldPoint);
    Component cSpace = initialCSpace;
    for (; cSpace != beanPane; cSpace = cSpace.getParent())
      if (cSpace == null)
        return null;
      else
        point.translate(cSpace.getX(), cSpace.getY());
    return point;
  };

  /**
   * Uses <code>translateCoordinateFromCSpace</code> to give the location of a
   * component in the <code>beanPane</code>'s coordinate space.
   * @param component the component whose location will be found.
   * @return the location of the component in the <code>beanPane</code>'s
   *         coordinate space.
   */
  public Point componentLocationInBeanPaneSpace(Component component)
  {
    return translateCoordinateFromCSpace(component.getLocation(), component
        .getParent());
  };

  /**
   * Translates a coordinate relative to the <code>beanPane</code>'s coordinate
   * space into the same coordinate relative to the coordinate space belonging
   * to <code>cSpace</code>.
   * @param point the coordinate to translate.
   * @param cSpace container with coordinate space to which <code>point</code>
   *        will be translated.
   * @return the transformed coordinate.  <code>null</code> if cSpace is not a
   *         descendant of <code>beanPane</code>.  NOTE: The coordinate may lay
   *         outside the bounds of the container.
   */
  public Point translateCoordinateToCSpace(Point point, Component cSpace)
  {
    point = new Point(point);
    for (; cSpace != beanPane; cSpace = cSpace.getParent())
      if (cSpace == null)
        return null;
      else
        point.translate(-cSpace.getX(), -cSpace.getY());
    return point;
  };

  public void setCursor(Cursor cursor) //XXX not particularly nice.
  {
    glassPane.setCursor(cursor);
  };

  public Component lowestComponentAt(Point p)
  {
    Component c, c2 = getBeanPane();
    do {
      c = c2;
      c2 = c.getComponentAt(translateCoordinateToCSpace(p, c));
    } while (c != c2 && c2 != null);
    if (c2 == getBeanPane())
      return null;
    return c2;
  };
};

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
package czt.animation.gui.design;

import czt.animation.gui.Form;            import czt.animation.gui.util.IntrospectionHelper;
import czt.animation.gui.persistence.delegates.BeanLinkDelegate;

import java.awt.BorderLayout;             import java.awt.Color;
import java.awt.Component;                import java.awt.Container;
import java.awt.Cursor;                   import java.awt.FocusTraversalPolicy;
import java.awt.Graphics;                 import java.awt.GridLayout;
import java.awt.KeyboardFocusManager;     import java.awt.Point;
import java.awt.Rectangle;                import java.awt.Window;
import java.awt.event.ActionEvent;        import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent; 
import java.awt.Graphics2D;                 
import java.awt.geom.Line2D;


import java.beans.Beans;                  import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;                import java.beans.Expression;
import java.beans.IntrospectionException; import java.beans.Introspector;           
import java.beans.PropertyChangeEvent;    import java.beans.PropertyChangeListener; 
import java.beans.XMLDecoder;             import java.beans.XMLEncoder;

import java.beans.beancontext.BeanContext;

import java.io.IOException;

import java.util.Arrays;                  import java.util.Collections;
import java.util.EventListener;           import java.util.HashMap;
import java.util.Iterator;                import java.util.Map;
import java.util.Vector;

import javax.swing.AbstractAction;        import javax.swing.Action;
import javax.swing.ActionMap;             import javax.swing.BorderFactory;
import javax.swing.Box;                   import javax.swing.ButtonGroup;
import javax.swing.InputMap;              import javax.swing.JComponent;
import javax.swing.JFrame;                import javax.swing.JLabel;
import javax.swing.JLayeredPane;          import javax.swing.JMenuBar;
import javax.swing.JPanel;                import javax.swing.JRadioButtonMenuItem;
import javax.swing.JMenu;                 import javax.swing.JMenuItem;
import javax.swing.JOptionPane;           import javax.swing.JToolTip;              
import javax.swing.KeyStroke;             import javax.swing.OverlayLayout;
import javax.swing.WindowConstants;

import javax.swing.border.BevelBorder;    import javax.swing.border.TitledBorder;

import javax.swing.event.EventListenerList;  import javax.swing.event.MouseInputAdapter;

/**
 * Window for designing a form.
 * This class manages the placement of beans into a form, configuration of properties, and linking of 
 * beans with events.
 */
public class FormDesign extends JFrame implements ToolChangeListener {
  protected EventListenerList beanSelectedListeners=new EventListenerList();
  public void addBeanSelectedListener(BeanSelectedListener l) {
    if(getCurrentBean()!=null) 
      l.beanSelected(new BeanSelectedEvent(this,getCurrentBean()));
    beanSelectedListeners.add(BeanSelectedListener.class, l);
  };
  public void removeBeanSelectedListener(BeanSelectedListener l) {
    beanSelectedListeners.remove(BeanSelectedListener.class, l);
  };
  public BeanSelectedListener[] getBeanSelectedListeners() {
    return (BeanSelectedListener[])beanSelectedListeners.getListeners(BeanSelectedListener.class);
  };
  protected void fireBeanSelected(Object bean) {
    final BeanSelectedListener[] listeners=getBeanSelectedListeners();
    final BeanSelectedEvent ev=new BeanSelectedEvent(this,bean);
    for(int i=0;i<listeners.length;i++) listeners[i].beanSelected(ev);
  };

  /**
   * The form being designed by this window
   */
  protected Form form;
  
  public Form getForm() {
    return form;
  };
  
  private Point getCenter(Component c) {
    Point cp=componentLocationInBeanPaneSpace(c);
    return new Point(cp.x+c.getWidth()/2,cp.y+c.getHeight()/2);
  };
      
  /**
   * Glass pane to catch mouse events.
   * The glass pane is used to block interaction with the beans/components being placed, and to draw
   * handles and other guides on top of the form being designed.<br>
   * <em>Note:</em> This glass pane is not the glass pane in this frame's root window.  It is part of a
   * layered panel placed inside the contentPane.  This is done because we don't want the glass pane to
   * go over the menu bar, tool bar, status bar, etc.
   */
  protected JPanel glassPane=new JPanel(null) {
      public String getToolTipText(MouseEvent event) {
	if(eventLinkHighlightingStatus!=ELHS_HIGHLIGHT_NO_LINKS) {
	  for(Iterator i=eventLinks.iterator();i.hasNext();) {
	    BeanLink bl=(BeanLink)i.next();
	    if((eventLinkHighlightingStatus&ELHS_HIGHLIGHT_CURRENT_ALL_LINKS)!=0
	       && bl.listener==getCurrentBeanComponent()
	       || eventLinkHighlightingStatus==ELHS_HIGHLIGHT_ALL_LINKS) {
	      if(getVisualLine(bl).ptLineDist(event.getPoint())<5)
		return bl.listenerType.getName();
	    }
	  }
	}
	return null;
      };
      
      public void highlight(Component c, Graphics2D g) {
	Rectangle r=c.getBounds();
	r.setLocation(componentLocationInBeanPaneSpace(c));
	g.setColor(Color.yellow);
	g.draw(r);
      };
      
      public void highlight(BeanLink bl, Color c, Graphics2D g) {
	g.setColor(c);
	g.draw(getVisualLine(bl));
      };
      
      public void paintComponent(Graphics g1) {
	Graphics2D g=(Graphics2D)g1;
	
	ToolWindow.Tool t=getCurrentTool();
	if(t!=null)t.paint(g,FormDesign.this);
	//Highlighting beans
	if(beanHighlightingStatus!=BHS_HIGHLIGHT_NO_BEANS) {
	  Component[] comps=getBeanPane().getComponents();
	  if((beanHighlightingStatus&BHS_HIGHLIGHT_NONVISUAL_BEANS)!=0)
	    for(int i=0;i<comps.length;i++)
	      if(comps[i] instanceof BeanWrapper)
		highlight(comps[i],g);
	  comps=getForm().getComponents();
	  if((beanHighlightingStatus&BHS_HIGHLIGHT_COMPONENT_BEANS)!=0) {
	    highlight(getForm(),g);
	    for(int i=0;i<comps.length;i++)
	      if(!(comps[i] instanceof BeanWrapper))
		highlight(comps[i],g); 
	  }
	}
	
	if(eventLinkHighlightingStatus!=ELHS_HIGHLIGHT_NO_LINKS || eventLinkHighlightingOverride) {
	  for(Iterator i=eventLinks.iterator();i.hasNext();) {
	    BeanLink bl=(BeanLink)i.next();
	    if(eventLinkHighlightingStatus==ELHS_HIGHLIGHT_ALL_LINKS||eventLinkHighlightingOverride)
	      highlight(bl,Color.red,g);
	    else if((eventLinkHighlightingStatus&ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS)!=0
		    && bl.listener==getCurrentBeanComponent())
	      highlight(bl,Color.red,g);
	    else if((eventLinkHighlightingStatus&ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS)!=0
		    && bl.source==getCurrentBeanComponent())
	      highlight(bl,Color.blue,g);
	  }
	}
      };
    };
  
  protected int beanHighlightingStatus=BHS_HIGHLIGHT_NO_BEANS;
  protected final static int BHS_HIGHLIGHT_NO_BEANS=0;
  protected final static int BHS_HIGHLIGHT_COMPONENT_BEANS=1;
  protected final static int BHS_HIGHLIGHT_NONVISUAL_BEANS=2;
  protected final static int BHS_HIGHLIGHT_ALL_BEANS=BHS_HIGHLIGHT_COMPONENT_BEANS
                                                    |BHS_HIGHLIGHT_NONVISUAL_BEANS;
  
  protected int eventLinkHighlightingStatus=ELHS_HIGHLIGHT_NO_LINKS;
  protected final static int ELHS_HIGHLIGHT_NO_LINKS=0;
  protected final static int ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS=1;
  protected final static int ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS=2;
  protected final static int ELHS_HIGHLIGHT_CURRENT_ALL_LINKS=3;
  protected final static int ELHS_HIGHLIGHT_ALL_LINKS=4;
  protected boolean eventLinkHighlightingOverride=false;
  public void setEventLinkHighlightingOverride(boolean o) {
    eventLinkHighlightingOverride=o;
    glassPane.repaint();
  };
  
  
  public static class BeanLink {
    public final Component source, listener;
    public final Class listenerType;
    public BeanLink(Component source, Component listener, Class listenerType) {
      this.source=source;this.listener=listener;this.listenerType=listenerType;
    };
    public boolean equals(Object obj) {
      if(!(obj instanceof BeanLink)) return false;
      BeanLink bl=(BeanLink)obj;
      return bl.source==source&&bl.listener==listener&&bl.listenerType.equals(listenerType);
    };    
  };

  static {
    BeanLinkDelegate.registerDelegate();
  };
  
  
  public Line2D getVisualLine(BeanLink l) {
    Point sp=componentLocationInBeanPaneSpace(l.source);
    Point lp=componentLocationInBeanPaneSpace(l.listener);
    return new Line2D.Double(sp.getX()+  l.source.getWidth()/2, sp.getY()+  l.source.getHeight()/2,
			     lp.getX()+l.listener.getWidth()/2, lp.getY()+l.listener.getHeight()/2);  
  };

  protected Vector eventLinks=new Vector/*<BeanLink>*/();  //XXX Should this be a set instead?
  public Vector getEventLinks() {
    return new Vector(eventLinks);
  };
  private void addEventLink(BeanLink bl) {
    Object sourceBean=BeanWrapper.getBean(bl.source);
    Object listenerBean=BeanWrapper.getBean(bl.listener);
    if(!bl.listenerType.isInstance(listenerBean)) throw new ClassCastException();
    if(eventLinks.contains(bl)) return;//If it's already registered, don't add it.
    //The extra check below to see if it is registered with the bean already is mostly to prevent it
    //being registered twice, because when XMLEncoder saves a file, it saves its listeners, and 
    //XMLDecoder loads them (before we get to the BeanLinks).
    //XXX A nicer solution to this issue should be found.
    if(!Arrays.asList(IntrospectionHelper.getBeanListeners(sourceBean,bl.listenerType))
       .contains(listenerBean)) {
      if(IntrospectionHelper.addBeanListener(sourceBean,bl.listenerType,listenerBean))
	eventLinks.add(bl);
    } else eventLinks.add(bl);
  };
  
  public void addEventLink(Component source, Component listener, Class listenerType) {
    addEventLink(new BeanLink(source,listener,listenerType));
  };
  /**
   *
   * @param bl A BeanLink describing the link to remove.
   * @param i An iterator that has just read bl from eventLinks, or null if it wasn't reached via an 
   *          iterator.  This is to get around the pesky ConcurrentModificationException.
   */
  private void removeEventLink(BeanLink bl, Iterator i) {
    Object sourceBean=BeanWrapper.getBean(bl.source);
    Object listenerBean=BeanWrapper.getBean(bl.listener);
    if(!bl.listenerType.isInstance(listenerBean)) throw new ClassCastException();
    IntrospectionHelper.removeBeanListener(sourceBean,bl.listenerType,listenerBean);
    if(i==null) eventLinks.remove(bl);    
    else i.remove();
  };
  public void removeEventLink(BeanLink bl) {
    removeEventLink(bl,null);
  };
  public void removeEventLink(Component source, Component listener, Class listenerType) {
    removeEventLink(new BeanLink(source,listener,listenerType));
  };
  public void removeEventLinksToFrom(Component obj) {
    removeEventLinksTo(obj);
    removeEventLinksFrom(obj);
  };
  public void removeEventLinksTo(Component listener) {
    for(Iterator i=eventLinks.iterator();i.hasNext();) {
      BeanLink bl=(BeanLink)i.next();
      if(bl.listener==listener) {      
	removeEventLink(bl,i);
      }
    };
  };
  public void removeEventLinksFrom(Component source) {
    for(Iterator i=eventLinks.iterator();i.hasNext();) {
      BeanLink bl=(BeanLink)i.next();
      if(bl.source==source) {      
	removeEventLink(bl,i);
      }
    }
  };
  public void removeEventLinksTo(Component listener, Class listenerType) {
    for(Iterator i=eventLinks.iterator();i.hasNext();) {
      BeanLink bl=(BeanLink)i.next();
      if(bl.listener==listener && bl.listenerType==listenerType) {      
	removeEventLink(bl,i);
      }
    }
  };
  public void removeEventLinksFrom(Component source, Class listenerType) {
    for(Iterator i=eventLinks.iterator();i.hasNext();) {
      BeanLink bl=(BeanLink)i.next();
      if(bl.source==source && bl.listenerType==listenerType) {      
	removeEventLink(bl,i);
      }
    }
  };
  
  
  private static class RaiseAction extends AbstractAction implements PropertyChangeListener{
    private FormDesign fd;
    private void setValues() {
      putValue(Action.NAME,fd.getForm().getName());
      putValue(Action.SHORT_DESCRIPTION,fd.getForm().getName());
      putValue(Action.LONG_DESCRIPTION,fd.getForm().getName());
    };
    
    public RaiseAction(FormDesign fd) {
      super(fd.getForm().getName());
      this.fd=fd;
      setValues();
      fd.getForm().addPropertyChangeListener("name",this);
    };
    public void actionPerformed(ActionEvent e) {
      fd.setVisible(true);
      fd.toFront();
    };
    public void propertyChange(PropertyChangeEvent evt) {
      setValues();
    };
    public boolean equals(Object obj) {
      if(obj instanceof RaiseAction)
	return ((RaiseAction)obj).fd==fd;
      return false;
    };
  };
  private final Action raiseAction;
  public Action getRaiseAction() {return raiseAction;};
  
  
  /**
   * The bean pane is used to contain the form being designed, and any beans (wrapped) that do not
   * visually appear within the form.
   */
  protected JPanel beanPane;
  public JPanel getBeanPane() {return beanPane;};
  
  /**
   * The actions provided by the user interface in this window.
   */
  protected final ActionMap actionMap=new ActionMap();
  /**
   * A map from key strokes to action keys for this window.
   */
  protected final InputMap inputMap=new InputMap();

  protected static class StatusBar extends JPanel {
    private JLabel beanLabel, toolLabel;
    public StatusBar() {
      this(null,null);
    }
    public StatusBar(Object bean, ToolWindow.Tool tool) {
      setLayout(new GridLayout(1,2));
      add(beanLabel=new JLabel());
      add(toolLabel=new JLabel());
      beanLabel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      toolLabel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      setBean(bean);
      setTool(tool);
    };
    public void setBean(Object bean) {
      String beanName;String beanTypeName;
      if(bean==null) beanName=beanTypeName="(none)";
      else {
	if(IntrospectionHelper.beanHasReadableProperty(bean,"name")) { 
	  beanName=(String)IntrospectionHelper.getBeanProperty(bean,"name");
	  if(beanName==null) 
	    beanName="(unnamed)";
	} else
	  beanName="(unnamed)";
	try {
	  beanTypeName=Introspector.getBeanInfo(bean.getClass()).getBeanDescriptor().getDisplayName();
	} catch (IntrospectionException e) {
	  beanTypeName=bean.getClass().getName();
	};
      }
      
      beanLabel.setText("Current bean: "+beanName+" ("+beanTypeName+")");
    };
    public void setTool(ToolWindow.Tool tool) {
      toolLabel.setText("Current tool: "+(tool==null?"(none)":tool.getName()));
    };
  };
  protected final StatusBar statusBar=new StatusBar();

  /**
   * The currently selected bean.
   */
  protected Object currentBean=null;
  protected Component currentComponent=null;
  public void unselectBean() {setCurrentBeanComponent(null);};
  

  protected PropertyChangeListener beanNameChangeListener=new PropertyChangeListener() {
      public void propertyChange(PropertyChangeEvent evt) {
	if(evt.getPropertyName().equals("name"))
	   statusBar.setBean(getCurrentBean());
      };
    };
  
  /**
   * Setter method for the currentBean property.  Sets the currentBean property, makes the resize 
   * handles visible for only the current bean.
   */  
  public void setCurrentBeanComponent(Component t) {
    Object oldBean=currentBean;
    Component oldComponent=currentComponent;
    if(oldBean!=null)
      IntrospectionHelper.removeBeanListener(oldBean,PropertyChangeListener.class, 
					     beanNameChangeListener);
    currentComponent=t;
    currentBean=BeanWrapper.getBean(currentComponent);
    
    if(currentBean!=null) {
      fireBeanSelected(currentBean);
      IntrospectionHelper.addBeanListener(currentBean,PropertyChangeListener.class,
					  beanNameChangeListener);
    }
    
    HandleSet hs;
    if(oldComponent!=null) {
      hs=(HandleSet)handles.get(oldComponent);
      if(hs!=null) hs.setBeanHandlesVisible(false);
    }
    if(currentComponent!=null) {
      hs=(HandleSet)handles.get(currentComponent);
      hs.setLocation();
      if(hs!=null) hs.setBeanHandlesVisible(true);
    }
    statusBar.setBean(getCurrentBean());
  };
  /**
   * Getter method for the currentBean property.
   */
  public Object getCurrentBean() {
    return currentBean;
  };
  public final boolean placementAllowed(Point location, Class type) {
    return getForm().getBounds().contains(location)==Component.class.isAssignableFrom(type);
  };

  /**
   * @return the component associated with the created bean.
   */
  public Component addBean(Object bean, Point location) throws BeanOutOfBoundsException {
    if(!placementAllowed(location,bean.getClass())) 
      throw new BeanOutOfBoundsException(bean.getClass(),location,form.getBounds());
    Component component=null;
    if(Beans.isInstanceOf(bean,Component.class)) {
      component=(Component) bean;
      location=translateCoordinateToCSpace(location,form);
    } else {
      component=new BeanWrapper(bean);
      getBeanPane().add(component);
    }
    component.setLocation(location);
    form.addBean(bean);
    new HandleSet(component);
    setCurrentBeanComponent(component);
    return component;
  };
  
  public boolean removeCurrentBean() {
    return removeBean(getCurrentBeanComponent());
  };
  public boolean removeBean(Component beanComponent) {
    if(beanComponent==null) return false;
    if(beanComponent==getForm()) return false;
    Object beanObject=BeanWrapper.getBean(beanComponent);
    if(beanComponent.getParent()==getBeanPane()) {
      getBeanPane().remove(beanComponent);
    }
    boolean result=getForm().removeBean(beanObject);
    if(beanComponent==getCurrentBeanComponent()) setCurrentBeanComponent(getForm());
    if(result) removeEventLinksToFrom(beanComponent);
    return result;
  };
  
  /**
   * Getter method for the currentComponent property.
   * The currentComponent property is equal to the currentBean property if the currentBean is a 
   * Component, otherwise it is a BeanWrapper wrapping the currentBean.
   * @see czt.animation.gui.design.BeanWrapper
   */
  public Component getCurrentBeanComponent() {
    return (Component)currentComponent;
  };
  
  /**
   * The currently selected tool.  It is a BeanInfo describing the bean type to place.
   */
  protected ToolWindow.Tool currentTool=null;
  public void toolChanged(ToolChangeEvent ev) {
    if(currentTool!=null) currentTool.unselected(this);
    currentTool=ev.getTool();
    if(currentTool!=null) currentTool.selected(this);
    statusBar.setTool(ev.getTool());
  };


  /**
   * Getter method for the currentTool property.
   */
  public ToolWindow.Tool getCurrentTool() {
    return currentTool;
  };
  
  protected void setupActions(ActionMap am, InputMap im, final DesignerCore desCore) {
    actionMap.setParent(am);
    inputMap.setParent(im);
    
    Action action_delete_form;
    action_delete_form=new AbstractAction("Delete Form") {
	public void actionPerformed(ActionEvent e) {
	  if(JOptionPane.showConfirmDialog(null,
					   "This action will delete the current form.\n"
					   +"Are you sure you want to do this?",
					   "Confirm delete this form.",
					   JOptionPane.YES_NO_OPTION)==JOptionPane.NO_OPTION)
	    return;
	  desCore.removeForm(FormDesign.this);//XXX prompt confirmation?
	};
      };
    action_delete_form.putValue(Action.NAME,"Delete Form");
    action_delete_form.putValue(Action.SHORT_DESCRIPTION,"Delete Form");
    action_delete_form.putValue(Action.LONG_DESCRIPTION,"Delete Form");
    //XXX action_delete_form.putValue(Action.SMALL_ICON,...);
    //XXX action_delete_form.putValue(Action.ACTION_COMMAND_KEY,...);
    action_delete_form.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_delete_form.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Delete Form",action_delete_form);

    inputMap.put((KeyStroke)actionMap.get("Delete Form").getValue(Action.ACCELERATOR_KEY),
		 "Delete Form");
    

    Action action_delete_bean;
    action_delete_bean=new AbstractAction("Delete Current Bean") {
	public void actionPerformed(ActionEvent e) {
	  if(getCurrentBean()!=null) 
	    if(!removeCurrentBean())getToolkit().beep();
	};
      };
    
    action_delete_bean.putValue(Action.NAME,"Delete Current Bean");
    action_delete_bean.putValue(Action.SHORT_DESCRIPTION,"Delete Current Bean");
    action_delete_bean.putValue(Action.LONG_DESCRIPTION,"Delete Current Bean");
    //XXX action_delete_bean.putValue(Action.SMALL_ICON,...);
    //XXX action_delete_bean.putValue(Action.ACTION_COMMAND_KEY,...);
    action_delete_bean.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("DELETE"));
    //XXX action_delete_bean.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Delete Current Bean",action_delete_bean);

    inputMap.put((KeyStroke)actionMap.get("Delete Current Bean").getValue(Action.ACCELERATOR_KEY),
		 "Delete Current Bean");


    Action action_down_bean;
    action_down_bean=new AbstractAction("Down Bean") {
	public void actionPerformed(ActionEvent e) {
	  Container bp=getBeanPane();
	  if(bp.getComponentCount()==0) {
	    setCurrentBeanComponent(null);
	  }
	  else if(getCurrentBeanComponent()==null) {
	    setCurrentBeanComponent(bp.getComponent(0));
	  } else {
	    Component comp=getCurrentBeanComponent();
	    if(comp instanceof Container && ((Container)comp).getComponentCount()>0)
	      setCurrentBeanComponent(((Container)comp).getComponent(0));
	    else
	      setCurrentBeanComponent(bp.getComponent(0));
	  }
	};
      };
    
    action_down_bean.putValue(Action.NAME,"Down Bean");
    action_down_bean.putValue(Action.SHORT_DESCRIPTION,"Down Bean");
    action_down_bean.putValue(Action.LONG_DESCRIPTION,"Down Bean");
    //XXX action_down_bean.putValue(Action.SMALL_ICON,...);
    //XXX action_down_bean.putValue(Action.ACTION_COMMAND_KEY,...);
    action_down_bean.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("SPACE"));
    //XXX action_down_bean.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Down Bean",action_down_bean);

    inputMap.put((KeyStroke)actionMap.get("Down Bean").getValue(Action.ACCELERATOR_KEY),
		 "Down Bean");
    inputMap.put(KeyStroke.getKeyStroke("control SPACE"),"Down Bean");


    Action action_up_bean;
    action_up_bean=new AbstractAction("Up Bean") {
	public void actionPerformed(ActionEvent e) {
	  Container bp=getBeanPane();
	  if(bp.getComponentCount()==0) {
	    setCurrentBeanComponent(null);
	  }
	  else if(getCurrentBeanComponent()==null) {
	    setCurrentBeanComponent(bp.getComponent(0));
	  } else {
	    Container cont=getCurrentBeanComponent().getParent();
	    if(cont!=bp)
	      setCurrentBeanComponent(cont);
	  }
	};
      };
    
    action_up_bean.putValue(Action.NAME,"Up Bean");
    action_up_bean.putValue(Action.SHORT_DESCRIPTION,"Up Bean");
    action_up_bean.putValue(Action.LONG_DESCRIPTION,"Up Bean");
    //XXX action_up_bean.putValue(Action.SMALL_ICON,...);
    //XXX action_up_bean.putValue(Action.ACTION_COMMAND_KEY,...);
    action_up_bean.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("shift SPACE"));
    //XXX action_up_bean.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Up Bean",action_up_bean);

    inputMap.put((KeyStroke)actionMap.get("Up Bean").getValue(Action.ACCELERATOR_KEY),
		 "Up Bean");
    inputMap.put(KeyStroke.getKeyStroke("control shift SPACE"),"Up Bean");


    Action action_next_bean;
    action_next_bean=new AbstractAction("Next Bean") {
	public void actionPerformed(ActionEvent e) {
	  Container bp=getBeanPane();
	  if(bp.getComponentCount()==0) {
	    setCurrentBeanComponent(null);
	  }
	  else if(getCurrentBeanComponent()==null) {
	    setCurrentBeanComponent(bp.getComponent(0));
	  } else {
	    bp=getCurrentBeanComponent().getParent();
	    for(int i=0;i<bp.getComponentCount();i++) {
	      if(bp.getComponent(i)==getCurrentBeanComponent()) {
		setCurrentBeanComponent(bp.getComponent((i+1)%bp.getComponentCount()));
		break;
	      }
	    }
	  }
	  
	};
      };
    
    action_next_bean.putValue(Action.NAME,"Next Bean");
    action_next_bean.putValue(Action.SHORT_DESCRIPTION,"Next Bean");
    action_next_bean.putValue(Action.LONG_DESCRIPTION,"Next Bean");
    //XXX action_next_bean.putValue(Action.SMALL_ICON,...);
    //XXX action_next_bean.putValue(Action.ACTION_COMMAND_KEY,...);
    action_next_bean.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("TAB"));
    //XXX action_next_bean.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Next Bean",action_next_bean);

    inputMap.put((KeyStroke)actionMap.get("Next Bean").getValue(Action.ACCELERATOR_KEY),
		 "Next Bean");
    inputMap.put(KeyStroke.getKeyStroke("control TAB"),"Next Bean");


    Action action_previous_bean;
    action_previous_bean=new AbstractAction("Previous Bean") {
	public void actionPerformed(ActionEvent e) {
	  Container bp=getBeanPane();
	  if(bp.getComponentCount()==0) {
	    setCurrentBeanComponent(null);
	  }
	  else if(getCurrentBeanComponent()==null) {
	    setCurrentBeanComponent(bp.getComponent(0));
	  } else {
	    bp=getCurrentBeanComponent().getParent();
	    for(int i=0;i<bp.getComponentCount();i++) {
	      if(bp.getComponent(i)==getCurrentBeanComponent()) {
		setCurrentBeanComponent(bp.getComponent((i+bp.getComponentCount()-1)%bp.getComponentCount()));
		break;
	      }
	    }
	  }
	  
	};
      };
    
    action_previous_bean.putValue(Action.NAME,"Previous Bean");
    action_previous_bean.putValue(Action.SHORT_DESCRIPTION,"Previous Bean");
    action_previous_bean.putValue(Action.LONG_DESCRIPTION,"Previous Bean");
    //XXX action_previous_bean.putValue(Action.SMALL_ICON,...);
    //XXX action_previous_bean.putValue(Action.ACTION_COMMAND_KEY,...);
    action_previous_bean.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("shift TAB"));
    //XXX action_previous_bean.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("Previous Bean",action_previous_bean);

    inputMap.put((KeyStroke)actionMap.get("Previous Bean").getValue(Action.ACCELERATOR_KEY),
		 "Previous Bean");
    inputMap.put(KeyStroke.getKeyStroke("control shift TAB"),"Previous Bean");

    Action action_view_highlight_all_beans;
    action_view_highlight_all_beans=new AbstractAction("Highlight All Beans") {
	public void actionPerformed(ActionEvent e) {
	  beanHighlightingStatus=BHS_HIGHLIGHT_ALL_BEANS;
	  glassPane.repaint();
	};
      };
    action_view_highlight_all_beans.putValue(Action.NAME,"Highlight All Beans");
    action_view_highlight_all_beans.putValue(Action.SHORT_DESCRIPTION,"Highlight All Beans");
    action_view_highlight_all_beans.putValue(Action.LONG_DESCRIPTION,"Highlight All Beans");
    //XXX action_view_highlight_all_beans(Action.SMALL_ICON,...);
    //XXX action_view_highlight_all_beans(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_all_beans.putValue(Action.ACCELERATOR_KEY,
						   KeyStroke.getKeyStroke("control A"));
    //XXX action_view_highlight_all_beans.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight All Beans",action_view_highlight_all_beans);
    inputMap.put((KeyStroke)actionMap.get("Highlight All Beans").getValue(Action.ACCELERATOR_KEY),
		 "Highlight All Beans");
    

    Action action_view_highlight_component_beans;
    action_view_highlight_component_beans=new AbstractAction("Highlight Components") {
	public void actionPerformed(ActionEvent e) {
	  beanHighlightingStatus=BHS_HIGHLIGHT_COMPONENT_BEANS;
	  glassPane.repaint();
	};
      };
    action_view_highlight_component_beans.putValue(Action.NAME,"Highlight Components");
    action_view_highlight_component_beans.putValue(Action.SHORT_DESCRIPTION,"Highlight Components");
    action_view_highlight_component_beans.putValue(Action.LONG_DESCRIPTION,"Highlight Components");
    //XXX action_view_highlight_component_beans(Action.SMALL_ICON,...);
    //XXX action_view_highlight_component_beans(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_component_beans.putValue(Action.ACCELERATOR_KEY,
						   KeyStroke.getKeyStroke("control C"));
    //XXX action_view_highlight_component_beans.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight Components",action_view_highlight_component_beans);
    inputMap.put((KeyStroke)actionMap.get("Highlight Components").getValue(Action.ACCELERATOR_KEY),
		 "Highlight Components");
    

    Action action_view_highlight_nonvisual_beans;
    action_view_highlight_nonvisual_beans=new AbstractAction("Highlight Non-visual Beans") {
	public void actionPerformed(ActionEvent e) {
	  beanHighlightingStatus=BHS_HIGHLIGHT_NONVISUAL_BEANS;
	  glassPane.repaint();
	};
      };
    action_view_highlight_nonvisual_beans.putValue(Action.NAME,"Highlight Non-visual Beans");
    action_view_highlight_nonvisual_beans.putValue(Action.SHORT_DESCRIPTION,
						   "Highlight Non-visual Beans");
    action_view_highlight_nonvisual_beans.putValue(Action.LONG_DESCRIPTION,
						   "Highlight Non-visual Beans");
    //XXX action_view_highlight_nonvisual_beans(Action.SMALL_ICON,...);
    //XXX action_view_highlight_nonvisual_beans(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_nonvisual_beans.putValue(Action.ACCELERATOR_KEY,
						   KeyStroke.getKeyStroke("control B"));
    //XXX action_view_highlight_nonvisual_beans.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight Non-visual Beans",action_view_highlight_nonvisual_beans);
    inputMap.put((KeyStroke)actionMap.get("Highlight Non-visual Beans")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Highlight Non-visual Beans");
    
    Action action_view_highlight_no_beans;
    action_view_highlight_no_beans=new AbstractAction("Highlight Non-visual Beans") {
	public void actionPerformed(ActionEvent e) {
	  beanHighlightingStatus=BHS_HIGHLIGHT_NO_BEANS;
	  glassPane.repaint();
	};
      };
    action_view_highlight_no_beans.putValue(Action.NAME,"Don't Highlight Beans");
    action_view_highlight_no_beans.putValue(Action.SHORT_DESCRIPTION,
						   "Don't Highlight Beans");
    action_view_highlight_no_beans.putValue(Action.LONG_DESCRIPTION,
						   "Don't Highlight Beans");
    //XXX action_view_highlight_no_beans(Action.SMALL_ICON,...);
    //XXX action_view_highlight_no_beans(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_no_beans.putValue(Action.ACCELERATOR_KEY,
						   KeyStroke.getKeyStroke("control D"));
    //XXX action_view_highlight_no_beans.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Don't Highlight Beans",action_view_highlight_no_beans);
    inputMap.put((KeyStroke)actionMap.get("Don't Highlight Beans")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Don't Highlight Beans");


    Action action_view_highlight_all_event_links;
    action_view_highlight_all_event_links=new AbstractAction("Highlight All Event Links") {
	public void actionPerformed(ActionEvent e) {
	  eventLinkHighlightingStatus=ELHS_HIGHLIGHT_ALL_LINKS;
	  glassPane.repaint();
	};
      };
    action_view_highlight_all_event_links.putValue(Action.NAME,"Highlight All Event Links");
    action_view_highlight_all_event_links.putValue(Action.SHORT_DESCRIPTION,
						   "Highlight All Event Links");
    action_view_highlight_all_event_links.putValue(Action.LONG_DESCRIPTION,
						   "Highlight All Event Links");
    //XXX action_view_highlight_all_event_links(Action.SMALL_ICON,...);
    //XXX action_view_highlight_all_event_links(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_all_event_links.putValue(Action.ACCELERATOR_KEY,
						   KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_view_highlight_all_event_links.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight All Event Links",action_view_highlight_all_event_links);
    inputMap.put((KeyStroke)actionMap.get("Highlight All Event Links")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Highlight All Event Links");

    Action action_view_highlight_current_all_event_links;
    action_view_highlight_current_all_event_links
      =new AbstractAction("Highlight Current Bean's Event Links") {
	  public void actionPerformed(ActionEvent e) {
	    eventLinkHighlightingStatus=ELHS_HIGHLIGHT_CURRENT_ALL_LINKS;
	    glassPane.repaint();
	  };
	};
    action_view_highlight_current_all_event_links.putValue(Action.NAME,
							   "Highlight Current Bean's Event Links");
    action_view_highlight_current_all_event_links.putValue(Action.SHORT_DESCRIPTION,
							   "Highlight Current Bean's Event Links");
    action_view_highlight_current_all_event_links.putValue(Action.LONG_DESCRIPTION,
							   "Highlight Current Bean's Event Links");
    //XXX action_view_highlight_current_all_event_links(Action.SMALL_ICON,...);
    //XXX action_view_highlight_current_all_event_links(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_current_all_event_links.putValue(Action.ACCELERATOR_KEY,
							   KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_view_highlight_current_all_event_links.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight Current Bean's Event Links",action_view_highlight_current_all_event_links);
    inputMap.put((KeyStroke)actionMap.get("Highlight Current Bean's Event Links")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Highlight Current Bean's Event Links");

    Action action_view_highlight_current_incoming_event_links;
    action_view_highlight_current_incoming_event_links
      =new AbstractAction("Highlight Current Bean's Incoming Event Links") {
	  public void actionPerformed(ActionEvent e) {
	    eventLinkHighlightingStatus=ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS;
	    glassPane.repaint();
	  };
	};
    action_view_highlight_current_incoming_event_links
      .putValue(Action.NAME,"Highlight Current Bean's Incoming Event Links");
    action_view_highlight_current_incoming_event_links
      .putValue(Action.SHORT_DESCRIPTION,"Highlight Current Bean's Incoming Event Links");
    action_view_highlight_current_incoming_event_links
      .putValue(Action.LONG_DESCRIPTION,"Highlight Current Bean's Incoming Event Links");
    //XXX action_view_highlight_current_incoming_event_links(Action.SMALL_ICON,...);
    //XXX action_view_highlight_current_incoming_event_links(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_current_incoming_event_links
      .putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_view_highlight_current_incoming_event_links.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight Current Bean's Incoming Event Links",
		  action_view_highlight_current_incoming_event_links);
    inputMap.put((KeyStroke)actionMap.get("Highlight Current Bean's Incoming Event Links")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Highlight Current Bean's Incoming Event Links");

    Action action_view_highlight_current_outgoing_event_links;
    action_view_highlight_current_outgoing_event_links
      =new AbstractAction("Highlight Current Bean's Outgoing Event Links") {
	  public void actionPerformed(ActionEvent e) {
	    eventLinkHighlightingStatus=ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS;
	    glassPane.repaint();
	  };
	};
    action_view_highlight_current_outgoing_event_links
      .putValue(Action.NAME,"Highlight Current Bean's Outgoing Event Links");
    action_view_highlight_current_outgoing_event_links
      .putValue(Action.SHORT_DESCRIPTION,"Highlight Current Bean's Outgoing Event Links");
    action_view_highlight_current_outgoing_event_links
      .putValue(Action.LONG_DESCRIPTION,"Highlight Current Bean's Outgoing Event Links");
    //XXX action_view_highlight_current_outgoing_event_links(Action.SMALL_ICON,...);
    //XXX action_view_highlight_current_outgoing_event_links(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_current_outgoing_event_links
      .putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_view_highlight_current_outgoing_event_links.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Highlight Current Bean's Outgoing Event Links",
		  action_view_highlight_current_outgoing_event_links);
    inputMap.put((KeyStroke)actionMap.get("Highlight Current Bean's Outgoing Event Links")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Highlight Current Bean's Outgoing Event Links");

    Action action_view_highlight_no_event_links;
    action_view_highlight_no_event_links=new AbstractAction("Don't Highlight Event Links") {
	  public void actionPerformed(ActionEvent e) {
	    eventLinkHighlightingStatus=ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS;
	    glassPane.repaint();
	  };
	};
    action_view_highlight_no_event_links
      .putValue(Action.NAME,"Don't Highlight Event Links");
    action_view_highlight_no_event_links
      .putValue(Action.SHORT_DESCRIPTION,"Don't Highlight Event Links");
    action_view_highlight_no_event_links
      .putValue(Action.LONG_DESCRIPTION,"Don't Highlight Event Links");
    //XXX action_view_highlight_no_event_links(Action.SMALL_ICON,...);
    //XXX action_view_highlight_no_event_links(Action.ACTION_COMMAND_KEY,...);
    action_view_highlight_no_event_links
      .putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control #"));//XXX
    //XXX action_view_highlight_no_event_links.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put("Don't Highlight Event Links",
		  action_view_highlight_no_event_links);
    inputMap.put((KeyStroke)actionMap.get("Don't Highlight Event Links")
		 .getValue(Action.ACCELERATOR_KEY),
		 "Don't Highlight Event Links");

};
  
  
  /**
   * Sets up the layering of {@link #glassPane glassPane} and {@link #beanPane beanPane}.
   * Called once only from the constructor.
   */
  protected void setupLayeredPanes() {
    JLayeredPane layeredPane=new JLayeredPane();
    layeredPane.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    //layeredPane.setBorder(BorderFactory.createLineBorder(Color.black));
    layeredPane.setLayout(new OverlayLayout(layeredPane));

    //The input map attached to layeredPane will handle everything, so we don't want focus to change to
    //anything else.
    layeredPane.setFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS,
				      Collections.EMPTY_SET);
    layeredPane.setFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS,
				      Collections.EMPTY_SET);
    layeredPane.setFocusTraversalKeys(KeyboardFocusManager.UP_CYCLE_TRAVERSAL_KEYS,
				      Collections.EMPTY_SET);
    layeredPane.setFocusTraversalPolicy(new FocusTraversalPolicy() {
	public Component getComponentAfter(Container focusCycleRoot, Component aComponent) {
	  return null;
	};
	public Component getComponentBefore(Container focusCycleRoot, Component aComponent) {
	  return null;
	};
	public Component getFirstComponent(Container focusCycleRoot) {
	  return null;
	};
	public Component getLastComponent(Container focusCycleRoot) {
	  return null;
	};
	public Component getDefaultComponent(Container focusCycleRoot) {
	  return null;
	};
	public Component getInitialComponent(Window window) {
	  return null;
	}
      });

    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(layeredPane,BorderLayout.CENTER);

    beanPane=new JPanel(null);
    beanPane.setFocusable(false);
    layeredPane.add(beanPane,new Integer(0));
    


    glassPane.setFocusable(false);
    glassPane.setOpaque(false);
    layeredPane.add(glassPane,new Integer(1));

    GPMouseListener gpml=new GPMouseListener();
    glassPane.addMouseListener(gpml);
    glassPane.addMouseMotionListener(gpml);

    layeredPane.setActionMap(actionMap);
    layeredPane.setInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,inputMap);
    layeredPane.setFocusable(true);
    layeredPane.requestFocusInWindow();    
  };
  /**
   * Sets up the menu bar.  Called once only from the constructor.
   */
  protected void setupMenus(JMenu window) {
    JMenuBar mb=new JMenuBar();
    JMenu file=new JMenu("File");
    file.setMnemonic(KeyEvent.VK_F);
    file.add(new JMenuItem(actionMap.get("New Form")));
    file.add(new JMenuItem(actionMap.get("Delete Form")));
    file.addSeparator();
    file.add(new JMenuItem(actionMap.get("Save...")));
    file.add(new JMenuItem(actionMap.get("Open...")));
    file.add(new JMenuItem(actionMap.get("Import...")));
    file.addSeparator();
    file.add(new JMenuItem(actionMap.get("Quit")));
    JMenu edit=new JMenu("Edit");
    edit.setMnemonic(KeyEvent.VK_E);
    JMenu view=new JMenu("View");
    view.setMnemonic(KeyEvent.VK_V);

    JMenu view_highlight_beans_menu=new JMenu("Highlight Beans");
    ButtonGroup view_highlight_beans=new ButtonGroup();
    JRadioButtonMenuItem rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight All Beans"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight Components"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight Non-visual Beans"));
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Don't Highlight Beans"));
    rbmi.setSelected(true);
    view_highlight_beans.add(rbmi);
    view_highlight_beans_menu.add(rbmi);
    view.add(view_highlight_beans_menu);
    
    JMenu view_highlight_links_menu=new JMenu("Highlight Event Links");
    ButtonGroup view_highlight_links=new ButtonGroup();
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight All Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's Incoming Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Highlight Current Bean's Outgoing Event Links"));
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    rbmi=new JRadioButtonMenuItem(actionMap.get("Don't Highlight Event Links"));
    rbmi.setSelected(true);
    view_highlight_links.add(rbmi);
    view_highlight_links_menu.add(rbmi);
    view.add(view_highlight_links_menu);

    

    JMenu help=new JMenu("Help");
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
  protected void setupStatusBar() {
    statusBar.setFocusable(false);
    getContentPane().add(statusBar,BorderLayout.SOUTH);
  };
  
  /**
   * Creates a new Form designer.
   */
  public FormDesign(ActionMap am, InputMap im, JMenu wm, DesignerCore dc) {
    this("Main",am,im,wm,dc);
  };
  
  public FormDesign(String name, ActionMap am, InputMap im, JMenu windowMenu, DesignerCore desCore) {
    this(new Form(name),am,im,windowMenu,desCore);
    form.setBounds(5,5,100,100);
  };
  
  public FormDesign(Form _form, ActionMap am, InputMap im, JMenu windowMenu, DesignerCore desCore) {
    super("Design Mode: "+_form.getName());
    setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
    glassPane.setToolTipText("");//Necessary because getToolTipText(MouseEvent) won't be used otherwise
    
    setupActions(am,im,desCore);
    setupLayeredPanes();
    setupMenus(windowMenu);
    setupStatusBar();
    handles=new HashMap();

    form=_form;
    form.addPropertyChangeListener("name",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  setTitle("Design Mode: "+form.getName());
	};
      });
    
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.black),
						    form.getName()));
    form.addPropertyChangeListener("name",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  //XXX It seems that Component/JComponent etc, don't send an event when 'name' changes!
	  //    Should find a solution that will work.  At present it is fixed with a nasty hack in
	  //    PropertiesWindow.java that sends the PropertyChangeEvents on behalf of the Component
	  ((TitledBorder)((Form)evt.getSource()).getBorder()).setTitle((String)evt.getNewValue());
	  ((Form)evt.getSource()).repaint();//XXX could this be narrowed to just repaint the border?
	};
      });
    
    getBeanPane().add(form);
    new HandleSet(form);
    setCurrentBeanComponent(form);    
    raiseAction=new RaiseAction(this);
  };

  public static FormDesign loadDesign(XMLDecoder decoder, 
				      ActionMap am, InputMap im, JMenu windowMenu, DesignerCore desCore) {
    Form form;
    Vector beanWrappers;
    Vector eventLinks;
    form=(Form)decoder.readObject();
    beanWrappers=(Vector)decoder.readObject();
    eventLinks=(Vector)decoder.readObject();

    FormDesign fd=new FormDesign(form,am,im,windowMenu,desCore);
    
    for(Iterator it=((BeanContext)form.getBeanContextProxy()).iterator();it.hasNext();)
      try {//Add handle sets for all of the beans already added into the form.
	fd.newHandleSet((Component)it.next());
      } catch(ClassCastException ex) {
	//Ignore exceptions from trying to cast for non-component beans.
      };
    
    for(Iterator i=eventLinks.iterator();i.hasNext();fd.addEventLink((BeanLink)i.next()));
    for(Iterator i=beanWrappers.iterator();i.hasNext();) {
      BeanWrapper bw=(BeanWrapper)i.next();
      fd.getBeanPane().add(bw);
      fd.newHandleSet(bw);
    };
    
    return fd;
  };
  public void saveDesign(XMLEncoder encoder) {
    encoder.writeObject(form);
    Component[] components=getBeanPane().getComponents();
    Vector beanWrappers=new Vector();
    for(int i=0;i<components.length;i++)
      if(components[i] instanceof BeanWrapper) 
	beanWrappers.add(components[i]);

    encoder.writeObject(beanWrappers);
    encoder.writeObject(eventLinks);
  };
  
  
  /**
   * Mapping from beans in the design to their set of handles.
   */
  protected Map handles;//Map<Object, HandleSet> map from bean/component to handles
  

  private void newHandleSet(final Component bean) {//XXX NOT NICE, FIX
    new HandleSet(bean);
  };
  
  /**
   * Class collecting together the eight resize handle, and one move handle belonging to a bean.
   */
  protected class HandleSet {
    /**
     * The corner and edge resize handles.  These appear as squares on the corners and edges of a bean.
     */
    public BeanHandle n,ne,e,se,s,sw,w,nw,move;
    /**
     * Calls setVisible on all of the BeanHandles.
     */
    public void setBeanHandlesVisible(boolean b) {
      n.setVisible(b);ne.setVisible(b);
      e.setVisible(b);se.setVisible(b);
      s.setVisible(b);sw.setVisible(b);
      w.setVisible(b);nw.setVisible(b);
      move.setVisible(b);
    };
    
    public void setLocation() {
      n.setLocation();ne.setLocation();
      e.setLocation();se.setLocation();
      s.setLocation();sw.setLocation();
      w.setLocation();nw.setLocation();
      move.setLocation();
    };
    
    
    /**
     * Creates a HandleSet, all of the handles that go in it, and a mouse adapter that sets the current
     * bean when it is clicked on.
     */
    public HandleSet(final Component bean) {

      glassPane.add(se=new BeanHandle(bean,Cursor.SE_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(s=new BeanHandle(bean,Cursor.S_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(e=new BeanHandle(bean,Cursor.E_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(sw=new BeanHandle(bean,Cursor.SW_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(ne=new BeanHandle(bean,Cursor.NE_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(n=new BeanHandle(bean,Cursor.N_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(w=new BeanHandle(bean,Cursor.W_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(nw=new BeanHandle(bean,Cursor.NW_RESIZE_CURSOR,FormDesign.this));
      glassPane.add(move=new BeanHandle(bean,Cursor.MOVE_CURSOR,FormDesign.this));
      handles.put(bean,this);
      setBeanHandlesVisible(false);
      
    };
  };
  
  /**
   * Mouse listener for the {@link #glassPane glass pane}.  Used mostly for creation of beans when 
   * the user clicks or drags directly on the glass pane.
   */
  protected class GPMouseListener extends MouseInputAdapter {
    public void mouseClicked (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseClicked (e,FormDesign.this);
    };
    public void mousePressed (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mousePressed (e,FormDesign.this);
    };
    public void mouseReleased(MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseReleased(e,FormDesign.this);
    };
    public void mouseEntered (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseEntered (e,FormDesign.this);
    };
    public void mouseExited  (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseExited  (e,FormDesign.this);
    };
    public void mouseDragged (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseDragged (e,FormDesign.this);
    };
    public void mouseMoved   (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseMoved   (e,FormDesign.this);
    };
  };  

  /**
   * Translates a coordinate described in a coordinate space that is a descendant of this 
   * <code>FormDesign</code> to the same coordinate relative to the <code>beanPane</code>'s coordinate
   * space.  
   * @param point the coordinate to translate.
   * @param cSpace container with coordinate space to which <code>point</code> is relative.
   * @return the transformed coordinate.  <code>null</code> if cSpace is not a descendant of 
   *         <code>beanPane</code>.
   */
  public Point translateCoordinateFromCSpace(Point point, Component cSpace) {
    point=new Point(point);
    for(;cSpace!=beanPane;cSpace=cSpace.getParent()) 
      if(cSpace==null) return null;
      else point.translate(cSpace.getX(),cSpace.getY());
    return point;
  };
  
  /**
   * Uses <code>translateCoordinateFromCSpace</code> to give the location of a component in the 
   * <code>beanPane</code>'s coordinate space.
   * @param component the component whose location will be found.
   * @return the location of the component in the <code>beanPane</code>'s coordinate space.
   */
  public Point componentLocationInBeanPaneSpace(Component component) {
    return translateCoordinateFromCSpace(component.getLocation(),component.getParent());
  };
  
  /**
   * Translates a coordinate relative to the <code>beanPane</code>'s coordinate space into the same
   * coordinate relative to the coordinate space belonging to <code>cSpace</code>.
   * @param point the coordinate to translate.
   * @param cSpace container with coordinate space to which <code>point</code> will be translated.
   * @return the transformed coordinate.  <code>null</code> if cSpace is not a descendant of 
   *         <code>beanPane</code>.  NOTE: The coordinate may lay outside the bounds of the container.
   */
  public Point translateCoordinateToCSpace(Point point, Component cSpace) {
    point=new Point(point);
    for(;cSpace!=beanPane;cSpace=cSpace.getParent())
      if(cSpace==null) return null;
      else point.translate(-cSpace.getX(),-cSpace.getY());
    return point;
  };

  public void setCursor(Cursor cursor) {//XXX not particularly nice.
    glassPane.setCursor(cursor);
  };
  


};

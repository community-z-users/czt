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
   * The glass pane is used to block interaction with the beans/components being placed, and to draw
   * handles and other guides on top of the form being designed.<br>
   * <em>Note:</em> This glass pane is not the glass p
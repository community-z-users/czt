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

import czt.animation.gui.Form;

import java.awt.BorderLayout;             import java.awt.Color;
import java.awt.Component;                import java.awt.Container;                
import java.awt.Cursor;                   import java.awt.Dimension;                
import java.awt.FlowLayout;               import java.awt.Graphics;                 
import java.awt.Image;                    import java.awt.MediaTracker;             
import java.awt.Point;                    import java.awt.Toolkit;                  
import java.awt.Transparency;             

import java.awt.event.ActionEvent;        import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;

import java.beans.BeanInfo;               import java.beans.BeanDescriptor;
import java.beans.Beans;                  import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException; import java.beans.Introspector;
import java.beans.PropertyChangeSupport;  

import java.io.IOException;

import java.util.Iterator;                import java.util.ListIterator;            
import java.util.Vector;

import javax.swing.AbstractAction;        import javax.swing.Action;
import javax.swing.BorderFactory;         import javax.swing.Icon; 
import javax.swing.ImageIcon;             import javax.swing.JButton;
import javax.swing.JFrame;                import javax.swing.JCheckBox;
import javax.swing.JLabel;                import javax.swing.JOptionPane;
import javax.swing.JPanel;

import javax.swing.border.BevelBorder;    import javax.swing.border.Border;
import javax.swing.border.EtchedBorder;   

import javax.swing.event.EventListenerList;


class ToolWindow extends JFrame {
  protected Vector tools; //Vector<Tool> tools
  protected JPanel nonBeanToolPanel;
  protected JPanel beanToolPanel;

  private Tool currentTool;
  private final Tool defaultTool;
  public Tool getCurrentTool() {
    return currentTool;
  };
  protected void setCurrentTool(Tool t) {
    Tool oldTool=currentTool;
    currentTool=t;
    if(oldTool!=null)oldTool.unselected();
    if(currentTool!=null)currentTool.selected();
    fireToolChanged(currentTool,oldTool);
    if(currentTool!=null&&currentTool.isOneShot()&&currentTool!=defaultTool)
      setCurrentTool(defaultTool);
  };
  
  private EventListenerList toolChangeListeners;
  /**
   * Registers a <code>ToolChangeListener</code> with the <code>ToolWindow</code>.  
   * Note: it will send a toolChanged message to the listener (with the tool and oldTool parameters 
   * equal) when it is registered.
   */
  public void addToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.add(ToolChangeListener.class, l);
    l.toolChanged(new ToolChangeEvent(this,getCurrentTool(),getCurrentTool()));
  }
  /**
   * Unregisters a <code>ToolChangeListener</code> with the <code>ToolWindow</code>.
   */
  public void removeToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.remove(ToolChangeListener.class, l);
  }
  public ToolChangeListener[] getToolChangeListeners() {
    return (ToolChangeListener[])toolChangeListeners.getListeners(ToolChangeListener.class);
  };
  protected void fireToolChanged(Tool tool, Tool oldTool) {
    final ToolChangeListener[] listeners=getToolChangeListeners();
    final ToolChangeEvent ev=new ToolChangeEvent(this,tool, oldTool);
    for(int i=0;i<listeners.length;i++) listeners[i].toolChanged(ev);
  };
  Cursor crossCursor;
  private void setupCrossCursor() {
    MediaTracker mt=new MediaTracker(this);
    Image baseCursorImage=getToolkit()
      .getImage(ClassLoader.getSystemResource("czt/animation/gui/design/XCursor.gif"))
      .getScaledInstance(16,16,Image.SCALE_DEFAULT);;
    mt.addImage(baseCursorImage,0);
    try {
      mt.waitForID(0);
    } catch (InterruptedException ex) {
      System.err.println("Interrupted");//XXX
    };
    
    Dimension bestSize=getToolkit().getBestCursorSize(16,16);
    Image cursorImage=getGraphicsConfiguration().createCompatibleImage((int)bestSize.getWidth(),
								       (int)bestSize.getHeight(),
								       
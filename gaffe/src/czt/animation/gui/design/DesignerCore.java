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

import czt.animation.gui.design.FormDesign;
import czt.animation.gui.design.ToolWindow;

import czt.animation.gui.design.properties.PropertiesWindow;

import czt.animation.gui.persistence.delegates.BeanWrapperDelegate;
import czt.animation.gui.persistence.delegates.FormDelegate;

import czt.animation.gui.scripting.ScriptDelegate;

import java.awt.event.ActionEvent;        import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;      import java.awt.event.WindowEvent;

import java.beans.ExceptionListener;
import java.beans.XMLDecoder;             import java.beans.XMLEncoder;

import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import java.beans.beancontext.BeanContextServicesSupport;

import java.util.EventListener;           import java.util.HashMap;
import java.util.Iterator;                import java.util.List;
import java.util.ListIterator;            import java.util.Vector;

import java.io.File;                      import java.io.FileInputStream;
import java.io.FileOutputStream;          import java.io.FileNotFoundException;     
import java.io.IOException;

import javax.swing.AbstractAction;        import javax.swing.Action;
import javax.swing.ActionMap;             import javax.swing.InputMap;
import javax.swing.JButton;               import javax.swing.JCheckBox;
import javax.swing.JFileChooser;          import javax.swing.JLabel;                
import javax.swing.JMenu;                 import javax.swing.JMenuItem;             
import javax.swing.JOptionPane;           import javax.swing.KeyStroke;

import javax.swing.event.EventListenerList;

public class DesignerCore implements BeanContextProxy {

  public static int run(String[] args) {
    new DesignerCore();
    return 0;
  };
  
  private BeanContextServicesSupport bcsSupport;
  public BeanContextChild getBeanContextProxy() {return bcsSupport;};

  private final List forms;//List<FormDesign>
  private FormDesign currentBeansForm;
  protected FormDesign getSelectedBeansForm() {return currentBeansForm;};
  private Object currentBean;
  protected Object getSelectedBean() {return currentBean;};

  private final ToolWindow toolWindow;
  public ToolWindow getToolWindow() {return toolWindow;};

  private final PropertiesWindow propertiesWindow=new PropertiesWindow();
  public PropertiesWindow getPropertiesWindow() {return propertiesWindow;};
  
  private EventListenerList listenerSupport=new EventListenerList();
  
  public void addFormDesignListener(FormDesignListener l) {
    for(Iterator i=forms.iterator();i.hasNext();)
      l.formCreated(new FormDesignEvent(this,(FormDesign)i.next(),FormDesignEvent.CREATED));
    listenerSupport.add(FormDesignListener.class,l);
  };
  public void removeFormDesignListener(FormDesignListener l) {
    listenerSupport.remove(FormDesignListener.class,l);
  };
  protected void fireFormCreated(FormDesign f) {
    EventListener[] list=listenerSupport.getListeners(FormDesignListener.class);
    FormDesignEvent ev=new FormDesignEvent(this,f,FormDesignEvent.CREATED);
    for(int i=0;i<list.length;i++)
      ((FormDesignListener)list[i]).formCreated(ev);
  };
  protected void fireFormDeleted(FormDesign f) {
    EventListener[] list=listenerSupport.getListeners(FormDesignListener.class);
    FormDesignEvent ev=new FormDesignEvent(this,f,FormDesignEvent.DELETED);
    for(int i=0;i<list.length;i++)
      ((FormDesignListener)list[i]).formDeleted(ev);
  };
  
  

  public DesignerCore() {
    forms=new Vector();//List<FormDesign>
    currentBeansForm=null; currentBean=null;

    //XXX classes should come from a settings file or something
    toolWindow=new ToolWindow(new Class[] {JButton.class,JCheckBox.class,JLabel.class,
					   ScriptDelegate.class});
    setupActions();
    
    bcsSupport=new BeanContextServicesSupport();
    bcsSupport.addService(DesignerCore.class,new BeanContextServiceProvider() {
	pu
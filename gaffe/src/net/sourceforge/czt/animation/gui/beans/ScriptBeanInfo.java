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
package net.sourceforge.czt.animation.gui.beans;

import java.awt.BorderLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Image;

import java.beans.BeanDescriptor;
import java.beans.Customizer;
import java.beans.SimpleBeanInfo;

import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;

import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

/**
 * <code>BeanInfo</code> for Script.  
 * Exists for the sole purpose of giving the ScriptBeanInfo bean an icon.
 */
public class ScriptBeanInfo extends SimpleBeanInfo {
  /**
   * Obtains the image for Script's icon. 
   * @return The image obtained from the file "ScriptIcon.gif".
   */
  public Image getIcon(int iconKind) {
    switch(iconKind) {
     case ICON_COLOR_32x32: case ICON_MONO_32x32:
       return loadImage("ScriptIcon.gif");
     case ICON_COLOR_16x16: case ICON_MONO_16x16:
       return loadImage("ScriptIcon.gif")
	 .getScaledInstance(16,16,Image.SCALE_FAST);
     default:
       throw new Error("iconKind should be one of ICON_COLOR_32x32, ICON_MONO_32x32, "
		       +"ICON_COLOR_16x16, ICON_MONO_16x16");
    }     
  };

  public static final class ScriptBeanCustomiser extends JPanel implements Customizer {
    private Script scriptBean=null;
    private JTextField nameField=new JTextField(20);
    private JTextField languageField=new JTextField(20);
    private JTextArea  scriptField=new JTextArea(5,20);
    public ScriptBeanCustomiser() {
      nameField.getDocument().addDocumentListener(new DocumentListener() {
	  public void insertUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void removeUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void changedUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  private void changeBean() {
	    scriptBean.setName(nameField.getText());
	    firePropertyChange("name",null,null);
	  };
	});
      languageField.getDocument().addDocumentListener(new DocumentListener() {
	  public void insertUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void removeUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void changedUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  private void changeBean() {
	    scriptBean.setLanguage(languageField.getText());
	    firePropertyChange("language",null,null);
	  };
	});
      scriptField.getDocument().addDocumentListener(new DocumentListener() {
	  public void insertUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void removeUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  public void changedUpdate(DocumentEvent e) {
	    changeBean();
	  };
	  private void changeBean() {
	    scriptBean.setScript(scriptField.getText());
	    firePropertyChange("script",null,null);
	  };
	});

      setLayout(new BorderLayout());
      JPanel northPane=new JPanel();
      GridBagLayout layout=new GridBagLayout();
      northPane.setLayout(layout);

      GridBagConstraints constraints=new GridBagConstraints();constraints.fill=GridBagConstraints.BOTH;
      JLabel label=new JLabel("Name:",JLabel.RIGHT);constraints.weightx=0;
      layout.setConstraints(label,constraints);
      northPane.add(label);
      constraints.weightx=1;
      constraints.gridwidth=GridBagConstraints.REMAINDER;
      layout.setConstraints(nameField,constraints);
      northPane.add(nameField);

      constraints=new GridBagConstraints();constraints.fill=GridBagConstraints.BOTH;
      label=new JLabel("Language:",JLabel.RIGHT);constraints.weightx=0;

      layout.setConstraints(label,constraints);
      northPane.add(label);
      constraints.weightx=1;
      constraints.gridwidth=GridBagConstraints.REMAINDER;
      layout.setConstraints(languageField,constraints);
      northPane.add(languageField);

      add(northPane,BorderLayout.NORTH);
      add(new JScrollPane(scriptField),BorderLayout.CENTER);
    };
    public void setObject(Object bean) {
      scriptBean=(Script)bean;
      System.err.println("%%%"+scriptBean.getScript());
      nameField.setText(scriptBean.getName());
      languageField.setText(scriptBean.getLanguage());
      scriptField.setText(scriptBean.getScript());
      System.err.println("%%%"+scriptField.getText());
      System.err.println("%%%"+scriptBean.getScript());
      
    };
  };
  private BeanDescriptor beanDescriptor=new BeanDescriptor(Script.class,ScriptBeanCustomiser.class);
  public BeanDescriptor getBeanDescriptor() {return beanDescriptor;};
  
};

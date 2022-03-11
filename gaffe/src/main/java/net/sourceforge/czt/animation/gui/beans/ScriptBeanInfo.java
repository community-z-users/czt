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
public class ScriptBeanInfo extends SimpleBeanInfo
{

  private final BeanDescriptor beanDescriptor_ = new BeanDescriptor(
      Script.class, ScriptBeanCustomiser.class);

  public BeanDescriptor getBeanDescriptor()
  {
    return beanDescriptor_;
  };

  /**
   * Obtains the image for Script's icon.
   * @return The image obtained from the file "ScriptIcon.gif".
   */
  public Image getIcon(int iconKind)
  {
    switch (iconKind) {
      case ICON_COLOR_32x32 :
      case ICON_MONO_32x32 :
        return loadImage("ScriptIcon.gif");
      case ICON_COLOR_16x16 :
      case ICON_MONO_16x16 :
        return loadImage("ScriptIcon.gif").getScaledInstance(16, 16,
            Image.SCALE_FAST);
      default :
        throw new Error("iconKind should be one of ICON_COLOR_32x32, "
            + "ICON_MONO_32x32, ICON_COLOR_16x16, ICON_MONO_16x16");
    }
  };

  /**
   * Customiser for customising Scripts.
   */
  public static final class ScriptBeanCustomiser extends JPanel
      implements
        Customizer
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -9072845488427674016L;

	private Script scriptBean_ = null;

    private JTextField nameField_ = new JTextField(20);

    private JTextField languageField_ = new JTextField(20);

    private JTextArea scriptField_ = new JTextArea(5, 20);

    public ScriptBeanCustomiser()
    {
      nameField_.getDocument().addDocumentListener(new DocumentListener()
      {
        public void insertUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void removeUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void changedUpdate(DocumentEvent e)
        {
          changeBean();
        };

        private void changeBean()
        {
          scriptBean_.setName(nameField_.getText());
          firePropertyChange("name", null, null);
        };
      });
      languageField_.getDocument().addDocumentListener(new DocumentListener()
      {
        public void insertUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void removeUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void changedUpdate(DocumentEvent e)
        {
          changeBean();
        };

        private void changeBean()
        {
          scriptBean_.setLanguage(languageField_.getText());
          firePropertyChange("language", null, null);
        };
      });
      scriptField_.getDocument().addDocumentListener(new DocumentListener()
      {
        public void insertUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void removeUpdate(DocumentEvent e)
        {
          changeBean();
        };

        public void changedUpdate(DocumentEvent e)
        {
          changeBean();
        };

        private void changeBean()
        {
          scriptBean_.setScript(scriptField_.getText());
          firePropertyChange("script", null, null);
        };
      });

      setLayout(new BorderLayout());
      JPanel northPane = new JPanel();
      GridBagLayout layout = new GridBagLayout();
      northPane.setLayout(layout);

      GridBagConstraints constraints = new GridBagConstraints();
      constraints.fill = GridBagConstraints.BOTH;
      JLabel label = new JLabel("Name:", JLabel.RIGHT);
      constraints.weightx = 0;
      layout.setConstraints(label, constraints);
      northPane.add(label);
      constraints.weightx = 1;
      constraints.gridwidth = GridBagConstraints.REMAINDER;
      layout.setConstraints(nameField_, constraints);
      northPane.add(nameField_);

      constraints = new GridBagConstraints();
      constraints.fill = GridBagConstraints.BOTH;
      label = new JLabel("Language:", JLabel.RIGHT);
      constraints.weightx = 0;

      layout.setConstraints(label, constraints);
      northPane.add(label);
      constraints.weightx = 1;
      constraints.gridwidth = GridBagConstraints.REMAINDER;
      layout.setConstraints(languageField_, constraints);
      northPane.add(languageField_);

      add(northPane, BorderLayout.NORTH);
      add(new JScrollPane(scriptField_), BorderLayout.CENTER);
    };

    public void setObject(Object bean)
    {
      scriptBean_ = (Script) bean;
      System.err.println("%%%" + scriptBean_.getScript());
      nameField_.setText(scriptBean_.getName());
      languageField_.setText(scriptBean_.getLanguage());
      scriptField_.setText(scriptBean_.getScript());
      System.err.println("%%%" + scriptField_.getText());
      System.err.println("%%%" + scriptBean_.getScript());
    };
  };
};

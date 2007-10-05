package net.sourceforge.czt.modeljunit.gui;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JTextField;

/**
 * DialogPackageSelection.java
 *
 * @author rong
 * ID : 1005450
 * 4th Oct 2007
 * The dialog provides an interface to select package from local 
 * hard drive.
 * */
public class DialogPackageURLSelection extends JDialog
  implements ActionListener
{
  private JTextField m_txtLocation;
  private JTextField m_txtName;
  private JButton m_butPackageLocation;
  private JButton m_butPackageName;
  private JButton m_butSave;
  
  public DialogPackageURLSelection()
  {
    this.setLayout(new GridBagLayout());
    GridBagConstraints cons = new GridBagConstraints();
    // Assign package location
    // Insets(top, left, down, right)
    cons.insets = new Insets(0,16,0,6);
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 0;
    cons.gridy = 0;
    add(new JLabel("Package repositry: "),cons);
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 1;
    cons.gridy = 0;
    cons.gridwidth = 3;
    cons.insets = new Insets(0,0,0,6);
    m_txtLocation = new JTextField(30);
    if(Parameter.getPackageLocation()!=null && Parameter.getPackageLocation().length()>0)
      m_txtLocation.setText(Parameter.getPackageLocation());
    add(m_txtLocation,cons);
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 5;
    cons.gridy = 0;
    cons.ipadx = 16;
    cons.insets = new Insets(3,0,3,6);
    m_butPackageLocation = new JButton("...");
    m_butPackageLocation.addActionListener(this);
    add(m_butPackageLocation,cons);
    // Assign package name
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.insets = new Insets(0,16,0,6);
    cons.weightx = 0.5;
    cons.gridx = 0;
    cons.gridy = 1;
    add(new JLabel("Package Name: "),cons);
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.insets = new Insets(0,0,0,6);
    cons.weightx = 0.5;
    cons.gridx = 1;
    cons.gridy = 1;
    cons.gridwidth = 3;
    m_txtName = new JTextField(30);
    if(Parameter.getPackageName()!=null && Parameter.getPackageName().length()>0)
      m_txtName.setText(Parameter.getPackageName());
    add(m_txtName,cons);
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 5;
    cons.gridy = 1;
    cons.ipadx = 16;
    // Insets(top, left, down, right)
    cons.insets = new Insets(3,0,3,6);
    m_butPackageName = new JButton("...");
    m_butPackageName.addActionListener(this);
    add(m_butPackageName,cons);
    
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 0;
    cons.gridy = 2;
    cons.insets = new Insets(0,16,6,6);
    m_butSave = new JButton("Save to default package");
    m_butSave.addActionListener(this);
    add(m_butSave,cons);
    this.pack();
  }

  @Override
  public void actionPerformed(ActionEvent e)
  {
    //------------ Save the package to default package --------------
    if(e.getSource() == m_butSave)
    {
      Parameter.wirteSettingFile();
    }
    //------------ Choose the package location --------------
    if(e.getSource() == this.m_butPackageLocation)
    {
      JFileChooser chooser = new JFileChooser();
      chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
      chooser.setDialogTitle("Open package location");
      chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));
      int option = chooser.showOpenDialog(this);
      if (option == JFileChooser.APPROVE_OPTION) 
      {
        File dir = chooser.getSelectedFile();
        m_txtLocation.setText(dir.getAbsolutePath());
        Parameter.setPackageLocation(m_txtLocation.getText());
      }
    }
    //------------ Choose the package name --------------
    if(e.getSource() == this.m_butPackageName)
    {
      JFileChooser chooser = new JFileChooser();
      chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
      chooser.setDialogTitle("Set package name");
      if(m_txtLocation.getText()!=null && m_txtLocation.getText().length()>0)
        chooser.setCurrentDirectory(new File(m_txtLocation.getText()));
      int option = chooser.showOpenDialog(this);
      if (option == JFileChooser.APPROVE_OPTION) 
      {
        File dir = chooser.getSelectedFile();
        
        int idx = m_txtLocation.getText().length();
        String name = dir.getAbsolutePath();
        // Check if package name is under the directory of package location
        // if it is return true, otherwise return false.
        if(!name.contains(m_txtLocation.getText()))
        {
          ErrorMessage.DisplayErrorMessage(
              "Invalid package name", 
              "Package has to locate under package location reposity!");
          return;
        }
        name = name.substring(idx, name.length());
        char[] cName = name.toCharArray();
        // Could use replaceAll but in Window File.separator is \
        // in regular expression i have to user "\\" but in Linux
        // File.separator is /, just use "/".
        for(int i=0;i<cName.length;i++)
        {
          if(cName[i] == File.separator.charAt(0))
          {
            if(i == 0)
              cName[0] = ' ';
            else
              cName[i] = '.';
           }
        }
        name = new String(cName);
        Parameter.setPackageName(name.trim());
        m_txtName.setText(Parameter.getPackageName());
      }
    }
    
  }
}

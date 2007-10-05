package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
/**
 * DialogPackageSelection.java
 *
 * @author rong
 * ID : 1005450
 * 30th Aug 2007
 * The dialog provides an interface to select package from local 
 * hard drive.
 * References:
 *      http://forum.java.sun.com/thread.jspa?threadID=714461&tstart=240
 *      http://www.javaworld.com/javaworld/jw-03-2000/jw-03-classload.html
 *      http://java.sun.com/products/jndi/tutorial/beyond/misc/classloader.html
 * @deprecated Use DislogPackageURLSelection.java to replace this class.
 * */
/*
public class DialogPackageSelection extends JDialog
  implements ListSelectionListener, ActionListener
{
  private static final long serialVersionUID = 2823926867321588393L;
  private static DialogPackageSelection m_dialog;

  private JPanel m_panelPackage;
  private JList m_listPackage;
  private DefaultListModel m_modelListPackage;
  private JButton m_butAdd;
  private JButton m_butRemove;
  private JButton m_butEdit;
  private JTextField m_txtPackageName;

  // Bad design I should change it later...
  private PanelTestDesign m_parentPanel;

  /*private DialogPackageSelection(PanelTestDesign parent)
  {
    super.setDefaultLookAndFeelDecorated(false);
    super.setAlwaysOnTop(true);
    super.setDefaultCloseOperation(JDialog.HIDE_ON_CLOSE);

    m_parentPanel = parent;

    m_panelPackage = new JPanel();
    //m_panelPackage.setPreferredSize(new Dimension(600,600));
    m_modelListPackage = new DefaultListModel();
    // Load package names from Setting file
    for(int i=0; i<Parameter.numberOfPackage(); i++)
    {
      m_modelListPackage.addElement((Object)(Parameter.getPackageName(i)));
    }
    m_listPackage = new JList(m_modelListPackage);
    m_listPackage.setSelectedIndex(0);
    m_listPackage.setSelectionMode(ListSelectionModel.SINGLE_INTERVAL_SELECTION);

    m_listPackage.addListSelectionListener(this);
    JScrollPane scroll = new JScrollPane();
    scroll.getViewport().add(m_listPackage);
    m_panelPackage.add(scroll);
    // Initialize buttons
    final int SPACE = 10;
    JPanel buttonPanel = new JPanel();
    buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.Y_AXIS));
    buttonPanel.add(Box.createVerticalStrut(SPACE));
    m_butAdd = new JButton("Add        ");
    m_butAdd.addActionListener(this);
    buttonPanel.add(m_butAdd);

    buttonPanel.add(Box.createVerticalStrut(SPACE));
    m_butRemove = new JButton("Remove");
    m_butRemove.addActionListener(this);
    buttonPanel.add(m_butRemove);

    buttonPanel.add(Box.createVerticalStrut(SPACE));
    m_butEdit= new JButton("Edit        ");
    m_butEdit.addActionListener(this);
    buttonPanel.add(m_butEdit);

    m_txtPackageName = new JTextField();
    m_txtPackageName.setColumns(26);
    m_txtPackageName.setText(Parameter.getPackageName(m_listPackage.getSelectedIndex()));

    this.setLayout(new BorderLayout());
    this.add(m_txtPackageName, BorderLayout.NORTH);
    this.getContentPane().add(m_panelPackage, BorderLayout.CENTER);
    this.getContentPane().add(buttonPanel,BorderLayout.EAST);
    pack();
  }

  public static DialogPackageSelection createPackageSelectionDialog(PanelTestDesign parent)
  {
    if(null == m_dialog)
      m_dialog = new DialogPackageSelection(parent);
    return m_dialog;

  }

  public void valueChanged(ListSelectionEvent e)
  {
    // When element has been removed, the selected index will become -1
    // and the valueChanged event will be triggered. Following if statement
    // is for avoid ArrayIndexOutOfBoundsException.
    if(m_listPackage.getSelectedIndex()<0)
      m_listPackage.setSelectedIndex(0);

    String packagename = (String)m_listPackage.getSelectedValue();
    m_listPackage.setToolTipText("Current package is: "+packagename);
    Parameter.setCurPackage(m_listPackage.getSelectedIndex());
    m_txtPackageName.setText(Parameter.getPackageName(m_listPackage.getSelectedIndex()));
    this.m_parentPanel.updatePackageName();
  }

  public void actionPerformed(ActionEvent e)
  {
    if(e.getSource() == m_butAdd)
    {
      if(Parameter.addPackageName(m_txtPackageName.getText()))
      {
        int index = Parameter.numberOfPackage()-1;
        // Add last package name to the list
        m_modelListPackage.addElement(Parameter.getPackageName(index));
        m_listPackage.setSelectedIndex(index);
      }
    }
    if(e.getSource() == m_butRemove)
    {
      int index = m_listPackage.getSelectedIndex();
      System.out.println("selected: "+index+",in list: "+Parameter.numberOfPackage());
      Parameter.removePackageName(index);
      System.out.println("Again selected: "+index+",in list: "+Parameter.numberOfPackage());
      m_modelListPackage.remove(index);
      m_listPackage.setSelectedIndex(0);
    }
    if(e.getSource() == m_butEdit)
    {
      String path = System.getProperty("java.class.path");
      System.out.println(path);
    }
  }
}*/

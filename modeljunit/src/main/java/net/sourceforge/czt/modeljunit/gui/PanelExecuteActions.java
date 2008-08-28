
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.ListCellRenderer;
import javax.swing.border.Border;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;

public class PanelExecuteActions extends PanelAbstract
    implements
      ActionListener,
      ListSelectionListener
{
  // REF: http://java.sun.com/developer/technicalArticles/InnerWorkings/customjlist/
  // The class models the action item in the action list
  private class ListItem
  {
    private Color color;

    private Color textColor;

    private String value;

    public ListItem(String s)
    {
      color = Color.WHITE;
      textColor = Color.BLACK;
      value = s;
    }

    public void setTextColor(Color c)
    {
      textColor = c;
    }

    public Color getTextColor()
    {
      return textColor;
    }

    public void setBKColor(Color c)
    {
      color = c;
    }

    public Color getBKColor()
    {
      return color;
    }

    public String getValue()
    {
      return value;
    }
  }


  class ActionCellRenderer extends JLabel implements ListCellRenderer
  {
    /**
      * serial version UID
      */
    private static final long serialVersionUID = 8047385899654978931L;

    public ActionCellRenderer()
    {
      // Don't paint behind the component
      setOpaque(true);
    }

    // Set the attributes of the 
    //class and return a reference
    public Component getListCellRendererComponent(JList list, Object value, // value to display
        int index, // cell index
        boolean isSel, // is selected
        boolean chf) // cell has focus?
    {
      // Set the text and 
      //background color for rendering
      setText(((ListItem) value).getValue());
      setBackground(((ListItem) value).getBKColor());
      setForeground(((ListItem) value).getTextColor());
      // Set a border if the 
      //list item is selected
      if (isSel)
        setBorder(BorderFactory.createLineBorder(Color.BLACK, 1));
      else
        setBorder(BorderFactory.createLineBorder(list.getBackground(), 1));
      return this;
    }
  }

  /**
   * serial version id
   */
  private static final long serialVersionUID = -2098899830666068702L;

  private static final String MODEL = "tester.getModel().";

  private static PanelExecuteActions m_panel = null;

  private JLabel m_labModName;

  private String m_strDefName = "No model loaded!";

  private int m_nCurrentSelectedAction;

  private JButton m_butReset;

  private JButton m_butExport;

  private JList m_listActoin;

  private DefaultListModel m_listActionModel;

  private JList m_listExecutionHistory;

  private DefaultListModel m_listExeHisModel;

  // Generated code
  private String[] m_strCodePart;

  // Split pane
  private JSplitPane m_splitPane;

  // Instance 
  private static PanelExecuteActions m_instance;

  public static PanelExecuteActions getPanelExecuteActionsInstance()
  {
    if (m_instance == null)
      m_instance = new PanelExecuteActions();
    return m_instance;
  }

  @Override
  public Object clone()
  {
    return null;
  }

  private PanelExecuteActions()
  {
    this.setLayout(new GridBagLayout());
    //JPanel paneInfo;
    //JPanel paneExeAction;

    //paneInfo = new JPanel();
    //paneInfo.setLayout(new BoxLayout(paneInfo,BoxLayout.X_AXIS));
    GridBagConstraints cons = new GridBagConstraints();
    // Name label
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 0;
    cons.gridy = 0;
    this.add(new JLabel("Model name:"), cons);
    m_labModName = new JLabel(m_strDefName);
    // Name label value
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 1;
    cons.gridy = 0;
    add(m_labModName, cons);
    // White space to fill the form
    cons = new GridBagConstraints();
    cons.weightx = 0.5;
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.anchor = GridBagConstraints.LINE_END;
    cons.gridx = 2;
    cons.gridy = 0;
    cons.gridwidth = 4;
    add(Box.createHorizontalGlue());
    // label action list
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 0;
    cons.gridy = 1;
    this.add(new JLabel("Action list"), cons);
    // label execution history
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.gridx = 1;
    cons.gridy = 1;
    this.add(new JLabel("Action execution history"), cons);
    // Reset button 
    m_butReset = new JButton("Reset action");
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.gridx = 2;
    cons.gridy = 1;
    m_butReset.addActionListener(this);
    this.add(m_butReset, cons);
    // Export button
    m_butExport = new JButton("Export to java file");
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.gridx = 3;
    cons.gridy = 1;
    m_butExport.addActionListener(this);
    this.add(m_butExport, cons);
    // Split component contains action list and execution history list
    cons = new GridBagConstraints();
    cons.fill = GridBagConstraints.HORIZONTAL;
    cons.weightx = 0.5;
    cons.weighty = 1.0;
    // height of split panel
    cons.ipady = 210;
    // Insets(top, left, bottom, right)
    cons.insets = new Insets(6, 0, 0, 0);
    cons.anchor = GridBagConstraints.PAGE_START;
    cons.gridx = 0;
    cons.gridy = 2;
    cons.gridwidth = 6;

    // Create lists
    // Action list
    m_listActionModel = new DefaultListModel();
    m_listActoin = new JList(m_listActionModel);
    m_listActoin.setCellRenderer(new ActionCellRenderer());
    m_listActoin.addListSelectionListener(this);
    m_listActoin.addMouseListener(new MouseAdapter()
    {
      public void mouseClicked(MouseEvent evt)
      {
        if (evt.getClickCount() == 2)
          doAction();
      }
    });
    reloadActionModel();
    // Executed action history list
    m_listExeHisModel = new DefaultListModel();
    m_listExecutionHistory = new JList(m_listExeHisModel);
    JScrollPane scrollActions = new JScrollPane(m_listActoin);
    JScrollPane scrollExeHis = new JScrollPane(m_listExecutionHistory);

    m_splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, scrollActions,
        scrollExeHis);
    m_splitPane.setOneTouchExpandable(true);
    m_splitPane.setDividerLocation(160);
    add(m_splitPane, cons);
    Border blackline = BorderFactory.createLineBorder(Color.black);

    this.setBorder(BorderFactory.createTitledBorder(blackline,
        "Action execution panel"));
  }

  /**
   * 
   * Get generated code from other panel
   * Get rid of statement "tester.generate();"
   * Using statements in action history list replace "tester.generate();"
   * 
   * @param code : the generated code from test design panel
   */
  public void setGeneratedCode(String code)
  {
    String strCode = code;
    m_strCodePart = strCode.split("tester.generate\\(\\d.\\);");
  }

  /**
   * If user load a new model, this function should be involved
   * to reset the action history
   * */
  public void resetActionHistoryList()
  {
    m_nCurrentSelectedAction = -1;
    m_listExeHisModel.clear();
  }

  /**
   * Every time user execute an action this function should be involved
   * to update action list. 
   * */
  public void resetSubComponents()
  {
    //m_nCurrentSelectedAction = -1;
    if (TestExeModel.getModelClass().getName() != null
        && TestExeModel.getModelClass().getName().length() > 0)
      m_labModName.setText(TestExeModel.getModelClass().getName());
    else
      m_labModName.setText(m_strDefName);
    reloadActionModel();
  }

  public static PanelExecuteActions createExecuteActionsPanel()
  {
    if (null == m_panel) {
      m_panel = new PanelExecuteActions();
    }
    return m_panel;
  }

  private void doAction()
  {
    if (!Parameter.isTestRunnable(true))
      return;
    // StringWriter msg = new StringWriter();
    String msg = new String();
    VerboseListener vl = new VerboseListener();
    Tester tester = TestExeModel.getTester(1);
    Model mod = tester.getModel();

    String action = ((ListItem) m_listActoin.getSelectedValue()).getValue();
    tester.addListener(vl);
    // redirect model's output
    //Writer defWriter = mod.getOutput();
    //mod.setOutput(msg);
    // run test manually
    int nActionNum = mod.getActionNumber(action);
    if (mod.isEnabled(nActionNum)) {
      mod.doAction(nActionNum);
      msg = " State: " + mod.getCurrentState().toString();
      m_listExeHisModel.addElement(MODEL + action + "(); // " + msg);
    }
    else
      ErrorMessage.DisplayErrorMessage("Cannot execute the action", "Action "
          + action + " cannot be executed in state: " + mod.getCurrentState());
    // restore model's output
    //mod.setOutput(defWriter);
    // reset action list
    reloadActionModel();
  }

  /** Fill actions into action list */
  void reloadActionModel()
  {
    int idxBackup = m_nCurrentSelectedAction;
    m_listActionModel.clear();
    // Get manual tester
    Tester tester = TestExeModel.getTester(1);
    if (tester == null)
      return;
    Model mod = tester.getModel();
    if (mod == null)
      return;
    int num = mod.getNumActions();
    ListItem item;
    for (int i = 0; i < num; i++) {
      String strAction = mod.getActionName(i).toString();
      item = new ListItem(strAction);
      if (!mod.isEnabled(i))
        item.setTextColor(Color.LIGHT_GRAY);
      if (i == idxBackup) {
        item.setTextColor(Color.WHITE);
        item.setBKColor(Color.GRAY);
      }
      m_listActionModel.addElement(item);
    }
    m_nCurrentSelectedAction = idxBackup;
    m_listActoin.setSelectedIndex(m_nCurrentSelectedAction);
  }

  @Override
  public void valueChanged(ListSelectionEvent e)
  {
    if (!e.getValueIsAdjusting() && e.getSource() == m_listActoin) {
      m_nCurrentSelectedAction = m_listActoin.getSelectedIndex();
    }
    if (!e.getValueIsAdjusting() && e.getSource() == m_listExecutionHistory) {
      System.out.println("action exe history changed");
    }
  }

  /**
   * The function will be call before any other actions be executed.
   * when user load new model from file.
   * @deprecated Should probably use newModel instead?
   */
  void autoModelInitialization()
  {
    if (m_listExeHisModel.getSize() == 0)
      doResetAction();
  }

  public void newModel()
  {
    doResetAction();
    resetSubComponents();
    // Clean the action history
    resetActionHistoryList();
    // Fill actions in action list
    reloadActionModel();
  }

  /**
   * If user reload a new model from PanelTestDesign.
   * This method will be called to reset the new model
   */
  void doResetAction()
  {
    if (!Parameter.isTestRunnable(true))
      return;
    Tester tester = TestExeModel.getTester(1);
    // tester object will be created when user select an algorithm
    if (tester == null) {
      ErrorMessage
          .DisplayErrorMessage("Tester object has not been created",
              "Please check test design pane, especially check the algorithm selection!");
      return;
    }

    Model mod = tester.getModel();
    // Reset the action history list
    m_listExeHisModel.clear();
    // Reset model
    mod.doReset();
    String state = mod.getCurrentState().toString();
    // Update action history list
    m_listExeHisModel.addElement(MODEL + "doReset(); // Reset model to state: "
        + state);
    reloadActionModel();
  }

  @Override
  public void actionPerformed(ActionEvent e)
  {
    //---------------- Reset button handler ---------------- 
    if (e.getSource() == m_butReset)
      doResetAction();
    // ---------------- Export button handler ----------------
    if (e.getSource() == m_butExport) {
      String code = m_strCodePart[0];
      code += System.getProperty("line.separator");
      for (int i = 0; i < m_listExeHisModel.size(); i++) {
        code += "    " + m_listExeHisModel.get(i).toString();
        code += System.getProperty("line.separator");
      }
      code += System.getProperty("line.separator");
      code += m_strCodePart[1];
      saveTestFile(code);
    }
  }

  public void saveTestFile(String code)
  {
    String extension = "java";
    FileChooserFilter javaFileFilter = new FileChooserFilter(extension,
        "Java Files");
    JFileChooser chooser = new JFileChooser();
    chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
    chooser.setDialogTitle("Save test file");
    if (Parameter.getFileChooserOpenMode() == 0)
      chooser
          .setCurrentDirectory(new File(Parameter.getModelChooserDirectory()));
    else
      chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));
    chooser.addChoosableFileFilter(javaFileFilter);
    int option = chooser.showDialog(null, "Export");

    if (option == JFileChooser.APPROVE_OPTION) {
      File f = chooser.getSelectedFile();
      // Set file chooser directory
      Parameter.setModelChooserDirectory(f.getParent());
      // Check the suffix ensure it be .java
      String name[] = f.getName().split("\\.");
      if (name.length != 2) {
        // System.out.println(name[0] + ", " + f.getPath());
        File nf = new File(f.getParent(), name[0] + ".java");
        try {
          nf.createNewFile();
        }
        catch (IOException e1) {
          e1.printStackTrace();
          ErrorMessage.DisplayErrorMessage("Cannot create file",
              "Try select other java file.");
        }
        f.delete();
        f = nf;
      }
      // Write the java file
      try {
        BufferedWriter writer = new BufferedWriter(new FileWriter(f));
        writer.write(code);
        writer.close();
      }
      catch (IOException e1) {
        e1.printStackTrace();
      }
    }
  }
}

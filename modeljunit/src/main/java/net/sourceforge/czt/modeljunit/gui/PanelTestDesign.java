
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.Locale;

import javax.swing.*;

public class PanelTestDesign extends JPanel implements ActionListener
{

  /**
   * 
   */
  private static final long serialVersionUID = 5316043261026727079L;

  // Model panel
  private JPanel m_panelModel;

  private JLabel m_labTestModel = new JLabel("Test Model:");

  private JTextField m_txtFilePath;

  private JButton m_butOpenModel;

  // Algorithm panel
  private final static int H_SPACE = 6;

  private int m_nCurAlgo;

  public int getCurrentAlgorithm()
  {
    return m_nCurAlgo;
  }

  private JPanel m_panelAlgorithmBase;

  private JComboBox m_combAlgorithmSelection = new JComboBox();

  private AlgorithmPanel[] m_panelAlgorithm;

  private OptionPanelDefault m_panelDefaultOption;

  // Coverage matrix panel
  private JPanel m_panelCoverageMatrix;

  private int m_nCheckBox = 3;

  private JCheckBox[] m_checkCoverage;

  private boolean[] m_bChecked;

  // Base panel
  private static PanelTestDesign m_panel = null;

  public static PanelTestDesign createTestDesignPanel()
  {
    if (m_panel == null)
      m_panel = new PanelTestDesign();
    return m_panel;
  }

  private PanelTestDesign()
  {
    // Set test case variable name the name will affect code generation 
    Parameter.setTestCaseVariableName("testCase");
    this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
    // ------ Setup model panel ------
    m_txtFilePath = new JTextField();
    m_txtFilePath.setColumns(26);
    m_butOpenModel = new JButton("...");
    m_butOpenModel.addActionListener(this);
    m_panelModel = new JPanel();
    m_panelModel.setLayout(new FlowLayout());
    m_panelModel.add(m_labTestModel);
    m_panelModel.add(m_txtFilePath);
    m_panelModel.add(m_butOpenModel);
    m_panelModel.setPreferredSize(new Dimension(30, 40));
    this.add(m_panelModel);
    this.add(Box.createVerticalStrut(H_SPACE));
    // ------ Initialize algorithm panel ------
    m_nCurAlgo = 0;
    m_panelAlgorithmBase = new JPanel();
    m_panelAlgorithm = new AlgorithmPanel[3];
    m_panelAlgorithm[0] = new AlgorithmPanel("Algorithm selection",
        "Select an algorithm from combobox.", "default.gif");
    m_panelAlgorithm[0].setOptionPanel(new OptionPanelDefault());
    m_panelAlgorithm[1] = new AlgorithmPanel("Random",
        "Random algorithm to travsal the model", "random.gif");
    m_panelAlgorithm[1].setOptionPanel(new OptionPanelRandomWalking());
    m_panelAlgorithm[2] = new AlgorithmPanel("Greedy",
        "Greedy algorithm to travsal the model", "greedy.gif");
    m_panelAlgorithm[2].setOptionPanel(new OptionPanelGreedy());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[0].getAlgorithmName());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[1].getAlgorithmName());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[2].getAlgorithmName());
    m_combAlgorithmSelection.addActionListener(this);
    m_panelAlgorithmBase.add(m_combAlgorithmSelection);
    m_panelDefaultOption = new OptionPanelDefault();
    m_panelAlgorithmBase.add(m_panelDefaultOption);
    this.add(m_panelAlgorithmBase);
    this.add(Box.createHorizontalStrut(H_SPACE));
    // ------ Coverage matrix panel ------
    m_panelCoverageMatrix = new JPanel();
    m_panelCoverageMatrix.setLayout(new BoxLayout(m_panelCoverageMatrix,
        BoxLayout.Y_AXIS));
    m_checkCoverage = new JCheckBox[m_nCheckBox];
    m_checkCoverage[0] = new JCheckBox("State coverage");
    m_checkCoverage[1] = new JCheckBox("Transition coverage");
    m_checkCoverage[2] = new JCheckBox("Transition pair coverage");
    Color bg = new Color(206, 206, 206);

    m_bChecked = new boolean[m_nCheckBox];
    for (int i = 0; i < m_nCheckBox; i++) {
      m_checkCoverage[i].setBackground(bg);
      m_checkCoverage[i].addActionListener(this);
      m_bChecked[i] = false;
      m_panelCoverageMatrix.add(m_checkCoverage[i]);
    }
    m_panelCoverageMatrix.setBackground(bg);
    this.add(m_panelCoverageMatrix);
    this.add(Box.createVerticalGlue());
  }

  public PanelTestDesign clone()
  {
    return null;
  }

  @Override
  public void actionPerformed(ActionEvent e)
  {
    if (e.getSource() == this.m_combAlgorithmSelection) {
      m_panelAlgorithmBase.removeAll();
      m_panelAlgorithmBase.setLayout(new FlowLayout());
      m_panelAlgorithmBase.add(m_combAlgorithmSelection);
      m_nCurAlgo = m_combAlgorithmSelection.getSelectedIndex();
      // Display the algorithm related panel
      if (m_panelAlgorithm[m_nCurAlgo].getOptionPanel() == null)
        System.out.println("Error: Algorithm panel is null");
      m_panelAlgorithmBase.add(m_panelAlgorithm[m_nCurAlgo].getOptionPanel());
      m_panelAlgorithmBase.revalidate();
      // Update the setting
      Parameter.setAlgorithmName(m_panelAlgorithm[m_nCurAlgo].getAlgorithmName());
    }
    if (e.getSource() == m_butOpenModel) {
      String[] extensions = {"java", "class"};
      FileChooserFilter javaFileFilter = new FileChooserFilter(extensions,
          "Java Files");
      JFileChooser chooser = new JFileChooser();
      if(Parameter.getFileChooserOpenMode() == 0)
        chooser.setCurrentDirectory(new File(Parameter.getModelChooserDirectory()));
      else
        chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));
      chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
      chooser.setDialogTitle("Opne model file");
      chooser.addChoosableFileFilter(javaFileFilter);
      int option = chooser.showOpenDialog(this.m_panelModel);

      if (option == JFileChooser.APPROVE_OPTION) {
        File f = chooser.getSelectedFile();
        String[] fileName = f.getName().split("\\.");
        Parameter.setClassName(fileName[0]);
        Parameter.setModelLocation(f.getAbsolutePath());
        // Update the text field component
        m_txtFilePath.setText(Parameter.getClassName() + " ( "
            + Parameter.getModelLocation() + " )");
        // Set file chooser dialog initial directory
        Parameter.setModelChooserDirectory(f.getAbsolutePath());
        m_txtFilePath.setCaretPosition(0);
      }
    }
    // Check the coverage matrix options
    for (int i = 0; i < m_nCheckBox; i++) {
      if (e.getSource() == m_checkCoverage[i]) {
        m_bChecked[i] = !m_bChecked[i];
        Parameter.setCoverageOption(m_bChecked);
      }
    }
  }

  public String generateCode()
  {
    if(m_nCurAlgo<1 
        || m_panelAlgorithm[m_nCurAlgo].hasError()
        || Parameter.getClassName() == null
        || Parameter.getClassName().length()<=0)
      return "";
    StringBuffer buf = new StringBuffer();
    // For random walk using random seed or not
    String strTestCase = Parameter.getTestCaseVariableName();
    if (m_nCurAlgo == 1 && m_panelAlgorithm[1].generateImportLab() != null)
      buf.append(m_panelAlgorithm[1].generateImportLab());

    buf.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.*;"));
    //
    if(m_checkCoverage[0].isSelected() 
        || m_checkCoverage[1].isSelected() 
        || m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;"));
    }
    // Import state coverage lab
    if(m_checkCoverage[0].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.StateCoverage;"));
    }
    // Import transition coverage lab
    if(m_checkCoverage[1].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;"));
    }
    // Import state transition pair coverage lab
    if(m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;"));
    }
    // Generate class content
    buf.append(Indentation.SEP);
    buf.append(Indentation.wrap("public class " + Parameter.getClassName()
        + "Tester"+Indentation.SEP+"{"));
    buf.append(Indentation.wrap("public static void main(String args[])"));
    buf.append(Indentation.wrap("{"));
    // Setup coverage matrix
    if(m_checkCoverage[0].isSelected() 
        || m_checkCoverage[1].isSelected() 
        || m_checkCoverage[2].isSelected())
    {
      if(m_checkCoverage[0].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric stCoverage = new StateCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(stCoverage);"));
      }
      if(m_checkCoverage[1].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric trCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(trCoverage);"));
      }
      if(m_checkCoverage[2].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric tpCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(tpCoverage);"));
      }
      buf.append(Indentation.SEP);
    }
    // Initialize test model
    buf.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    buf.append(Indentation.wrap("ModelTestCase " + strTestCase
        + " = new ModelTestCase(model);"));
    buf.append(Indentation.wrap(strTestCase + ".setVerbosity(2);"));
    // Generate code according to particular algorithm.
    buf.append(Indentation.SEP);
    buf.append(m_panelAlgorithm[m_nCurAlgo].generateCode());
    // Accurate coverage metrics 
    buf.append(Indentation.SEP);
    buf.append(Indentation.wrap("testCase.buildGraph();"));
    buf.append(Indentation.wrap("}"));
    buf.append(Indentation.wrap("}"));

    return buf.toString();
  }


  private class FileChooserFilter extends javax.swing.filechooser.FileFilter
  {
    private String m_description = null;

    private String[] m_extension = null;

    public FileChooserFilter(String[] extension, String description)
    {
      m_description = description;
      m_extension = new String[extension.length];
      for (int i = 0; i < extension.length; i++) {
        m_extension[i] = "." + extension[i].toLowerCase();
      }
    }

    public String getDescription()
    {
      return m_description;
    }

    @Override
    public boolean accept(File f)
    {
      if (f == null)
        return false;
      if (f.isDirectory())
        return true;
      for (int i = 0; i < m_extension.length; i++) {
        if (f.getName().toLowerCase().endsWith(m_extension[i]))
          return true;
      }
      return false;
    }
  }
}

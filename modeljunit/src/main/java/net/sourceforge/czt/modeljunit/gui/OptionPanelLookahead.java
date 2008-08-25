
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.lang.reflect.Constructor;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.border.Border;

import net.sourceforge.czt.modeljunit.LookaheadTester;
import net.sourceforge.czt.modeljunit.examples.FSM;

public class OptionPanelLookahead extends OptionPanelAdapter
    implements
      IAlgorithmParameter
{
  private static final long serialVersionUID = -3923262405217218593L;

  private JTextField m_lookaheadDepth;

  private int m_defaultDepth;

  private JTextField m_maxLength;

  private int m_defaultMaxLength;

  public OptionPanelLookahead(String name, String explain, String imgPath)
  {
    super(name, explain, imgPath);

    if (m_defaultDepth == 0) {
      // find out the default values
      LookaheadTester tmp = new LookaheadTester(new FSM());
      m_defaultDepth = tmp.getDepth();
      m_defaultMaxLength = tmp.getMaxLength();
    }

    this.setLayout(new GridLayout(2, 2));
    add(new JLabel("Lookahead Depth:"));
    m_lookaheadDepth = new JTextField(Integer.toString(m_defaultDepth));
    m_lookaheadDepth.setPreferredSize(new Dimension(60, 20));
    add(m_lookaheadDepth);
    add(new JLabel("Maximum Test Length:"));
    m_maxLength = new JTextField(Integer.toString(m_defaultMaxLength));
    m_maxLength.setPreferredSize(new Dimension(60, 20));
    add(m_maxLength);

    Border edge = BorderFactory.createLineBorder(Color.WHITE);

    this.setBorder(BorderFactory.createTitledBorder(edge,
        "Lookahead algorithm pane"));
  }

  /** Converts a string into an integer value.
   *  Returns minvalue-1 if the string is not legal.
   * @param str     A string to convert
   * @param minvalue The minimum value for this parameter
   * @return   The parameter value, or minvalue-1 on error.
   */
  private int getIntValue(String str, int minvalue)
  {
    int value = 0;
    try {
      value = Integer.parseInt(str);
    }
    catch (NumberFormatException ex) {
      // TODO: report errors to the user somehow/somewhere
      value = minvalue - 1;
    }
    if (value < minvalue) {
      value = minvalue - 1;
    }
    return value;
  }

  @Override
  public String generateCode()
  {
    StringBuffer result = new StringBuffer();

    // Initialize test model
    result.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    result.append(Indentation
        .wrap("LookaheadTester tester = new LookaheadTester(model);"));

    // Calculate the Lookahead depth
    int depth = getIntValue(m_lookaheadDepth.getText(), 1);
    if (depth >= 1 && depth != m_defaultDepth) {
      result.append(Indentation.wrap("tester.setDepth(" + depth + ");"));
    }

    // Calculate the maximum test sequence length
    int maxLength = getIntValue(m_maxLength.getText(), 1);
    if (maxLength >= 1 && maxLength != m_defaultMaxLength) {
      result
          .append(Indentation.wrap("tester.setMaxLength(" + maxLength + ");"));
    }

    return result.toString();
  }

  @Override
  public void initialize(int idx)
  {
    try {
      // Initialize model test case by using the loaded model
      // Tester tester = new GreedyTester(new SimpleSet());
      Class<?> testerClass = Class
          .forName("net.sourceforge.czt.modeljunit.LookaheadTester");
      Constructor<?> con = testerClass.getConstructor(new Class[]{Class
          .forName("net.sourceforge.czt.modeljunit.FsmModel")});
      m_tester[idx] = (LookaheadTester) con
          .newInstance(new Object[]{TestExeModel.getModelObject()});
    }
    catch (Exception exp) {
      exp.printStackTrace();
    }
  }

  @Override
  public String generateImportLab()
  {
    StringBuffer result = new StringBuffer();
    result.append(Indentation
        .wrap("import net.sourceforge.czt.modeljunit.LookaheadTester;"));
    return result.toString();
  }

  @Override
  public void runAlgorithm(int idx)
  {
    // Set the Lookahead depth
    int depth = getIntValue(m_lookaheadDepth.getText(), 1);
    if (depth >= 1 && depth != m_defaultDepth) {
      ((LookaheadTester) m_tester[idx]).setDepth(depth);
    }

    // Set the maximum test sequence length
    int maxLength = getIntValue(m_maxLength.getText(), 1);
    if (maxLength >= 1 && maxLength != m_defaultMaxLength) {
      ((LookaheadTester) m_tester[idx]).setMaxLength(maxLength);
    }
  }
}

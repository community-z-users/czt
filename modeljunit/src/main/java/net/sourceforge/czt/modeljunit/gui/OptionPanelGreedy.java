
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Random;

import javax.swing.Box;
import javax.swing.JCheckBox;
import javax.swing.JLabel;
import javax.swing.JTextField;

import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.examples.SimpleSet;

public class OptionPanelGreedy extends OptionPanelAdapter
    implements
      ActionListener,
      IAlgorithmParameter
{

  /**
   * Serial version ID
   */
  private static final long serialVersionUID = -3666437825873201003L;

  private StringBuffer m_bufCode;

  private JCheckBox m_checkRandomSeed;

  public OptionPanelGreedy()
  {
    // setLayout(new GridLayout(2,3,3,2));
    m_checkRandomSeed = new JCheckBox("Use random seed");
    add(m_checkRandomSeed);
    add(Box.createHorizontalStrut(6));
    add(Box.createHorizontalGlue());

  }

  public void actionPerformed(ActionEvent arg0)
  {
    // TODO Auto-generated method stub

  }


  @Override
  public String generateCode()
  {
    m_bufCode = new StringBuffer();

    // Initialize test model
    m_bufCode.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    m_bufCode.append(Indentation.wrap("Tester tester = new GreedyTester(model);"));
    // To use random seed or not
    if(m_checkRandomSeed.isSelected())
      m_bufCode.append(Indentation.wrap("tester.setRandom(new Random());"));
    else
      m_bufCode.append(Indentation.wrap("tester.setRandom(new Random(tester.FIXEDSEED));"));

    return m_bufCode.toString();
  }

  @Override
  public void initialize()
  {
    // TODO Auto-generated method stub

  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
    m_bufCode = new StringBuffer();
    try {
      m_bufCode.append(bufReader.readLine());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
    try {
      bufWriter.write(m_bufCode.toString());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }
  @Override
  public String generateImportLab()
  {
    m_bufCode = new StringBuffer();
    m_bufCode.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.GreedyTester;"));
    return m_bufCode.toString();
  }

  @Override
  public Tester runAlgorithm() throws InstantiationException, IllegalAccessException, SecurityException, IllegalArgumentException, ClassNotFoundException, NoSuchMethodException, InvocationTargetException
  {
    // Initialize model test case by using the loaded model
    // Tester tester = new GreedyTester(new SimpleSet());
    Class<?> testerClass =
      Class.forName("net.sourceforge.czt.modeljunit.GreedyTester");
    Constructor<?> con = testerClass.getConstructor
      (new Class[]{Class.forName("net.sourceforge.czt.modeljunit.FsmModel")});
    Tester tester =
      (GreedyTester)con.newInstance(new Object[]{Parameter.getModelObject()});
    // Set reset probility
    // caseObj.setResetProbability(Parameter.getResetProbility());
    if(m_checkRandomSeed.isSelected())
    {
      Random rand = new Random();
      tester.setRandom(rand);
    }
    else
    {
      tester.setRandom(new Random(Tester.FIXEDSEED));
    }

    return tester;
  }
}


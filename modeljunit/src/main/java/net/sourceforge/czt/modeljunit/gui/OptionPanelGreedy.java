
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
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
    // If user does not want to use random seed,
    // test will user tester.setRandom(new Random(tester.FIXEDSEED)),
    // Which makes application will generate same tests every time it runs.
    if(m_checkRandomSeed.isSelected())
      m_bufCode.append(Indentation.wrap("tester.setRandom(new Random());"));

    return m_bufCode.toString();
  }

  @Override
  public void initialize()
  {
    try
    {
    // Initialize model test case by using the loaded model
    // Tester tester = new GreedyTester(new SimpleSet());
    Class<?> testerClass =
      Class.forName("net.sourceforge.czt.modeljunit.GreedyTester");
    Constructor<?> con = testerClass.getConstructor
      (new Class[]{Class.forName("net.sourceforge.czt.modeljunit.FsmModel")});
    m_tester =
      (GreedyTester)con.newInstance(new Object[]{Parameter.getModelObject()});
    }catch(Exception exp)
    {
      exp.printStackTrace();
    }
    

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
    if(m_checkRandomSeed.isSelected())
      m_bufCode.append(Indentation.wrap("import java.util.Random;"));
    
    m_bufCode.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.GreedyTester;"));
    return m_bufCode.toString();
  }

  @Override
  public void runAlgorithm()
  {
    
    // Set reset probility
    // caseObj.setResetProbability(Parameter.getResetProbility());
    if(m_checkRandomSeed.isSelected())
    {
      Random rand = new Random();
      m_tester.setRandom(rand);
    }
    else
    {
      m_tester.setRandom(new Random(Tester.FIXEDSEED));
    }
  }
}



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

import net.sourceforge.czt.modeljunit.ModelTestCase;

public class OptionPanelRandomWalking extends OptionPanelAdapter
    implements
      ActionListener,
      IAlgorithmParameter
{

  /**
   * 
   */
  private static final long serialVersionUID = -7675450997014889733L;

  private JLabel m_labelLength;

  private JTextField m_txtLength;

  private StringBuffer m_bufRandomTest;

  private JCheckBox m_checkRandomSeed;
  
  public OptionPanelRandomWalking()
  {
    m_labelLength = new JLabel("Random walk length:");
    m_txtLength = new JTextField();
    m_txtLength.setColumns(5);
    m_txtLength.setText("10");

    m_checkRandomSeed = new JCheckBox("Use random seed");
    
    setLayout(new GridLayout(2,3,3,2));
    add(m_labelLength);
    m_txtLength.setMaximumSize(new Dimension(60,15));
    add(m_txtLength);
    add(Box.createHorizontalGlue());

    add(m_checkRandomSeed);
    add(Box.createHorizontalStrut(6));
    add(Box.createHorizontalGlue());
   
  }

  @Override
  public void actionPerformed(ActionEvent arg0)
  {
    // TODO Auto-generated method stub

  }

  @Override
  public String generateCode()
  {
    if(this.m_txtLength.getText().length()<=0)
      m_bHasError = true;
    m_bufRandomTest = new StringBuffer();
    
    if(m_checkRandomSeed.isSelected())
    {
      m_bufRandomTest.append(Indentation.wrap("Random rand = new Random();"));
      m_bufRandomTest.append(Indentation.wrap(Parameter.getTestCaseVariableName() 
          + ".randomWalk("+ m_txtLength.getText()
          + ", rand);"));
    }
    else
      m_bufRandomTest.append(Indentation.wrap(Parameter.getTestCaseVariableName() 
          +".randomWalk("+ m_txtLength.getText()+ ");"));
    return m_bufRandomTest.toString();
  }

  @Override
  public void initialize()
  {
    // TODO Auto-generated method stub

  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
    m_bufRandomTest = new StringBuffer();
    try {
      m_bufRandomTest.append(bufReader.readLine());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
    try {
      bufWriter.write(m_bufRandomTest.toString());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }
  @Override
  public String generateImportLab()
  {
    if(m_checkRandomSeed.isSelected())
    {
      return Indentation.wrap("import java.util.Random;");
    }
    else
      return null;
  }
  @Override
  public ModelTestCase runAlgorithm() throws InstantiationException, IllegalAccessException, SecurityException, IllegalArgumentException, ClassNotFoundException, NoSuchMethodException, InvocationTargetException
  {
    // Initialize model test case by using the loaded model
    Class<?> testcaseClass = 
      Class.forName("net.sourceforge.czt.modeljunit.ModelTestCase");
    Constructor<?> con = testcaseClass.getConstructor
      (new Class[]{Class.forName("net.sourceforge.czt.modeljunit.FsmModel")});
    ModelTestCase caseObj = 
      (ModelTestCase)con.newInstance(new Object[]{Parameter.getModelObject()});
    // Set reset probility
    caseObj.setResetProbability(Parameter.getResetProbility());
    // Set verbosity
    caseObj.setVerbosity(Parameter.getVerbosity());
    // Set failure verbosity
    caseObj.setFailureVerbosity(Parameter.getFailureVerbosity());
    // Get random walk length
    int length = Integer.valueOf(m_txtLength.getText());
    if(m_checkRandomSeed.isSelected())
    {
      Random rand = new Random();
      caseObj.randomWalk(length,rand);
    }
    else
    {
      caseObj.randomWalk(length);
    }
    if(Parameter.getGenerateGraph())
    {
      caseObj.buildGraph();
      try
      {
        caseObj.printGraphDot(Parameter.getClassName()+".dot");
      }
      catch(Exception exp)
      { exp.printStackTrace();}
    }
    return caseObj;
  }
}

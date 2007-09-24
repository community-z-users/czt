package net.sourceforge.czt.modeljunit.gui;

import java.awt.Dimension;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;


import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Tester;

public class PanelExecuteActions extends JPanel
  implements ListSelectionListener 
{
  /**
   * 
   */
  private static final long serialVersionUID = -2098899830666068702L;

  private static PanelExecuteActions m_panel = null;
  
  private JLabel m_labModName;
  private String m_strDefName = "No model loaded!";
  private int m_nCurrentSelectedAction;
  private JList m_listActoin;
  private JList m_listExecutionHistory;
  
  //Split pane
  private JSplitPane m_splitPane;
  
  private PanelExecuteActions()
  {
    this.setLayout(new BoxLayout(this,BoxLayout.Y_AXIS));
    JPanel paneInfo;
    JPanel paneExeAction;
    
    paneInfo = new JPanel();
    paneInfo.setLayout(new BoxLayout(paneInfo,BoxLayout.X_AXIS));
    
   
    // Information panel
    paneInfo.add(new JLabel("Model name:"));
    m_labModName = new JLabel(m_strDefName);
    paneInfo.add(Box.createHorizontalStrut(16));
    paneInfo.add(m_labModName);
    paneInfo.add(Box.createHorizontalGlue());
    // Test running panel
    paneExeAction = new JPanel();
    // Create lists
    // Action list
    m_listActoin = new JList(TestExeModel.GetModelAction());
    m_listActoin.addListSelectionListener(this);
    m_listActoin.addMouseListener(new MouseAdapter()
      {
        public void mouseClicked(MouseEvent evt) 
        {
          if (evt.getClickCount() == 2) { doAction();}
        }
      });
    // Executed action history list
    m_listExecutionHistory = new JList();
    JScrollPane scrollActions = new JScrollPane(m_listActoin);
    JScrollPane scrollExeHis = new JScrollPane(m_listExecutionHistory);
    
     
    m_splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, scrollActions, scrollExeHis);
    m_splitPane.setPreferredSize(new Dimension(600,350));
    m_splitPane.setOneTouchExpandable(true);
    m_splitPane.setDividerLocation(160);
    paneExeAction.add(m_splitPane);
    
    add(paneInfo);
    add(paneExeAction);
  }

  public void ResetSubComponents()
  {
    if(Parameter.getModelClass().getName() != null &&
        Parameter.getModelClass().getName().length() > 0)
      m_labModName.setText(Parameter.getModelClass().getName());
    else
      m_labModName.setText(m_strDefName);
  }
  
  public static PanelExecuteActions createExecuteActionsPanel()
  {
    if(null == m_panel)
    {
      m_panel = new PanelExecuteActions();
    }
    return m_panel;
  }

  private void doAction()
  {
    Tester tester = TestExeModel.getTester();
    Model mod = tester.getModel();

  }
  
  @Override
  public void valueChanged(ListSelectionEvent e)
  {
    if(!e.getValueIsAdjusting() && e.getSource()==m_listActoin)
    {
      m_nCurrentSelectedAction = m_listActoin.getSelectedIndex();
    }
    if(!e.getValueIsAdjusting() && e.getSource()==m_listExecutionHistory)
    {System.out.println("action exe history changed");}
    
  }

}

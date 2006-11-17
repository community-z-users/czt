
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.GraphicsEnvironment;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JSplitPane;
import javax.swing.border.TitledBorder;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.control.ExitListener;
import net.sourceforge.czt.animation.control.GaffeLoadListener;
import net.sourceforge.czt.animation.control.GaffeSaveListener;
import net.sourceforge.czt.animation.control.ResetListener;
import net.sourceforge.czt.animation.control.ShowConfigDialogListener;
import net.sourceforge.czt.animation.control.ShowOutputDialogListener;
import net.sourceforge.czt.animation.control.ShowSchemaDialogListener;
import net.sourceforge.czt.animation.control.ShowStepTreeDialogListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class MainFrame extends JFrame
{
  private JSplitPane rightSplit;

  private JSplitPane frameSplit;

  /**
   * 
   */
  public MainFrame()
  {
    JMenuBar mainMenuBar = new JMenuBar();
    JMenu fileMenu = new JMenu("File");
    JMenu viewMenu = new JMenu("View");
    JMenu designMenu = new JMenu("Design");
    JMenu toolMenu = new JMenu("Tool");
    JMenu helpMenu = new JMenu("Help");
    JMenuItem openItem = new JMenuItem("Open..");
    JMenuItem loadItem = new JMenuItem("Load..");
    JMenuItem saveItem = new JMenuItem("Save..");
    JMenuItem closeItem = new JMenuItem("Close");
    JMenuItem exitItem = new JMenuItem("Exit");
    JMenuItem outputItem = new JMenuItem("Show Output..");
    JMenuItem stepTreeItem = new JMenuItem("Show StepTree..");
    JMenuItem designItem = new JMenuItem("Design..");
    JMenuItem preferItem = new JMenuItem("Preference..");
    JMenuItem helpItem = new JMenuItem("Help");
    JMenuItem aboutItem = new JMenuItem("About");

    fileMenu.add(openItem);
    fileMenu.add(loadItem);
    fileMenu.add(saveItem);
    fileMenu.add(closeItem);
    fileMenu.add(exitItem);
    viewMenu.add(outputItem);
    viewMenu.add(stepTreeItem);
    designMenu.add(designItem);
    toolMenu.add(preferItem);
    helpMenu.add(helpItem);
    helpMenu.add(aboutItem);
    mainMenuBar.add(fileMenu);
    mainMenuBar.add(viewMenu);
    mainMenuBar.add(designMenu);
    mainMenuBar.add(toolMenu);
    mainMenuBar.add(helpMenu);

    VariablePane statePane = new VariablePane();
    statePane.setBorder(new TitledBorder("state"));
    OperationPane operationPane = new OperationPane();
    OutputPane outputPane = new OutputPane();
    ToolBar toolBar = new ToolBar();
    StepTreePane stp = new StepTreePane();
    StatusLabel statusLabel = new StatusLabel("Ready");

    GaffeUI.setStepTreePane(stp);
    GaffeUI.setToolBar(toolBar);
    GaffeUI.setOutputPane(outputPane);
    GaffeUI.setStatePane(statePane);
    GaffeUI.setOperationPane(operationPane);
    GaffeUI.setStatusLabel(statusLabel);

    rightSplit = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
    rightSplit.setTopComponent(statePane);
    rightSplit.setBottomComponent(outputPane);
    rightSplit.setDividerLocation(0.2);
    frameSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
    frameSplit.setLeftComponent(operationPane);
    frameSplit.setRightComponent(rightSplit);
    frameSplit.setVisible(false);
    JPanel contentPane = (JPanel) this.getContentPane();
    contentPane.setLayout(new BorderLayout());
    contentPane.add(frameSplit, BorderLayout.CENTER);
    contentPane.add(toolBar, BorderLayout.NORTH);
    contentPane.add(new StatusLabel("Ready"), BorderLayout.SOUTH);

    openItem.addActionListener(new ShowSchemaDialogListener());
    loadItem.addActionListener(new GaffeLoadListener());
    saveItem.addActionListener(new GaffeSaveListener());
    closeItem.addActionListener(new ResetListener());
    exitItem.addActionListener(new ExitListener());
    outputItem.addActionListener(new ShowOutputDialogListener());
    stepTreeItem.addActionListener(new ShowStepTreeDialogListener());
    designItem.addActionListener(new ShowConfigDialogListener());

    GraphicsEnvironment env = GraphicsEnvironment.getLocalGraphicsEnvironment();
    this.setBounds(env.getMaximumWindowBounds());
    this.setJMenuBar(mainMenuBar);
    this.setTitle("Community Z Tools -- Gaffe2");
    this.setLocation(0, 0);
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

    GaffeUI.setMainFrame(this);
  }

  public void reset()
  {
    frameSplit.setVisible(true);
    validate();
    rightSplit.setDividerLocation(0.8);
    frameSplit.setDividerLocation(0.2);
  }

  /**
   * @param args
   */
  public static void main(String[] args)
  {
    GaffeUtil.loadExprMap();
    MainFrame mf = new MainFrame();
    mf.setVisible(true);
  }
}


package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JSplitPane;

import net.sourceforge.czt.animation.control.CloseItemListener;
import net.sourceforge.czt.animation.control.DesignItemListener;
import net.sourceforge.czt.animation.control.ExitItemListener;
import net.sourceforge.czt.animation.control.LoadItemListener;
import net.sourceforge.czt.animation.control.OpenItemListener;
import net.sourceforge.czt.animation.control.OutputItemListener;
import net.sourceforge.czt.animation.control.SaveItemListener;
import net.sourceforge.czt.animation.control.StepTreeItemListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class MainFrame extends JFrame
{
  private static JSplitPane frameSplit;

  private static JSplitPane rightSplit;

  private static MainFrame mainFrame;

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

    StatePane statePane = new StatePane();
    OperationPane operationPane = new OperationPane();
    OutputPane outputPane = new OutputPane();
    ToolBar toolBar = new ToolBar();

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
    contentPane.add(new StatusLabel(), BorderLayout.SOUTH);

    StatusLabel.setMessage("Ready");

    openItem.addActionListener(new OpenItemListener());
    loadItem.addActionListener(new LoadItemListener());
    saveItem.addActionListener(new SaveItemListener());
    closeItem.addActionListener(new CloseItemListener());
    exitItem.addActionListener(new ExitItemListener());
    outputItem.addActionListener(new OutputItemListener());
    stepTreeItem.addActionListener(new StepTreeItemListener());
    designItem.addActionListener(new DesignItemListener());

    this.setJMenuBar(mainMenuBar);
    this.setTitle("Communicate Z Tools -- Gaffe2");
    this.setSize(800, 600);
    this.setLocation(80, 60);
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

    mainFrame = this;
  }

  /**
   * @return Returns the splitPane.
   */
  public static JSplitPane getFrameSplit()
  {
    return frameSplit;
  }

  /**
   * @return Returns the rightSplit.
   */
  public static JSplitPane getRightSplit()
  {
    return rightSplit;
  }

  /**
   * @return Returns the mainFrame.
   */
  public static MainFrame getMainFrame()
  {
    return mainFrame;
  }

  /**
   * @param args
   */
  public static void main(String[] args)
  {
    MainFrame mf = new MainFrame();
    mf.setVisible(true);
  }
}

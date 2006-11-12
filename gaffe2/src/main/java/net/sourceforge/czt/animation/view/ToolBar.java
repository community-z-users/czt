
package net.sourceforge.czt.animation.view;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JToolBar;

import net.sourceforge.czt.animation.control.ChangeResultListener;
import net.sourceforge.czt.animation.control.ChangeStepListener;
import net.sourceforge.czt.animation.model.Step;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class ToolBar extends JToolBar implements PropertyChangeListener
{
  private JButton backStepButton;

  private JButton nextStepButton;

  private JButton backResultButton;

  private JButton nextResultButton;

  private JPopupMenu menu;

  private static ToolBar currentToolBar;

  /**
   * 
   */
  public ToolBar()
  {
    String resourceRoot = "./src/main/resources/";
    
    ImageIcon nextResultIcon = new ImageIcon(resourceRoot+"nextResult.jpg");
    ImageIcon backResultIcon = new ImageIcon(resourceRoot+"preResult.jpg");
    ImageIcon nextStepIcon = new ImageIcon(resourceRoot+"nextStep.jpg");
    ImageIcon backStepIcon = new ImageIcon(resourceRoot+"preStep.jpg");

    backStepButton = new JButton(backStepIcon);
    nextStepButton = new JButton(nextStepIcon);
    backResultButton = new JButton(backResultIcon);
    nextResultButton = new JButton(nextResultIcon);

    reset();

    menu = new JPopupMenu();

    backResultButton.addActionListener(new ChangeResultListener(-1));
    nextResultButton.addActionListener(new ChangeResultListener(+1));
    backStepButton.addActionListener(new ChangeStepListener(null));
    nextStepButton.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent arg0)
      {
        // TODO Auto-generated method stub
        menu.removeAll();
        ChangeStepListener csl = new ChangeStepListener(menu);
        for (String operation : StepTree.getAvailableOperations()) {
          JMenuItem item = new JMenuItem(operation);
          item.addActionListener(csl);
          menu.add(item);
        }
        JButton source = (JButton) arg0.getSource();
        menu.show(source, 0, source.getSize().height);
      }
    });

    this.add(backStepButton);
    this.add(backResultButton);
    this.add(nextResultButton);
    this.add(nextStepButton);

    currentToolBar = this;
  }

  /**
   * @return Returns the currentToolBarPane.
   */
  public static ToolBar getCurrentToolBar()
  {
    return currentToolBar;
  }

  /**
   * 
   */
  public void reset()
  {
    backStepButton.setEnabled(false);
    nextStepButton.setEnabled(false);
    backResultButton.setEnabled(false);
    nextResultButton.setEnabled(false);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    Step step = (Step) arg0.getSource();
    backStepButton.setEnabled(StepTree.hasPrevious());
    nextStepButton.setEnabled(StepTree.hasNext());
    backResultButton.setEnabled(step.getIndex() > 0);
    nextResultButton.setEnabled(step.getIndex() < (step.size() - 1)
        || !step.isComplete());
  }
}

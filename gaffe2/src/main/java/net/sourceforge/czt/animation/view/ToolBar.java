
package net.sourceforge.czt.animation.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JToolBar;

import net.sourceforge.czt.animation.control.ChangeResultListener;
import net.sourceforge.czt.animation.control.ChangeStepListener;
import net.sourceforge.czt.animation.control.ChangeStepMenuListener;
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

    backResultButton.addActionListener(new ChangeResultListener(-1));
    nextResultButton.addActionListener(new ChangeResultListener(+1));
    backStepButton.addActionListener(new ChangeStepListener(null));
    nextStepButton.addActionListener(new ChangeStepMenuListener());

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

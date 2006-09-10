
package net.sourceforge.czt.gaffe2.animation.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JToolBar;

import net.sourceforge.czt.gaffe2.animation.control.ChangeResultListener;
import net.sourceforge.czt.gaffe2.animation.control.ChangeStepListener;
import net.sourceforge.czt.gaffe2.animation.control.ChangeStepMenuListener;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;

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
    ImageIcon nextResultIcon = new ImageIcon("./resource/nextResult.jpg");
    ImageIcon backResultIcon = new ImageIcon("./resource/preResult.jpg");
    ImageIcon nextStepIcon   = new ImageIcon("./resource/nextStep.jpg");
    ImageIcon backStepIcon   = new ImageIcon("./resource/preStep.jpg");
    
    backStepButton = new JButton(backStepIcon);
    nextStepButton = new JButton(nextStepIcon);
    backResultButton = new JButton(backResultIcon);
    nextResultButton = new JButton(nextResultIcon);

    reset();

    backStepButton.addActionListener(new ChangeStepListener(null));
    nextStepButton.addActionListener(new ChangeStepMenuListener());
    backResultButton.addActionListener(new ChangeResultListener(-1));
    nextResultButton.addActionListener(new ChangeResultListener(+1));

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
  public void reset(){
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

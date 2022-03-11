
package net.sourceforge.czt.animation.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JToolBar;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.control.ChangeResultListener;
import net.sourceforge.czt.animation.control.ChangeStepListener;
import net.sourceforge.czt.animation.control.ShowOperationMenuListener;
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

  /**
   * Constructor
   */
  public ToolBar()
  {
    String resourceRoot = "./src/main/resources/";

    ImageIcon nextResultIcon = new ImageIcon(resourceRoot + "nextResult.jpg");
    ImageIcon backResultIcon = new ImageIcon(resourceRoot + "preResult.jpg");
    ImageIcon nextStepIcon = new ImageIcon(resourceRoot + "nextStep.jpg");
    ImageIcon backStepIcon = new ImageIcon(resourceRoot + "preStep.jpg");

    backStepButton = new JButton(backStepIcon);
    nextStepButton = new JButton(nextStepIcon);
    backResultButton = new JButton(backResultIcon);
    nextResultButton = new JButton(nextResultIcon);

    reset();

    backResultButton.addActionListener(new ChangeResultListener(-1));
    nextResultButton.addActionListener(new ChangeResultListener(+1));
    backStepButton.addActionListener(new ChangeStepListener(null));
    nextStepButton.addActionListener(new ShowOperationMenuListener());

    this.add(backStepButton);
    this.add(backResultButton);
    this.add(nextResultButton);
    this.add(nextStepButton);
    
    GaffeUI.setToolBar(this);
  }

  /**
   * Reset all the buttons to initial state
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
    StepTree tree = (StepTree) arg0.getSource();
    backStepButton.setEnabled(tree.hasPrevious());
    nextStepButton.setEnabled(tree.hasNext());
    backResultButton.setEnabled(tree.getIndex() > 0);
    nextResultButton.setEnabled(tree.getIndex() < (tree.size() - 1)
        || !tree.isComplete());
  }
}

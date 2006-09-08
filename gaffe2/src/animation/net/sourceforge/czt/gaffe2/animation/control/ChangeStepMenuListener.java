
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

import net.sourceforge.czt.gaffe2.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
public class ChangeStepMenuListener implements ActionListener
{
  private JPopupMenu menu;

  /**
   * 
   */
  public ChangeStepMenuListener()
  {
    menu = new JPopupMenu();
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
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
    menu.setLocation(source.getLocationOnScreen());
    menu.setVisible(true);
  }

}

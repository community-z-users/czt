
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.view.DesignDialog;

public class DesignItemListener implements ActionListener
{

  public DesignItemListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    DesignDialog dd = new DesignDialog();
    dd.setVisible(true);
  }

}

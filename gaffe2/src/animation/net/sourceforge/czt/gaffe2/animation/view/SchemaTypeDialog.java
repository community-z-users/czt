
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.gaffe2.animation.control.CancelListener;
import net.sourceforge.czt.gaffe2.animation.control.SchemaTypeListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class SchemaTypeDialog extends JDialog
{
  //For dynamical genenation
  private JPanel schemaTypePane;

  //For submit action
  private ArrayList<JComboBox> result;

  /**
   * @param parent
   */
  public SchemaTypeDialog(MainFrame parent)
  {
    result = new ArrayList<JComboBox>();
    schemaTypePane = new JPanel();
    JPanel buttonPane = new JPanel();
    JButton confirmButton = new JButton("OK");
    confirmButton.addActionListener(new SchemaTypeListener(result));
    confirmButton.addActionListener(new CancelListener(this));
    buttonPane.add(confirmButton);
    this.setLayout(new BorderLayout());
    this.add(schemaTypePane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
  }

  /**
   * @return
   */
  public JPanel getSchemaPane()
  {
    return schemaTypePane;
  }

  /**
   * @return
   */
  public ArrayList<JComboBox> getResult()
  {
    return result;
  }

}

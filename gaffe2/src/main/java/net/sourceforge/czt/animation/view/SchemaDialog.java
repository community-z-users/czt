
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.util.ArrayList;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.animation.control.DisposeDialogListener;
import net.sourceforge.czt.animation.control.InitializeListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class SchemaDialog extends JDialog
{
  //For dynamical genenation
  private JPanel schemaTypePane;

  //For submit action
  private ArrayList<JComboBox> result;

  /**
   * @param parent
   */
  public SchemaDialog()
  {
    result = new ArrayList<JComboBox>();
    schemaTypePane = new JPanel();
    JPanel buttonPane = new JPanel();
    JButton confirmButton = new JButton("OK");
    confirmButton.addActionListener(new InitializeListener(result));
    confirmButton.addActionListener(new DisposeDialogListener(this));
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

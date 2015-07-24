/**
 * 
 */

package net.sourceforge.czt.animation.control;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.ArrayList;
import java.util.Set;

import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.border.TitledBorder;

import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.animation.view.SchemaDialog;
import net.sourceforge.czt.animation.view.VariablePane;

/**
 * @author Linan Zhang
 *
 */
public class ShowSchemaDialogListener implements ActionListener
{
  /**
   * Constructor
   */
  public ShowSchemaDialogListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    JFileChooser fileChooser = new JFileChooser("Open a Z specification..");
    if (fileChooser.showOpenDialog(null) == JFileChooser.APPROVE_OPTION) {
      this.generateSchemaDialog(fileChooser.getSelectedFile());
    }
  }

  /**
   * Generate a dialog for user to confirm each schema types.
   * @param file
   */
  private void generateSchemaDialog(File file)
  {
    Analyzer analyzer = GaffeFactory.getAnalyzer();
    SchemaDialog scd = new SchemaDialog();
    JPanel contentPane = scd.getSchemaPane();
    analyzer.initialize(file);
    GaffeUtil.addStepTree(file.getName(), new StepTree());
    VariablePane statePane = new VariablePane();
    statePane.setBorder(new TitledBorder("state"));
    statePane.setName(file.getName());
    GaffeUI.getMainFrame().tab(statePane,"RT");
    GaffeUI.setStatePane(statePane);
    Set<String> nameSet = analyzer.getSchemaNames();
    contentPane.setLayout(new GridLayout(nameSet.size(), 2));
    int i = 0;
    JComboBox<String> typeComboBox;
    ArrayList<JComboBox<String>> result = scd.getResult();
    for (String key : nameSet) {
      JLabel label = new JLabel(key);
      label.setToolTipText(analyzer.getSchemaContent(key));
      typeComboBox = new JComboBox<String>();
      typeComboBox.setName(key);
      typeComboBox.addItem(new String("Operation"));
      typeComboBox.addItem(new String("State"));
      typeComboBox.addItem(new String("Initial"));
      typeComboBox.addItem(new String("Ignore"));
      typeComboBox.setSelectedItem(analyzer.getSchemaType(key));
      result.add(typeComboBox);
      contentPane.add(label, i++, 0);
      contentPane.add(typeComboBox, i++, 1);
    }
    scd.validate();
    scd.pack();
    scd.setTitle(file.getName());
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = scd.getSize();
    scd.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
    scd.setModal(true);
    scd.setVisible(true);
  }
}

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

import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.SchemaTypeDialog;

/**
 * @author Linan Zhang
 *
 */
public class OpenItemListener implements ActionListener
{
  MainFrame parent;

  /**
   * 
   */
  public OpenItemListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    parent = MainFrame.getMainFrame();
    JFileChooser fileChooser = new JFileChooser("Open a Z specification..");
    if (fileChooser.showOpenDialog(parent) == JFileChooser.APPROVE_OPTION) {
      this.generateSchemaDialog(fileChooser.getSelectedFile());
    }
  }

  /**
   * @param file
   */
  private void generateSchemaDialog(File file)
  {
    Analyzer analyzer = GaffeFactory.getAnalyzer();
    SchemaTypeDialog scd = new SchemaTypeDialog(parent);
    JPanel contentPane = scd.getSchemaPane();
    analyzer.initialize(file);
    Set<String> nameSet = analyzer.getSchemaNames();
    contentPane.setLayout(new GridLayout(nameSet.size(), 2));
    int i = 0;
    JComboBox typeComboBox;
    ArrayList<JComboBox> result = scd.getResult();
    for (String key : nameSet) {
      JLabel label = new JLabel(key);
      label.setToolTipText(analyzer.getSchemaContent(key));
      typeComboBox = new JComboBox();
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
    scd.setLocation((dim1.width-dim2.width)/2,(dim1.height-dim2.height)/2);
    scd.setModal(true);
    scd.setVisible(true);
  }
}

/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.GridLayout;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.ArrayList;
import java.util.Set;

import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JPanel;

import net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.gaffe2.animation.view.SchemaTypeDialog;

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
    GaffeFactory.getZLive().getSectionManager().reset();
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
    Point position = parent.getLocation();
    scd.setLocation(position.x + 80, position.y + 60);
    scd.setModal(true);
    scd.setVisible(true);
  }
}

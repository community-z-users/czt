
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Toolkit;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import javax.swing.DefaultCellEditor;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableCellEditor;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.control.ConfigChangeListener;
import net.sourceforge.czt.animation.control.CloseDialogListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class ConfigDialog extends JDialog
{
  private ArrayList<DefaultCellEditor> editors = new ArrayList<DefaultCellEditor>(
      3);

  private JTable customMapTable;

  private static Map<String, Class<?>> customMap;

  private static Map<String, List<Class<?>>> availableMap;

  /**
   * Constructor
   */
  public ConfigDialog()
  {
    super();

    // Preparing adapter mapping table
    customMap = GaffeUtil.getCustomMap();
    availableMap = GaffeUtil.getAvailableMap();
    final int rowCount = customMap.keySet().size();
    final int colCount = 2;
    DefaultTableModel model = new DefaultTableModel(rowCount, colCount);
    List<Class<?>> adapterList = null;
    int row = 0;
    for (String key : customMap.keySet()) {
      Class<?> curAdapter = customMap.get(key);
      for (String available : availableMap.keySet()) {
        adapterList = availableMap.get(available);
        if (adapterList.contains(curAdapter)) {
          break;
        }
      }
      model.setValueAt(key, row, 0);
      model.setValueAt(customMap.get(key), row, 1);
      editors.add(new DefaultCellEditor(new JComboBox<>(adapterList.toArray())));
      row++;
    }
    customMapTable = new JTable(model)
    {
      public TableCellEditor getCellEditor(int row, int column)
      {
        int modelColumn = convertColumnIndexToModel(column);

        if (modelColumn == 1 && row < rowCount)
          return (TableCellEditor) editors.get(row);
        else
          return super.getCellEditor(row, column);
      }
    };
    customMapTable.putClientProperty("JTable.autoStartsEdit", Boolean.TRUE);

    // Preparing adapterMapping panel
    JScrollPane customMapPane = new JScrollPane(customMapTable);

    // Preparing ok button
    JButton okButton = new JButton("OK");
    okButton.addActionListener(new ConfigChangeListener(this));

    // Preparing cancel button
    JButton cancelButton = new JButton("Cancel");
    cancelButton.addActionListener(new CloseDialogListener(this));

    // Preparing action panel
    JPanel buttonPane = new JPanel();
    buttonPane.add(okButton);
    buttonPane.add(cancelButton);

    // Preparing this dialog
    this.setLayout(new BorderLayout());
    this.add(customMapPane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.pack();
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = this.getSize();
    this.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
    this.setVisible(true);
  }

  /**
   * @return the customMapTable.
   */
  public JTable getCustomMapTable()
  {
    return customMapTable;
  }

}

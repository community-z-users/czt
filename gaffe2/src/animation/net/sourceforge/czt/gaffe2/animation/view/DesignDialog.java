
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;
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

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.control.CancelListener;
import net.sourceforge.czt.gaffe2.animation.control.ConfigChangeListener;

@SuppressWarnings("serial")
public class DesignDialog extends JDialog
{
  private ArrayList<DefaultCellEditor> editors = new ArrayList<DefaultCellEditor>(3);
  
  private JTable customMapTable;
  
  private static Map<String, Class> customMap;
  
  private static Map<String, List<Class>> availableMap;

  public DesignDialog()
  {
    super();
    
    // Preparing adapter mapping table
    customMap = GaffeFactory.getCustomMap();
    availableMap = GaffeFactory.getAvailableMap();
    final int rowCount = customMap.keySet().size();
    final int colCount = 2;
    DefaultTableModel model = new DefaultTableModel(rowCount, colCount);
    List<Class> adapterList = null;
    int row = 0;
    for (String key : customMap.keySet()) {
      Class curAdapter = customMap.get(key);
      for (String available: availableMap.keySet()){
        adapterList = availableMap.get(available);
        if (adapterList.contains(curAdapter)){
          break;
        }
      }
      model.setValueAt(key, row, 0);
      model.setValueAt(customMap.get(key), row, 1);
      editors.add(new DefaultCellEditor(new JComboBox(adapterList.toArray())));
      row++;
    }
    customMapTable = new JTable(model)
    {
        public TableCellEditor getCellEditor(int row, int column)
        {
            int modelColumn = convertColumnIndexToModel( column );

            if (modelColumn == 1 && row < rowCount)
                return (TableCellEditor)editors.get(row);
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
    cancelButton.addActionListener(new CancelListener(this));
    
    // Preparing action panel
    JPanel buttonPane = new JPanel();
    buttonPane.add(okButton);
    buttonPane.add(cancelButton);
    
    // Preparing this dialog
    this.setLayout(new BorderLayout());
    this.add(customMapPane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.pack();
  }
  /**
   * @return Returns the customMapTable.
   */
  public JTable getCustomMapTable()
  {
    return customMapTable;
  }

}

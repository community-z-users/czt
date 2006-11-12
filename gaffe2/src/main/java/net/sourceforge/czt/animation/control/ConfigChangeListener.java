
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.util.Map;

import javax.swing.JTable;
import javax.swing.table.TableCellEditor;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.view.DesignDialog;

public class ConfigChangeListener implements java.awt.event.ActionListener
{
  private DesignDialog designDialog;

  public ConfigChangeListener(DesignDialog dd)
  {
    designDialog = dd;
  }

  public void actionPerformed(ActionEvent arg0)
  {
    Map<String, Class> customMap = GaffeFactory.getCustomMap();
    JTable customMapTable = designDialog.getCustomMapTable();
    designDialog.setVisible(false);
    String key = "";
    TableCellEditor selected = null;
    Class curAdapter;
    for (int row = 0; row < customMapTable.getRowCount(); row++) {
      key = (String) customMapTable.getValueAt(row, 0);
      selected = customMapTable.getCellEditor(row, 1);
      curAdapter = (Class) (selected.getCellEditorValue());
      customMap.put(key, curAdapter);
      System.out.println(key + " is adapted by " + curAdapter);
    }
    designDialog.dispose();
  }

}


package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.Component;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractCellEditor;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

import net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;

@SuppressWarnings("serial")
public class DesignDialog extends JDialog
{
  private JTable table;
  private static Map<String, Adapter>  adapterMap;
  private static Map<String, List<Adapter>> availableMap;
  
  public DesignDialog()
  {
    super();
    adapterMap = GaffeFactory.getAdapterMap();
    availableMap = GaffeFactory.getAvailableMap();
    int rowCount = availableMap.keySet().size();
    int colCount = 2;
    DefaultTableModel model = new DefaultTableModel(rowCount,colCount);
    String[] adapters;
    List<Adapter> adapterList;
    int i=0;
    int row=0;
    for (String key : availableMap.keySet()){
      adapterList = availableMap.get(key);
      adapters = new String[adapterList.size()];
      for (i=0;i<adapters.length;i++){
        adapters[i] = adapterList.get(i).toString();
      }
      model.setValueAt(key,row,0);
      model.setValueAt(adapters,row,1);
      row++;
    }
    table = new JTable(model);
    ComboBoxRenderer dcr = new ComboBoxRenderer(adapterMap);
    ComboBoxEditor   dce = new ComboBoxEditor(adapterMap);
    table.getColumnModel().getColumn(1).setCellEditor(dce);
    table.getColumnModel().getColumn(1).setCellRenderer(dcr);
    this.add(new JScrollPane(table));
    this.pack();
  }

  private static class ComboBoxEditor extends AbstractCellEditor
    implements TableCellEditor
  {
    private String[] data;
    private ComboBoxRenderer cbr;
    
    public ComboBoxEditor(Map<String, Adapter> adaptermap){
      cbr = new ComboBoxRenderer(adapterMap);
    }
    
    public Object getCellEditorValue() {
      return data;
    }

    public Component getTableCellEditorComponent(JTable table, Object value,
        boolean isSelected, int row, int column)
    {
      data = (String[]) value; 
      return cbr.getTableCellRendererComponent(table, value, isSelected, true, row, column);
    }
  }
  
  private static class ComboBoxRenderer extends JComboBox
      implements TableCellRenderer
  {
    private HashMap<String, String> map;
    
    public ComboBoxRenderer(Map<String, Adapter> adaptermap){
      map = new HashMap<String, String>();
      for (String key: adapterMap.keySet()){
        map.put(key,adapterMap.get(key).toString());
      }
    }
    
    public Component getTableCellRendererComponent(JTable table, Object value,
        boolean isSelected, boolean hasFocus, int row, int column)
    {
      map.put(table.getValueAt(row,0).toString(),this.getSelectedItem().toString());
      removeAllItems();
      String[] choices = (String[])value;
      for(String s: choices){
        addItem(s);
      }
      this.setSelectedItem(adapterMap.get(table.getValueAt(row,0)).toString());
      return this;
    }
  }

}

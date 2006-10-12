
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.BoxLayout;
import javax.swing.JComponent;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.border.TitledBorder;

import net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class VariablePane extends JScrollPane implements PropertyChangeListener
{
  protected JPanel contentPane;

  protected HashMap<String, Adapter> componentMap;

  /**
   * 
   */
  public VariablePane()
  {
    componentMap = new HashMap<String, Adapter>();
    contentPane = new JPanel();
    contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
    this.getViewport().setView(contentPane);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    Step source = (Step) arg0.getSource();
    HashMap<String, Expr> result = source.getResultSelected();
    contentPane.removeAll();
    Adapter adapter = null;
    for (String key : componentMap.keySet()) {
      adapter = componentMap.get(key);
      adapter.setExpr(result.get(key));
      this.add(key, adapter.getComponent());
    }
    contentPane.validate();
    this.repaint();
  }

  /**
   * @param key
   * @param jc
   */
  public void add(String key, JComponent jc)
  {
    Map<String, List<Class>> availableMap = GaffeFactory.getAvailableMap();
    List<Class> adapterList = availableMap.get(componentMap.get(key).getExpr().getClass().getSimpleName());
    final JPopupMenu popupMenu = new JPopupMenu();
    for (Class clazz: adapterList){
      final JMenuItem menuItem = new JMenuItem(clazz.getSimpleName());
      menuItem.addActionListener(new ActionListener(){
        public void actionPerformed(ActionEvent actionEvent){
          System.out.println(menuItem.getText());
        }
      });
      popupMenu.add(menuItem);
    }
    JPanel pane = new JPanel(new BorderLayout());
    pane.setBorder(new TitledBorder(key));
    pane.add(new JScrollPane(jc), BorderLayout.CENTER);
    pane.addMouseListener(new MouseAdapter(){
      public void mousePressed(MouseEvent mouseEvent){
        if (mouseEvent.getButton() == MouseEvent.BUTTON2){
          popupMenu.setLocation(mouseEvent.getPoint());
          popupMenu.setVisible(true);
        }
      }
    });
    contentPane.add(pane);
  }

  /**
   * 
   */
  public void update()
  {
    contentPane.removeAll();
    for (String key : componentMap.keySet()) {
      this.add(key, componentMap.get(key).getComponent());
    }
    contentPane.validate();
  }

  public void reset(){
    contentPane.removeAll();
    componentMap.clear();
  }
  /**
   * @return Returns the contentPane.
   */
  public JPanel getContentPane()
  {
    return contentPane;
  }

  /**
   * @return Returns the componentMap.
   */
  public HashMap<String, Adapter> getComponentMap()
  {
    return componentMap;
  }

  /**
   * @param componentMap The componentMap to set.
   */
  public void setComponentMap(HashMap<String, Adapter> componentMap)
  {
    this.componentMap = componentMap;
  }
}

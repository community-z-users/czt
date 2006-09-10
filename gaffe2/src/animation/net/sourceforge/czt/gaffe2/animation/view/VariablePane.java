
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashMap;

import javax.swing.BoxLayout;
import javax.swing.JComponent;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;

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

  protected HashMap<String, JComponent> componentMap;

  /**
   * 
   */
  public VariablePane()
  {
    componentMap = new HashMap<String, JComponent>();
    contentPane = new JPanel();
    contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
    this.getViewport().setView(contentPane);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    HashMap<String, JComponent> newMap = null;
    Step source = (Step) arg0.getSource();
    HashMap<String, Expr> result = source.getResultSelected();
    newMap = GaffeFactory.exprMapToComponentMap(newMap, result);
    contentPane.removeAll();
    for (String key : componentMap.keySet()) {
      componentMap.put(key, newMap.get(key));
      this.add(key, newMap.get(key));
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
    JPanel pane = new JPanel(new BorderLayout());
    pane.setBorder(new TitledBorder(key));
    if (jc instanceof JTextField) {
      pane.add((JTextField) jc, BorderLayout.CENTER);
    }
    else if (jc instanceof JList) {
      pane.add(new JScrollPane((JList) jc), BorderLayout.CENTER);
    }
    else if (jc instanceof JTable) {
      pane.add(new JScrollPane((JTable) jc), BorderLayout.CENTER);
    }
    contentPane.add(pane);
  }

  /**
   * 
   */
  public void update()
  {
    contentPane.removeAll();
    for (String key : componentMap.keySet()) {
      this.add(key, componentMap.get(key));
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
  public HashMap<String, JComponent> getComponentMap()
  {
    return componentMap;
  }

  /**
   * @param componentMap The componentMap to set.
   */
  public void setComponentMap(HashMap<String, JComponent> componentMap)
  {
    this.componentMap = componentMap;
  }
}

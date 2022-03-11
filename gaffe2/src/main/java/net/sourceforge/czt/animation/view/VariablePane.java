
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.beans.BeanInfo;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyDescriptor;
import java.beans.PropertyEditor;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.border.TitledBorder;

import net.sourceforge.czt.animation.common.adapter.Adapter;
import net.sourceforge.czt.animation.common.adapter.NumExpr_JSpinnerAdapter;
import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.StepTree;
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
   * Constructor
   */
  public VariablePane()
  {
    final VariablePane vp = this;
    componentMap = new HashMap<String, Adapter>();
    contentPane = new JPanel();
    contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
    final JPopupMenu popupMenu = new JPopupMenu();
    final JMenu addMenu = new JMenu("Add..");
    final JMenu remMenu = new JMenu("Remove..");
    final JMenu splMenu = new JMenu("Split..");
    final JMenu layMenu = new JMenu("Layout..");
    addMenu.addMouseListener(new MouseAdapter()
    {
      public void mouseEntered(MouseEvent me)
      {
        addMenu.removeAll();
        for (final String key : componentMap.keySet()) {
          final JMenuItem addItem = new JMenuItem(key);
          addItem.addActionListener(new AddVariableListener(vp));
          addMenu.add(addItem);
        }
      }
    });
    remMenu.addMouseListener(new MouseAdapter()
    {
      public void mouseEntered(MouseEvent me)
      {
        remMenu.removeAll();
        for (final String key : componentMap.keySet()) {
          final JMenuItem remItem = new JMenuItem(key);
          remItem.addActionListener(new RemVariableListener(vp));
          remMenu.add(remItem);
        }
      }
    });
    JMenuItem horSplItem = new JMenuItem("Horizontal Split");
    JMenuItem verSplItem = new JMenuItem("Vertical   Split");
    horSplItem.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        VariablePane pane1 = new VariablePane();
        VariablePane pane2 = new VariablePane();
        HashMap<String, Adapter> componentMap1 = new HashMap<String, Adapter>();
        HashMap<String, Adapter> componentMap2 = new HashMap<String, Adapter>();
        int i = 0;
        for (String key : componentMap.keySet()) {
          if (i % 2 == 0) {
            componentMap1.put(key, componentMap.get(key));
          }
          else {
            componentMap2.put(key, componentMap.get(key));
          }
          i++;
        }
        pane1.setComponentMap(componentMap1);
        pane1.update();
        pane2.setComponentMap(componentMap2);
        pane2.update();
        JSplitPane newSplitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        newSplitPane.setLeftComponent(pane1);
        newSplitPane.setRightComponent(pane2);
        contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
        contentPane.removeAll();
        contentPane.add(newSplitPane);
        contentPane.validate();
      }
    });
    verSplItem.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        VariablePane pane1 = new VariablePane();
        VariablePane pane2 = new VariablePane();
        HashMap<String, Adapter> componentMap1 = new HashMap<String, Adapter>();
        HashMap<String, Adapter> componentMap2 = new HashMap<String, Adapter>();
        int i = 0;
        for (String key : componentMap.keySet()) {
          if (i % 2 == 0) {
            componentMap1.put(key, componentMap.get(key));
          }
          else {
            componentMap2.put(key, componentMap.get(key));
          }
          i++;
        }
        pane1.setComponentMap(componentMap1);
        pane1.update();
        pane2.setComponentMap(componentMap2);
        pane2.update();
        JSplitPane newSplitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        newSplitPane.setTopComponent(pane1);
        newSplitPane.setBottomComponent(pane2);
        contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
        contentPane.removeAll();
        contentPane.add(newSplitPane);
        contentPane.validate();
      }
    });
    splMenu.add(horSplItem);
    splMenu.add(verSplItem);
    JMenuItem layoutItem1 = new JMenuItem(FlowLayout.class.getSimpleName());
    JMenuItem layoutItem2 = new JMenuItem(CardLayout.class.getSimpleName());
    JMenuItem layoutItem3 = new JMenuItem(GridLayout.class.getSimpleName());
    JMenuItem layoutItem4 = new JMenuItem(BoxLayout.class.getSimpleName()
        + "-X");
    JMenuItem layoutItem5 = new JMenuItem(BoxLayout.class.getSimpleName()
        + "-Y");
    layoutItem1.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        contentPane.setLayout(new FlowLayout());
        contentPane.validate();
      }
    });
    layoutItem2.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        final CardLayout cardLayout = new CardLayout();
        JButton preButton = new JButton("Pre");
        preButton.addActionListener(new ActionListener()
        {
          public void actionPerformed(ActionEvent ae)
          {
            cardLayout.previous(contentPane);
          }
        });
        JButton nextButton = new JButton("Next");
        nextButton.addActionListener(new ActionListener()
        {
          public void actionPerformed(ActionEvent ae)
          {
            cardLayout.next(contentPane);
          }
        });
        ToolBar toolBar = GaffeUI.getToolBar();
        toolBar.addSeparator();
        toolBar.add(preButton);
        toolBar.add(nextButton);
        contentPane.setLayout(cardLayout);
        contentPane.validate();
      }
    });
    layoutItem3.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        contentPane.setLayout(new GridLayout());
        contentPane.validate();
      }
    });
    layoutItem4.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.X_AXIS));
        contentPane.validate();
      }
    });
    layoutItem5.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        contentPane.setLayout(new BoxLayout(contentPane, BoxLayout.Y_AXIS));
        contentPane.validate();
      }
    });
    layMenu.add(layoutItem1);
    layMenu.add(layoutItem2);
    layMenu.add(layoutItem3);
    layMenu.add(layoutItem4);
    layMenu.add(layoutItem5);
    popupMenu.add(addMenu);
    popupMenu.add(remMenu);
    popupMenu.add(splMenu);
    popupMenu.add(layMenu);
    this.addMouseListener(new MouseAdapter()
    {
      public void mouseClicked(MouseEvent mouseEvent)
      {
        if (mouseEvent.getButton() == MouseEvent.BUTTON3) {
          popupMenu.show(mouseEvent.getComponent(), mouseEvent.getX(),
              mouseEvent.getY());
        }
      }
    });
    this.getViewport().setView(contentPane);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    StepTree source = (StepTree) arg0.getSource();
    HashMap<String, Expr> result = source.getStep().getResultSelected();
    if (result == null) {
      new WrapperDialog(new MessagePane("No results found!"));
      return;
    }
    contentPane.removeAll();
    Adapter adapter = null;
    for (String key : componentMap.keySet()) {
      adapter = componentMap.get(key);
      adapter.setExpr(result.get(key));
      this.add(key);
    }
    contentPane.validate();
    this.repaint();
  }

  /**
   * Add a new variable into the pane
   * @param key
   * @param jc
   */
  public void add(String key)
  {
    final Map<String, List<Class<?>>> availableMap = GaffeUtil.getAvailableMap();
    final String name = key;
    final Expr expr = componentMap.get(key).getExpr();
    final List<Class<?>> adapterList = availableMap.get(componentMap.get(key)
        .getExpr().getClass().getSimpleName());
    final JPopupMenu popupMenu = new JPopupMenu();
    final JPanel pane = new JPanel(new BorderLayout());
    for (Class<?> adapterClass : adapterList) {
      final JMenuItem menuItem = new JMenuItem(adapterClass.getSimpleName());
      menuItem.addActionListener(new ActionListener()
      {
        public void actionPerformed(ActionEvent actionEvent)
        {
          for (Class<?> adapterClass : adapterList) {
            if (adapterClass.getSimpleName().equals(menuItem.getText())) {
              try {
                Adapter newAdapter = (Adapter) adapterClass.newInstance();
                System.out.println(expr.toString());
                newAdapter.setExpr(expr);
                componentMap.put(name, newAdapter);
                update();
              } catch (IllegalAccessException acceEx) {
                acceEx.printStackTrace();
              } catch (InstantiationException instEx) {
                instEx.printStackTrace();
              }
            }
          }
          popupMenu.setVisible(false);
        }
      });
      popupMenu.add(menuItem);
    }
    final JMenuItem menuItem = new JMenuItem("Properties ...");
    menuItem.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ae)
      {
        try {
          JDialog dialog = new JDialog();
          JPanel contentPane = (JPanel) dialog.getContentPane();
          BeanInfo bi = Introspector.getBeanInfo(NumExpr_JSpinnerAdapter.class);
          PropertyDescriptor[] pds = bi.getPropertyDescriptors();
          contentPane.setLayout(new GridLayout(pds.length, 2));
          int i = 0;
          for (PropertyDescriptor pd : pds) {
            PropertyEditor pe = pd.createPropertyEditor(componentMap.get(name));
            System.out.println(pe);
            contentPane.add(
                new JLabel(pds[i].getName() + " :", JLabel.TRAILING), i, 0);
            contentPane.add(pe.getCustomEditor(), i, 1);
            i++;
          }
          dialog.pack();
          dialog.setLocationRelativeTo(contentPane);
          dialog.setVisible(true);
        } catch (IntrospectionException introEx) {
          introEx.printStackTrace();
        }
      }
    });
    popupMenu.add(menuItem);
    pane.setBorder(new TitledBorder(key));
    pane.add(new JScrollPane(componentMap.get(key).getComponent()),
        BorderLayout.CENTER);
    pane.addMouseListener(new MouseAdapter()
    {
      public void mouseClicked(MouseEvent mouseEvent)
      {
        if (mouseEvent.getButton() == MouseEvent.BUTTON3) {
          popupMenu.show(mouseEvent.getComponent(), mouseEvent.getX(),
              mouseEvent.getY());
        }
      }
    });
    contentPane.add(pane);
  }

  /**
   * remove a variable from a existing pane
   */
  public void remove(String key)
  {
    contentPane.remove(componentMap.get(key).getComponent().getParent()
        .getParent());
  }

  /**
   * update all the variables displayed
   */
  public void update()
  {
    contentPane.removeAll();
    for (String key : componentMap.keySet()) {
      this.add(key);
    }
    contentPane.validate();
  }

  /**
   * reset the container into empty state
   */
  public void reset()
  {
    contentPane.removeAll();
    componentMap.clear();
  }

  /**
   * @return the contentPane. the container itself
   */
  public JPanel getContentPane()
  {
    return contentPane;
  }

  /**
   * @return the componentMap.
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

  /**
   * add a new Variable.
   */
  public class AddVariableListener implements ActionListener
  {
    VariablePane vp;

    public AddVariableListener(VariablePane vp)
    {
      this.vp = vp;
    }

    public void actionPerformed(ActionEvent ae)
    {
      JMenuItem menuItem = (JMenuItem) ae.getSource();
      vp.add(menuItem.getText());
      vp.validate();
    }
  }

  /**
   * remove an existing variable
   */
  public class RemVariableListener implements ActionListener
  {
    VariablePane vp;

    public RemVariableListener(VariablePane vp)
    {
      this.vp = vp;
    }

    public void actionPerformed(ActionEvent ae)
    {
      JMenuItem menuItem = (JMenuItem) ae.getSource();
      vp.remove(menuItem.getText());
      vp.validate();
    }
  }
}

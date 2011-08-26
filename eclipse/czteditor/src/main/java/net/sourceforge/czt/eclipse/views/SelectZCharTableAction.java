
package net.sourceforge.czt.eclipse.views;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import net.sourceforge.czt.eclipse.CZTPluginImages;
import net.sourceforge.czt.eclipse.views.ZCharMapView.DialectTable;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IContributionManager;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.ToolItem;

/**
 * Adapted from org.eclipse.ui.internal.console.OpenConsoleAction
 * 
 * @author Andrius Velykis
 */
public class SelectZCharTableAction extends Action implements IMenuCreator
{

  private static final String DEFAULT_LABEL = "Select Dialect";
  
  private final ZCharMapView charView;

  private final List<DialectTable> charTables = new ArrayList<DialectTable>();

  private IContributionManager mgr;
  private Menu fMenu;

  public SelectZCharTableAction(ZCharMapView charView, Collection<DialectTable> charTables)
  {
    this.charView = charView;
    this.charTables.addAll(charTables);
    
    setText(DEFAULT_LABEL);
    setToolTipText("Select Dialect to Display Its Character Table");
    setImageDescriptor(CZTPluginImages.DESC_CHAR_TABLE);
    setMenuCreator(this);
  }
  
  /* (non-Javadoc)
   * @see org.eclipse.jface.action.IMenuCreator#dispose()
   */
  @Override
  public void dispose()
  {
    charTables.clear();
  }

  /*
   * @see org.eclipse.jface.action.Action#runWithEvent(org.eclipse.swt.widgets.Event)
   * @since 3.5
   */
  @Override
  public void runWithEvent(Event event)
  {
    if (event.widget instanceof ToolItem) {
      ToolItem toolItem = (ToolItem) event.widget;
      Control control = toolItem.getParent();
      Menu menu = getMenu(control);

      Rectangle bounds = toolItem.getBounds();
      Point topLeft = new Point(bounds.x, bounds.y + bounds.height);
      menu.setLocation(control.toDisplay(topLeft));
      menu.setVisible(true);
    }
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.action.IMenuCreator#getMenu(org.eclipse.swt.widgets.Control)
   */
  @Override
  public Menu getMenu(Control parent)
  {
    if (fMenu != null) {
      fMenu.dispose();
    }

    fMenu = new Menu(parent);
    for (DialectTable table : charTables) {
      ActionContributionItem item = new ActionContributionItem(new DialectTableAction(table));
      item.fill(fMenu, -1);
    }
    return fMenu;
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.action.IMenuCreator#getMenu(org.eclipse.swt.widgets.Menu)
   */
  @Override
  public Menu getMenu(Menu parent)
  {
    return null;
  }

  public void setCurrentTable(DialectTable table) {
    setText(table.getLabel());
    if (mgr != null) {
      mgr.update(true);
    }
  }
  
  public void setManager(IContributionManager mgr) {
    this.mgr = mgr;
  }

  private static String getActionText(DialectTable table) {
    String text = table.getLabel();
    int mnemonicIndex = text.indexOf(table.getMnemonic());
    if (mnemonicIndex >= 0) {
      text = (new StringBuilder(text)).insert(mnemonicIndex, "&").toString();
    }
    
    return text;
  }
  
  private class DialectTableAction extends Action
  {

    private final DialectTable table;

    public DialectTableAction(DialectTable table)
    {
      setText(getActionText(table));
      this.table = table;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.action.IAction#run()
     */
    @Override
    public void run()
    {
      charView.selectTable(table);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.action.IAction#runWithEvent(org.eclipse.swt.widgets.Event)
     */
    @Override
    public void runWithEvent(Event event)
    {
      run();
    }
  }

}

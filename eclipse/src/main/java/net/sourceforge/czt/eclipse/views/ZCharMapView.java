
package net.sourceforge.czt.eclipse.views;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.util.ZChar;
import net.sourceforge.czt.eclipse.util.ZCharTable;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.TableCursor;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.MouseTrackListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.IDocumentProvider;

/**
 * The view shows the Z characters in a table
 */

/**
 * @author Chengdong Xu
 */
public class ZCharMapView extends ViewPart
{
  private ZCharTable zchTable = new ZCharTable();

  private Combo charCombo;

  private TableViewer viewer;

  private Label descriptionLabel;

  private TextEditor textEditor;
  
  private FontData fCharMapViewFontData = new FontData();
  
  private Font fCharMapViewFont;
  
  private TableCursor fTableCursor;

  //private Action action1;
  //private Action action2;
  //private Action doubleClickAction;

  /*
   * The content provider class is responsible for
   * providing objects to the view. It can wrap
   * existing objects in adapters or simply return
   * objects as-is. These objects may be sensitive
   * to the current input of the view, or ignore
   * it and always show the same content 
   * (like Task List, for example).
   */

  class ViewContentProvider implements IStructuredContentProvider
  {
    public void inputChanged(Viewer v, Object oldInput, Object newInput)
    {
    }

    public void dispose()
    {
    }

    public Object[] getElements(Object parent)
    {
      return zchTable.getZCharTable();
    }
  }

  class ViewLabelProvider extends LabelProvider implements ITableLabelProvider
  {
    public String getColumnText(Object obj, int index)
    {
      //return getText(obj);
      Object zchar[] = (Object[]) obj;
      if (index == 0) {
        return (String) zchar[0];
      }
      else if (index > 0 && index < zchar.length) {
        ZChar zch = (ZChar) zchar[index];
        return zch.getLabel();
      }
      else {
        return "";
      }
    }

    public Image getColumnImage(Object obj, int index)
    {
      //return getImage(obj);
      return null;
    }

    public Image getImage(Object obj)
    {
      return PlatformUI.getWorkbench().getSharedImages().getImage(
          ISharedImages.IMG_OBJ_ELEMENT);
    }
  }

  //	class NameSorter extends ViewerSorter {
  //	}

  /**
   * The constructor.
   */
  public ZCharMapView()
  {
  }

  /**
   * This is a callback that will allow us
   * to create the viewer and initialize it.
   */
  public void createPartControl(Composite parent)
  {
    fCharMapViewFontData.setName("CZT");
    fCharMapViewFontData.setHeight(10);
    fCharMapViewFontData.setStyle(SWT.BOLD);
    fCharMapViewFont = new Font(Display.getDefault(), fCharMapViewFontData);
    createTable(parent);

    //		makeActions();
    //		hookContextMenu();
    //		hookDoubleClickAction();
    //		contributeToActionBars();
  }

  private void createTable(Composite parent)
  {
    FormData formData;
    parent.setLayout(new FormLayout());

    descriptionLabel = new Label(parent, SWT.CENTER);
    formData = new FormData();
    formData.top = new FormAttachment(100, -35);
    formData.left = new FormAttachment(0, 5);
    formData.right = new FormAttachment(100, -5);
    formData.bottom = new FormAttachment(100, -5);
    descriptionLabel.setLayoutData((formData));

    charCombo = new Combo(parent, SWT.READ_ONLY);
    charCombo.setItems(new String[]{"Unicode Markup", "Latex Markup",
        "Hex String"});
    charCombo.select(0);
    charCombo.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent event)
      {

      }
    });
    formData = new FormData();
    formData.top = new FormAttachment(0, 5);
    formData.left = new FormAttachment(0, 5);
    charCombo.setLayoutData((formData));

    viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);

    final Table table = viewer.getTable();
    table.setFont(fCharMapViewFont);
    fTableCursor = new TableCursor(table, SWT.NULL);
    fTableCursor.setFont(fCharMapViewFont);
    
    table.setHeaderVisible(false);
    table.setLinesVisible(true);
    table.addMouseListener(new MouseListener()
    {
      private Point fMousePos = null;

      private ZChar zch = null;

      public void mouseDown(MouseEvent event)
      {
        fMousePos = new Point(event.x, event.y);
      }

      public void mouseUp(MouseEvent event)
      {
        if ((event.x != fMousePos.x) || (event.y != fMousePos.y))
          return;

        zch = getZCharAtPoint(table, fMousePos);
        if (zch != null) {
          insertZChar(zch);
        }
      }

      public void mouseDoubleClick(MouseEvent event)
      {
      }
    });
    table.addMouseTrackListener(new MouseTrackListener()
    {
      public void mouseEnter(MouseEvent event)
      {

      }

      public void mouseExit(MouseEvent event)
      {
        table.setToolTipText("");
      }

      public void mouseHover(MouseEvent event)
      {
        table.setToolTipText("");
        ZChar zch = getZCharAtPoint(table, new Point(event.x, event.y));
        if (zch != null) {
          String descString = zch.getDescription() + "(Unicode:"
              + zch.getUnicode() + "; Latex:" + zch.getLatex();
          table.setToolTipText(descString);
        }
      }
    });

    TableColumn tableColumn = new TableColumn(table, SWT.LEFT);
    tableColumn.setText("");
    tableColumn.setWidth(100);
    for (int i = 1; i < zchTable.getColumnCount(); i++) {
      tableColumn = new TableColumn(table, SWT.CENTER);
      tableColumn.setText("");
      tableColumn.setWidth(50);
    }

    table.pack();

    formData = new FormData();
    formData.top = new FormAttachment(charCombo, 5);
    formData.bottom = new FormAttachment(descriptionLabel, -5);
    formData.left = new FormAttachment(0, 5);
    formData.right = new FormAttachment(100, -5);
    table.setLayoutData((formData));

    viewer.setLabelProvider(new ViewLabelProvider());
    viewer.setContentProvider(new ViewContentProvider());
    //		viewer.setSorter(new NameSorter());
    viewer.setInput(zchTable.getZCharTable());
  }

  private ZChar getZCharAtPoint(final Table table, Point pt)
  {
    Rectangle clientArea = table.getClientArea();
    if (!clientArea.contains(pt)) {
      return null;
    }
    int index = table.getTopIndex();
    while (index < table.getItemCount()) {
      boolean visible = false;
      TableItem item = table.getItem(index);
      for (int i = 1; i < table.getColumnCount(); i++) {
        Rectangle rect = item.getBounds(i);
        if (rect.contains(pt)) {
          Object ch = zchTable.getValueAt(index, i);
          if (ch instanceof ZChar) {
            return (ZChar) ch;
          }
        }
        if (!visible && rect.intersects(clientArea)) {
          visible = true;
        }
      }
      if (!visible)
        return null;
      index++;
    }
    return null;
  }

  private void insertZChar(ZChar zch)
  {
    try {
      String fileType = null;
      String stringInput = null;
      textEditor = (TextEditor) getSite().getPage().getActiveEditor();
      IDocumentProvider dp = textEditor.getDocumentProvider();
      IDocument doc = dp.getDocument(textEditor.getEditorInput());
      ITextSelection selection = (ITextSelection) textEditor
          .getSelectionProvider().getSelection();

      if (textEditor instanceof ZEditor)
        fileType = ((ZEditor) textEditor).getFileType();

      if (fileType == null)
        stringInput = zch.getLabel();
      else if (fileType.equalsIgnoreCase(IZFileType.FILETYPE_LATEX))
        stringInput = zch.getLatex();
      else if (fileType.equalsIgnoreCase(IZFileType.FILETYPE_UTF8)
          || fileType.equalsIgnoreCase(IZFileType.FILETYPE_UTF16))
        stringInput = zch.getUnicode();
      else
        stringInput = zch.getHexString();

      doc.replace(selection.getOffset(), selection.getLength(), stringInput);
      getSite().getPage().activate(textEditor);
      textEditor.selectAndReveal(selection.getOffset() + stringInput.length(),
          0);

    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /*
   private void hookContextMenu() {
   MenuManager menuMgr = new MenuManager("#PopupMenu");
   menuMgr.setRemoveAllWhenShown(true);
   menuMgr.addMenuListener(new IMenuListener() {
   public void menuAboutToShow(IMenuManager manager) {
   ZCharMapView.this.fillContextMenu(manager);
   }
   });
   Menu menu = menuMgr.createContextMenu(viewer.getControl());
   viewer.getControl().setMenu(menu);
   getSite().registerContextMenu(menuMgr, viewer);
   }

   private void contributeToActionBars() {
   IActionBars bars = getViewSite().getActionBars();
   fillLocalPullDown(bars.getMenuManager());
   fillLocalToolBar(bars.getToolBarManager());
   }

   private void fillLocalPullDown(IMenuManager manager) {
   manager.add(action1);
   manager.add(new Separator());
   manager.add(action2);
   }

   private void fillContextMenu(IMenuManager manager) {
   manager.add(action1);
   manager.add(action2);
   // Other plug-ins can contribute there actions here
   manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
   }
   
   private void fillLocalToolBar(IToolBarManager manager) {
   manager.add(action1);
   manager.add(action2);
   }

   private void makeActions() {
   action1 = new Action() {
   public void run() {
   showMessage("Action 1 executed");
   }
   };
   action1.setText("Action 1");
   action1.setToolTipText("Action 1 tooltip");
   action1.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().
   getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));
   
   action2 = new Action() {
   public void run() {
   showMessage("Action 2 executed");
   }
   };
   action2.setText("Action 2");
   action2.setToolTipText("Action 2 tooltip");
   action2.setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().
   getImageDescriptor(ISharedImages.IMG_OBJS_INFO_TSK));
   doubleClickAction = new Action() {
   public void run() {
   ISelection selection = viewer.getSelection();
   Object obj = ((IStructuredSelection)selection).getFirstElement();
   showMessage("Double-click detected on "+obj.toString());
   }
   };
   }

   private void hookDoubleClickAction() {
   viewer.addDoubleClickListener(new IDoubleClickListener() {
   public void doubleClick(DoubleClickEvent event) {
   doubleClickAction.run();
   }
   });
   }
   */
  private void showMessage(String message)
  {
    MessageDialog.openInformation(viewer.getControl().getShell(), "Z Char Map",
        message);
  }

  /**
   * Passing the focus request to the viewer's control.
   */
  public void setFocus()
  {
    viewer.getControl().setFocus();
  }
}
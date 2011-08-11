
package net.sourceforge.czt.eclipse.views;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.TableCursor;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.MouseAdapter;
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
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.IDocumentProvider;

import static java.lang.Math.max;

/**
 * The view shows the Z characters in a table
 */

/**
 * @author Chengdong Xu
 */
public class ZCharMapView extends ViewPart
{
  // Path of Z character file
  private final IPath PATH_Z_TABLE = new Path("lib/ZTable.xml");
  // Path of Object Z character file
  private final IPath PATH_OBJECT_Z_TABLE = new Path("lib/ObjectZTable.xml");
  // Path of Circus character file
  private final IPath PATH_CIRCUS_TABLE = new Path("lib/CircusTable.xml");
  // Path of Z/Eves character file
  private final IPath PATH_ZEVES_TABLE = new Path("lib/ZEvesTable.xml");
  
  private ZCharTable fZTable = new ZCharTable(PATH_Z_TABLE);
  private ZCharTable fObjectZTable = new ZCharTable(PATH_OBJECT_Z_TABLE);
  private ZCharTable fCircusTable = new ZCharTable(PATH_CIRCUS_TABLE);
  private ZCharTable fZEvesTable = new ZCharTable(PATH_ZEVES_TABLE);
  private ZCharTable fCharTable = fZTable;
  
  protected Object fInput;

  private Combo fNotationCombo;
  private TableViewer viewer;
  private TextEditor textEditor;
  private FontData fCharMapViewFontData = new FontData();
  private Font fCharMapViewFont;
  private TableCursor fTableCursor;

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
//      System.out.println("input changed");
      if (newInput != null && oldInput != newInput && newInput instanceof ZCharTable) {
        fCharTable = (ZCharTable)newInput;
        v.refresh();
//        ((TableViewer)v).getTable().pack(true);
//        v.getControl().update();
//        v.getControl().getParent().pack(true);  
      }
    }

    public void dispose()
    {
    }

    public Object[] getElements(Object parent)
    {
      return fCharTable.getZCharTable();
    }
  }

  class ViewLabelProvider extends LabelProvider implements ITableLabelProvider
  {
    public String getColumnText(Object obj, int index)
    {
      //return getText(obj);
      Object zchars[] = (Object[]) obj;
      if (index == 0) {
        return (String) zchars[0];
      }
      else if (index > 0 && index < zchars.length) {
        ZChar zch = (ZChar) zchars[index];
        if (zch == null)
          return null;
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
    
    CZTPlugin.getDefault()
      .getPreferenceStore()
      .addPropertyChangeListener(new IPropertyChangeListener() {

        public void propertyChange(PropertyChangeEvent event)
        {
          String key = event.getProperty();
          if (key.equals(PreferenceConstants.PROP_DIALECT)) {
            String value = String.valueOf(event.getNewValue());
            selectDialectTable(value);
          }
        }
      });
    
    // select current dialect table
    String dialect = CZTPlugin.getDefault().getPreferenceStore()
        .getString(PreferenceConstants.PROP_DIALECT);
    selectDialectTable(dialect);
    updateTableForSelection();

    //		makeActions();
    //		hookContextMenu();
    //		hookDoubleClickAction();
    //		contributeToActionBars();
  }
  
  private void selectDialectTable(String value)
  {
    if ("z".equals(value))
      fNotationCombo.select(0);
    else if ("oz".equals(value))
      fNotationCombo.select(1);
    else if ("circus".equals(value))
      fNotationCombo.select(2);
    else if ("zeves".equals(value)) {
      fNotationCombo.select(3);
    }
  }
  
  private void updateTableForSelection()
  {
    if (viewer != null) {
      switch (fNotationCombo.getSelectionIndex()) {
        case 0:
          viewer.setInput(fZTable);
          break;
        case 1:
          viewer.setInput(fObjectZTable);
          break;
        case 2:
          viewer.setInput(fCircusTable);
          break;
        case 3:
          viewer.setInput(fZEvesTable);
          break;
        default:
          viewer.setInput(fZTable);
      }
    }
  }

  private void createTable(Composite parent)
  {
    FormData formData;
    parent.setLayout(new FormLayout());

    fNotationCombo = new Combo(parent, SWT.READ_ONLY);
    fNotationCombo.setItems(new String[]{"Z", "Object Z",
        "Circus", "Z/Eves"});
    fNotationCombo.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent event)
      {
        updateTableForSelection();
      }
    });
    formData = new FormData();
    formData.top = new FormAttachment(0, 5);
    formData.left = new FormAttachment(0, 5);
    fNotationCombo.setLayoutData((formData));

    viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
    final Table table = viewer.getTable();
//    CZTColorManager manager = new CZTColorManager();
//    Color color = manager.getColor(IZColorConstants.SCHEMA);
    table.setFont(fCharMapViewFont);
    fTableCursor = new TableCursor(table, SWT.NULL);
    fTableCursor.setFont(fCharMapViewFont);
    fTableCursor.addMouseTrackListener(new MouseTrackListener()
    {
      public void mouseEnter(MouseEvent event)
      {
        table.setToolTipText("");
      }

      public void mouseExit(MouseEvent event)
      {
        fTableCursor.setToolTipText("");
        table.setToolTipText("");
      }

      public void mouseHover(MouseEvent event)
      {
        fTableCursor.setToolTipText("");
        table.setToolTipText("");

        ZChar zch = getZCharAtPoint(table, fTableCursor.getLocation());
        if (zch != null) {
          String descString = zch.getDescription() + "(Unicode:"
              + zch.getUnicode() + "; Latex:" + zch.getLatex();
          fTableCursor.setToolTipText(descString);

        }
      }
    });
    
    fTableCursor.addMouseListener(new MouseAdapter() {
      private ZChar zch = null;
      private boolean mousedown = false;

      public void mouseDown(MouseEvent event)
      {
        mousedown = true;
      }

      public void mouseUp(MouseEvent event)
      {
        if (mousedown) {
          mousedown = false;
          Rectangle rect = fTableCursor.getBounds();
          if (!fTableCursor.getBounds().contains(rect.x + event.x, rect.y + event.y))
            return;
          zch = getZCharAtPoint(table, fTableCursor.getLocation());
          if (zch != null) {
            insertZChar(zch);
          }
        }
      }

      public void mouseDoubleClick(MouseEvent event)
      {
      }
    });
    
    fTableCursor.addKeyListener(new KeyListener()
    {
      public void keyPressed(KeyEvent event)
      {

      }

      public void keyReleased(KeyEvent event)
      {
        if (event.character == SWT.CR) {
          ZChar zch = getZCharAtPoint(table, fTableCursor.getLocation());
          if (zch != null)
            insertZChar(zch);
        }
      }
    });

    table.setHeaderVisible(false);
    table.setLinesVisible(true);
    table.addMouseListener(new MouseListener()
    {
      private ZChar fDownChar = null;
      private ZChar fUpChar = null;
      private boolean mousedown = false;

      public void mouseDown(MouseEvent event)
      {
        mousedown = true;
        Point p = new Point(event.x, event.y);
        fDownChar = getZCharAtPoint(table, p);
      }

      public void mouseUp(MouseEvent event)
      {
        if (mousedown) {
          mousedown = false;
          Point p = new Point(event.x, event.y);
          fUpChar = getZCharAtPoint(table, p);
          if (fUpChar != null && fUpChar.equals(fDownChar)) {
            insertZChar(fUpChar);
          }
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

    table.setRedraw(false);
    
    // get the longest column count of all tables
    int maxColumnCount = max(
        fZTable.getColumnCount(),
        max(fObjectZTable.getColumnCount(),
            max(fCircusTable.getColumnCount(), 
                fZEvesTable.getColumnCount())));
    
    TableColumn tableColumn = new TableColumn(table, SWT.LEFT);
    tableColumn.setText("");
    tableColumn.setWidth(100);
    for (int i = 1; i < maxColumnCount; i++) {
      tableColumn = new TableColumn(table, SWT.CENTER);
      tableColumn.setText("");
      tableColumn.setWidth(50);
    }
    
    table.pack(true);
    table.setRedraw(true);
    
    formData = new FormData();
    formData.top = new FormAttachment(fNotationCombo, 5);
    formData.bottom = new FormAttachment(100, -5);
    formData.left = new FormAttachment(0, 5);
    formData.right = new FormAttachment(100, -5);
    table.setLayoutData((formData));

    viewer.setLabelProvider(new ViewLabelProvider());
    viewer.setContentProvider(new ViewContentProvider());
    //		viewer.setSorter(new NameSorter());
    viewer.setInput(fZTable);
    
//    fNotationCombo.select(0);
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
          Object ch = fCharTable.getValueAt(index, i);
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
      if (textEditor == null)
        return;
      IDocumentProvider dp = textEditor.getDocumentProvider();
      IDocument doc = dp.getDocument(textEditor.getEditorInput());
      ITextSelection selection = (ITextSelection) textEditor
          .getSelectionProvider().getSelection();

      if (textEditor instanceof ZEditor)
        fileType = ((ZEditor) textEditor).getFileType();

      if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType))
        stringInput = zch.getLatex();
      else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
          || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType))
        stringInput = zch.getUnicode();
      else
        stringInput = zch.getDescription();

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
 */
//  private void showMessage(String message)
//  {
//    MessageDialog.openInformation(viewer.getControl().getShell(), "Z Char Map",
//        message);
//  }

  /**
   * Passing the focus request to the viewer's control.
   */
  public void setFocus()
  {
    viewer.getControl().setFocus();
  }
}
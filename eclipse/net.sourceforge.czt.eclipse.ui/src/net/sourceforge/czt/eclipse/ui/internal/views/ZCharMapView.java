
package net.sourceforge.czt.eclipse.ui.internal.views;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.internal.editors.IDialectChangedListener;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZChar;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZCharTable;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZDialectSupport;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZDialectSupport.ZDialect;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.preferences.ZEditorConstants;
import net.sourceforge.czt.session.Markup;

import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.TableViewerEditor;
import org.eclipse.jface.viewers.TableViewerFocusCellManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.jface.window.ToolTip;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;

import static java.lang.Math.max;

/**
 * The view shows the Z characters in a table 
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZCharMapView extends ViewPart
{
  
  private static final String EDITOR_FONT = ZEditorConstants.FONT_UNICODE;
  
  private TableViewer viewer;
  private Font editorFont;
  private StyledToolTipSupport toolTipSupport;
  
  private SelectZCharTableAction selectAction;
  
  private IDialectChangedListener dialectListener;

  public ZCharMapView()
  {
    super();
  }

  private Font getEditorFont()
  {
    if (editorFont == null) {
      editorFont = JFaceResources.getFont(EDITOR_FONT);
    }

    return editorFont;
  }

  /**
   * This is a callback that will allow us
   * to create the viewer and initialize it.
   */
  @Override
  public void createPartControl(Composite parent)
  {
    
    createTable(parent);
    
    createActions();
    IToolBarManager tbm= getViewSite().getActionBars().getToolBarManager();
    configureToolBar(tbm);
    
    ZDialectSupport.INSTANCE.addDialectChangedListener(dialectListener = 
        new IDialectChangedListener()
        {

          @Override
          public void dialectChanged(String newDialect)
          {
            selectDialectTable(newDialect);
          }
        });
    
    
    // select current dialect table
    selectTable(ZDialectSupport.INSTANCE.getCurrentDialectTableId());
  }

  @Override
  public void dispose()
  {
    if (dialectListener != null) {
      ZDialectSupport.INSTANCE.removeDialectChangedListener(dialectListener);
      dialectListener = null;
    }
    super.dispose();
  }

  private void createActions() {
    this.selectAction = new SelectZCharTableAction(this, ZDialectSupport.INSTANCE.getTableIds());
  }
  
  protected void configureToolBar(IToolBarManager mgr)
  {
    mgr.add(new Separator("dialectGroup")); //$NON-NLS-1$

    selectAction.setManager(mgr);
    ActionContributionItem selectActionItem = new ActionContributionItem(selectAction);
    selectActionItem.setMode(ActionContributionItem.MODE_FORCE_TEXT);
    mgr.add(selectActionItem);
  }
  
  private void selectDialectTable(String dialect)
  {
    selectTable(ZDialect.find(dialect));
  }
  
  void selectTable(ZDialect table) {
    if (table == null) {
      table = ZDialect.Z;
    }
    
    selectAction.setCurrentTable(table);
    viewer.setInput(ZDialectSupport.INSTANCE.getCharacterTable(table));
    
    setContentDescription(table.getLabel() + " character table");
  }
  
  private void createTable(Composite parent)
  {

    viewer = new TableViewer(parent, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION);
    final Table table = viewer.getTable();
    
    table.setHeaderVisible(false);
    table.setLinesVisible(true);
    
    final TableViewerFocusCellManager cellFocus = initSingleCellFocus(viewer);
    
    table.addSelectionListener(new SelectionAdapter()
    {
      @Override
      public void widgetDefaultSelected(SelectionEvent e)
      {
        ViewerCell cell = cellFocus.getFocusCell();
        if (cell != null) {
          ZChar zch = getZCharAtCell(cell);
          if (zch != null) {
            insertZChar(zch);
          }
        }
      }
    });

    table.addMouseListener(new MouseAdapter()
    {
      private ZChar fDownChar = null;
      private ZChar fUpChar = null;
      private boolean mousedown = false;

      @Override
      public void mouseDown(MouseEvent event)
      {
        mousedown = true;
        Point p = new Point(event.x, event.y);
        fDownChar = getZCharAtPoint(table, p);
      }

      @Override
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
    });
    
    // enable tooltips
    toolTipSupport = StyledToolTipSupport.enableToolTipFor(viewer, ToolTip.NO_RECREATE);
    
    // init table font update
    initEditorFont();
    
    table.setRedraw(false);
    
    // get the longest column count of all tables
    int maxColumnCount = 0;
    for (ZCharTable charTable : ZDialectSupport.INSTANCE.getCharacterTables()) {
      maxColumnCount = max(maxColumnCount, charTable.getColumnCount());
    }

    // add name column
    addColumn(100, 0, SWT.LEFT).setLabelProvider(new ColumnLabelProvider2() {
      @Override
      public String getText(Object element) {
        Object[] zChars = (Object[]) element;
        return (String) zChars[0];
      }
    });
    
    // add the remaining columns
    for (int i = 1; i < maxColumnCount; i++) {
      addColumn(50, i, SWT.CENTER).setLabelProvider(new ZCharLabelProvider(i));
    }
    
    table.pack(true);
    table.setRedraw(true);
    
    viewer.setContentProvider(new ZCharTableContentProvider());
  }
  
  private void initEditorFont() {
    
    // set row height to font's height (needed when fonts increase)
    viewer.getTable().addListener(SWT.MeasureItem, new Listener() { 
      public void handleEvent(Event event) { 
        int height = event.gc.getFontMetrics().getHeight();
        event.height = height;
      } 
    });
    
    final IPropertyChangeListener fontChangeListener = new IPropertyChangeListener()
    {
      @Override
      public void propertyChange(PropertyChangeEvent event)
      {
        if (event.getProperty().equals(EDITOR_FONT)) {
          editorFont = JFaceResources.getFont(EDITOR_FONT);
          viewer.refresh();
        }
      }
    };
    
    viewer.getTable().addDisposeListener(new DisposeListener()
    {
      @Override
      public void widgetDisposed(DisposeEvent e)
      {
        JFaceResources.getFontRegistry().removeListener(fontChangeListener);
      }
    });
    
    JFaceResources.getFontRegistry().addListener(fontChangeListener);
  }

  private TableViewerFocusCellManager initSingleCellFocus(TableViewer viewer)
  {
    final TableViewerFocusCellManager cellFocus = new TableViewerFocusCellManager(viewer,
        new FocusCellOwnerDrawHighlighter(viewer));

    ColumnViewerEditorActivationStrategy actSupport = new ColumnViewerEditorActivationStrategy(viewer)
    {
      @Override
      protected boolean isEditorActivationEvent(ColumnViewerEditorActivationEvent event)
      {
        return false;
      }
    };

    TableViewerEditor.create(viewer, cellFocus, actSupport, 
        ColumnViewerEditor.TABBING_HORIZONTAL | ColumnViewerEditor.TABBING_MOVE_TO_ROW_NEIGHBOR 
        | ColumnViewerEditor.TABBING_VERTICAL | ColumnViewerEditor.KEYBOARD_ACTIVATION);
    
    return cellFocus;
  }
  
  private ZChar getZCharAtPoint(final Table table, Point pt)
  {
    ViewerCell cell = viewer.getCell(pt);
    if (cell != null) {
      return getZCharAtCell(cell);
    }
    
    return null;
  }

  private ZChar getZCharAtCell(ViewerCell cell)
  {
    int column = cell.getColumnIndex();
    Object[] row = (Object[]) cell.getElement();
    if (column < row.length) {
      Object cellValue = row[column];
      if (cellValue instanceof ZChar) {
        return (ZChar) cellValue;
      }
    }
    
    return null;
  }
  
  private void insertZChar(ZChar zch)
  {
    IEditorPart editor = getSite().getPage().getActiveEditor();
    if (!(editor instanceof ITextEditor)) {
      return;
    }
    
    ITextEditor textEditor = (ITextEditor) editor;
    IDocument doc = ZEditorUtil.getDocument(textEditor);
    ITextSelection selection = (ITextSelection) textEditor.getSelectionProvider().getSelection();
    
    Markup markup = null;
    if (textEditor instanceof ZEditor) {
      markup = ((ZEditor) textEditor).getMarkup();
    }

    String stringInput;
    if (markup == Markup.LATEX) {
      stringInput = zch.getLatex();
    } else if (markup == Markup.UNICODE) {
      stringInput = zch.getUnicode();
    } else {
      stringInput = zch.getDescription();
    }
      
    try {
      doc.replace(selection.getOffset(), selection.getLength(), stringInput);
      getSite().getPage().activate(textEditor);
      textEditor.selectAndReveal(selection.getOffset() + stringInput.length(), 0);
    } catch (BadLocationException e) {
      CztUIPlugin.log(e);
    }
  }
  
  @Override
  public void setFocus()
  {
    viewer.getControl().setFocus();
  }

  public TableViewerColumn addColumn(int width, final int colNumber, int style)
  {

    TableViewerColumn viewerColumn = new TableViewerColumn(viewer, style);
    TableColumn column = viewerColumn.getColumn();
    column.setText("");
//    column.setToolTipText(null);
    column.setWidth(width);
//    column.setResizable(true);
//    column.setMoveable(true);
    return viewerColumn;
  }


  private static class ColumnLabelProvider2 extends ColumnLabelProvider
  {

    @Override
    public String getToolTipText(Object element)
    {
      String text = getText(element);

      if (text == null || text.isEmpty()) {
        return null;
      }

      return text;
    }
  }
  
  private class ZCharLabelProvider extends ColumnLabelProvider2 {
    
    private final int column;
    
    public ZCharLabelProvider(int column)
    {
      this.column = column;
    }

    @Override
    public String getText(Object element) {
      ZChar zCh = getZChar(element);
      if (zCh != null) {
        return zCh.getLabel();
      }
      
      return "";
    }

    @Override
    public String getToolTipText(Object element)
    {
      ZChar zCh = getZChar(element);
      if (zCh != null) {
        return getZCharToolTip(zCh);
      }
      
      return super.getToolTipText(element);
    }
    
    private ZChar getZChar(Object element) {
      Object[] zChars = (Object[]) element;
      if (column < zChars.length) {
        ZChar zCh = (ZChar) zChars[column];
        if (zCh != null) {
          return zCh;
        }
      }
      return null;
    }
    
    private String getZCharToolTip(ZChar zch)
    {
      
      toolTipSupport.clearDecor();
      StringBuilder tooltip = new StringBuilder();
      
      append(tooltip, zch.getDescription(), SWT.BOLD);
      tooltip.append("\n");
      append(tooltip, "Unicode: ", SWT.ITALIC);
      appendMulti(tooltip, zch.getUnicode());
      tooltip.append("\n");
      append(tooltip, "LaTeX: ", SWT.ITALIC);
      appendMulti(tooltip, zch.getLatex());
      
      String text = tooltip.toString();
      toolTipSupport.text = text;
      return text;
    }

    private void append(StringBuilder tooltip, String text, int fontStyle)
    {
      int offset = tooltip.length();
      int length = text.length();

      tooltip.append(text);
      toolTipSupport.ranges.put(new Position(offset, length), fontStyle);
    }
    
    private void appendMulti(StringBuilder tooltip, String text)
    {
      text = text.trim();
      if (text.contains("\n")) {
        // has newlines, so add a newline at the start
        text = "\n" + text;
      }
      tooltip.append(text);
    }

    @Override
    public Font getFont(Object element)
    {
      return getEditorFont();
    }
  }

  private static class ZCharTableContentProvider implements IStructuredContentProvider
  {
    @Override
    public void inputChanged(Viewer v, Object oldInput, Object newInput) {}

    @Override
    public void dispose() {}

    @Override
    public Object[] getElements(Object parent)
    {
      if (parent == null) {
        return new Object[0];
      }

      return ((ZCharTable) parent).getZCharTable();
    }
  }
  
  private static class StyledToolTipSupport extends ColumnViewerToolTipSupport
  {

    private String text;
    private Map<Position, Integer> ranges = new LinkedHashMap<Position, Integer>();
    
    public StyledToolTipSupport(ColumnViewer viewer, int style, boolean manualActivation)
    {
      super(viewer, style, manualActivation);
    }

    @Override
    protected Composite createToolTipContentArea(Event event, Composite parent)
    {
      Image image = getImage(event);
      Image bgImage = getBackgroundImage(event);
      String text = getText(event);
      Color fgColor = getForegroundColor(event);
      Color bgColor = getBackgroundColor(event);
      Font font = getFont(event);

      StyledText textArea = new StyledText(parent, getStyle(event));
      textArea.setMargins(4, 4, 4, 4);
      if (text != null) {
        textArea.setText(text);
      }

      if (fgColor != null) {
        textArea.setForeground(fgColor);
      }

      if (bgColor != null) {
        textArea.setBackground(bgColor);
      }

      if (bgImage != null) {
        textArea.setBackgroundImage(image);
      }

      if (font != null) {
        textArea.setFont(font);
      }

      if (this.text != null && text != null && this.text.equals(text)) {
        // same text - apply formatting
        for (Entry<Position, Integer> range : ranges.entrySet()) {
          textArea.setStyleRange(createRange(range.getKey(), range.getValue()));
        }
      }

      return textArea;
    }

    private StyleRange createRange(Position position, int fontStyle)
    {
      StyleRange styleRange = new StyleRange();
      styleRange.start = position.getOffset();
      styleRange.length = position.getLength();
      styleRange.fontStyle = fontStyle;
      return styleRange;
    }

    @Override
    public boolean isHideOnMouseDown()
    {
      return false;
    }

    public static final StyledToolTipSupport enableToolTipFor(ColumnViewer viewer, int style)
    {
      return new StyledToolTipSupport(viewer, style, false);
    }
    
    public void clearDecor() {
      this.text = null;
      this.ranges.clear();
    }
  }
}
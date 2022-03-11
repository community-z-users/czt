package net.sourceforge.czt.eclipse.ui.util;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;


public class FilteredTree2 extends FilteredTree {

	private final ColumnViewerComparator sorter;
	
	public FilteredTree2(Composite parent, int treeStyle, 
			ITreeContentProvider contentProvider,
			ILabelProvider filterLabelProvider,
			ColumnViewerComparator sorter) {
		
		super(parent, treeStyle, new PatternFilter(), true);
		this.sorter = sorter;
		
		treeViewer.setContentProvider(contentProvider);
		
		// add a main label provider - will be used by filter functionality,
		// because columns have their own filters
        treeViewer.setLabelProvider(filterLabelProvider);
        
        treeViewer.getTree().setHeaderVisible(true);
        
        treeViewer.setComparator(sorter);
        
        setFont(parent.getFont());
        filterText.setMessage("type filter text");
	}
	
	public TreeViewerColumn addColumn(String title, int width, final int colNumber, int style) {
		
		TreeViewerColumn viewerColumn = new TreeViewerColumn(treeViewer, style);
		TreeColumn column = viewerColumn.getColumn();
		column.setText(title);
		column.setToolTipText(title);
		column.setWidth(width);
		column.setResizable(true);
		column.setMoveable(true);
		column.addSelectionListener(getSelectionAdapter(column, colNumber));
		return viewerColumn;
	}
	
	private SelectionAdapter getSelectionAdapter(final TreeColumn column, final int index) {
		SelectionAdapter selectionAdapter = new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				sorter.setColumn(index);
				int dir = sorter.getDirection();
				treeViewer.getTree().setSortDirection(dir);
				treeViewer.getTree().setSortColumn(column);
				treeViewer.refresh();
			}
		};
		return selectionAdapter;
	}
	
	public static abstract class ColumnViewerComparator extends ViewerComparator {
    	
    	private int currentColumn = -1;
    	// ascending by default
    	private boolean descending = false;

    	public int getDirection() {
    		return descending ? SWT.DOWN : SWT.UP;
    	}

    	public void setColumn(int column) {
    		if (column == this.currentColumn) {
    			// Same column as last sort; toggle the direction
    			descending = !descending;
    		} else {
    			// New column; do an ascending sort
    			this.currentColumn = column;
    			descending = false;
    		}
    	}

    	@Override
    	public int compare(Viewer viewer, Object e1, Object e2) {
    		return compare(viewer, e1, e2, currentColumn, descending);
    	}
    	
    	protected abstract int compare(Viewer viewer, Object e1, Object e2, int column, boolean descending);
    	
    }

}

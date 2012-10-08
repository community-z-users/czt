package net.sourceforge.czt.eclipse.vcg.ui.views;

import java.util.List;

import net.sourceforge.czt.eclipse.ui.CztUI;
import net.sourceforge.czt.eclipse.ui.util.FilteredTree2;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;


class VCTree extends FilteredTree2
{
  
  private final ResourceManager resourceManager = new LocalResourceManager(JFaceResources.getResources(), this);

  public VCTree(Composite parent, int treeStyle)
  {
    super(parent, treeStyle, 
        new VCEntryContentProvider(), 
        new VCFilterLabelProvider(),
        new VCViewerComparator());

    // enable tooltips
    ColumnViewerToolTipSupport.enableFor(treeViewer);

    // First column is for the theorem name
    addColumn("Name", 180, 0, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        VCEntry entry = (VCEntry) element;
        return entry.getVCName();
      }

      @Override
      public Image getImage(Object element)
      {
        VCEntry entry = (VCEntry) element;
        return CztUI.getTermImage(resourceManager, entry.getVCPara());
      }
    });

    // Second column is for the theorem source paragraph number
    addColumn("Source Paragraph", 100, 3, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        VCEntry entry = (VCEntry) element;
        return String.valueOf(entry.getSourceParagraph());
      }
    });

    // Second column is for the theorem source paragraph number
    addColumn("In Specification", 60, 3, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        return getInSpecText((VCEntry) element);
      }
    });

  }

  private static String getInSpecText(VCEntry entry)
  {
    if (entry.isInSpecification()) {
      return "In Spec";
    }

    return "";
  }

  public void setInput(List<? extends VCEntry> vcs)
  {
    treeViewer.setInput(vcs.toArray());
  }


  private static class VCFilterLabelProvider extends LabelProvider
  {

    @Override
    public String getText(Object element)
    {

      VCEntry entry = (VCEntry) element;
      return entry.getVCName() + " " + entry.getSourceParagraph() + " " + getInSpecText(entry);
    }
  }


  private static class VCEntryContentProvider implements ITreeContentProvider
  {

    @Override
    public void dispose()
    {
    }

    @Override
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
    }

    @Override
    public Object[] getElements(Object inputElement)
    {
      if (inputElement instanceof Object[]) {
        return (Object[]) inputElement;
      }

      return new Object[0];
    }

    @Override
    public Object[] getChildren(Object parentElement)
    {
      return new Object[0];
    }

    @Override
    public Object getParent(Object element)
    {
      return null;
    }

    @Override
    public boolean hasChildren(Object element)
    {
      return false;
    }
  }


  private static class VCViewerComparator extends ColumnViewerComparator
  {

    @Override
    protected int compare(Viewer viewer, Object e1, Object e2, int column, boolean descending)
    {

      VCEntry t1 = (VCEntry) e1;
      VCEntry t2 = (VCEntry) e2;
      int rc = 0;
      switch (column) {
        case 0 :
          rc = t1.getVCName().compareToIgnoreCase(t2.getVCName());
          break;
        case 1 :
          rc = t1.getSourceParagraph().compareToIgnoreCase(t2.getSourceParagraph());
          break;
        case 2 :
          rc = Boolean.valueOf(t1.isInSpecification()).compareTo(
               Boolean.valueOf(t2.isInSpecification()));
          break;
        default :
          rc = 0;
      }
      // If descending order, flip the direction
      if (descending) {
        rc = -rc;
      }
      return rc;
    }

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

}

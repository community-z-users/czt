package net.sourceforge.czt.eclipse.zeves.ui.views;

import java.util.List;

import net.sourceforge.czt.eclipse.ui.util.FilteredTree2;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesImages;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ZEvesApi.ZEvesTheoremType;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
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

/**
 * @author Andrius Velykis
 */
class TheoremTree extends FilteredTree2
{
  
  private final ResourceManager resourceManager = 
      new LocalResourceManager(JFaceResources.getResources(), this);

  public TheoremTree(Composite parent, int treeStyle)
  {

    super(parent, treeStyle, 
        new TheoremEntryContentProvider(),
        new TheoremFilterLabelProvider(),
        new TheoremViewerComparator());

    // enable tooltips
    ColumnViewerToolTipSupport.enableFor(treeViewer);

    // First column is for the theorem name
    addColumn("Name", 250, 0, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        TheoremEntry entry = (TheoremEntry) element;
        return entry.getTheoremName();
      }

      @Override
      public Image getImage(Object element)
      {
        TheoremEntry entry = (TheoremEntry) element;

        switch (entry.getType()) {
          case AXIOM :
            return resourceManager.createImageWithDefault(ZEvesImages.THEOREM_AXIOM);
          case GOAL : {
            boolean proved = entry.isProved();
            if (proved) {
              return resourceManager.createImageWithDefault(ZEvesImages.THEOREM_PROVED);
            }
            else {
              return resourceManager.createImageWithDefault(ZEvesImages.THEOREM_UNPROVED);
            }
          }
        }

        return null;
      }
    });

    // Third column is for the theorem source paragraph number
    addColumn("Proved", 40, 1, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        TheoremEntry entry = (TheoremEntry) element;
        Boolean proved = entry.isProved();

        return proved != null ? proved.toString() : "";
      }
    });

    // Second column is for the theorem type
    addColumn("Type", 50, 2, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        TheoremEntry entry = (TheoremEntry) element;
        return renderType(entry.getType());
      }
    });

    // Third column is for the theorem source paragraph number
    addColumn("Source Paragraph", 40, 3, SWT.NONE).setLabelProvider(new ColumnLabelProvider2()
    {
      @Override
      public String getText(Object element)
      {
        TheoremEntry entry = (TheoremEntry) element;
        return String.valueOf(entry.getSourceParagraph());
      }
    });

  }

  private static String renderType(ZEvesTheoremType type)
  {
    switch (type) {
      case AXIOM :
        return "Axiom";
      case GOAL :
        return "Proof obligation";
    }

    return "";
  }

  public void setInput(List<? extends TheoremEntry> theorems)
  {
    treeViewer.setInput(theorems.toArray());
  }


  private static class TheoremFilterLabelProvider extends LabelProvider
  {

    @Override
    public String getText(Object element)
    {
      TheoremEntry entry = (TheoremEntry) element;
      return entry.getTheoremName() + " " + renderType(entry.getType()) + " " + entry.getSourceParagraph();
    }
  }


  private static class TheoremEntryContentProvider implements ITreeContentProvider
  {

    @Override
    public void dispose() {}

    @Override
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

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


  private static class TheoremViewerComparator extends ColumnViewerComparator
  {

    @Override
    protected int compare(Viewer viewer, Object e1, Object e2, int column, boolean descending)
    {

      TheoremEntry t1 = (TheoremEntry) e1;
      TheoremEntry t2 = (TheoremEntry) e2;
      int rc = 0;
      switch (column) {
        case 0 :
          rc = t1.getTheoremName().compareToIgnoreCase(t2.getTheoremName());
          break;
        case 1 : {
          rc = compareBooleans(t1.isProved(), t2.isProved());
          break;
        }
        case 2 :
          String tt1 = t1.getType() != null ? t1.getType().toString() : "";
          String tt2 = t2.getType() != null ? t2.getType().toString() : "";
          rc = tt1.compareTo(tt2);
          break;
        case 3 :
          rc = t1.getSourceParagraph() - t2.getSourceParagraph();
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

    private int compareBooleans(Boolean p1, Boolean p2)
    {
      if (p1 == p2) {
        return 0;
      }

      if (p1 == null) {
        return -1;
      }

      if (p2 == null) {
        return 1;
      }

      if (p1) {
        return 1;
      }
      else {
        return -1;
      }
    }

  }


  public static class TheoremEntry implements IZInfoObject
  {

    private final String theoremName;

    private final ZEvesTheoremType type;

    private final int sourceParagraph;

    private final Boolean proved;

    public TheoremEntry(String theoremName, ZEvesTheoremType type, int sourceParagraph,
        Boolean proved)
    {
      super();
      this.theoremName = theoremName;
      this.type = type;
      this.sourceParagraph = sourceParagraph;
      this.proved = proved;
    }

    public String getTheoremName()
    {
      return theoremName;
    }

    public ZEvesTheoremType getType()
    {
      return type;
    }

    public int getSourceParagraph()
    {
      return sourceParagraph;
    }

    public Boolean isProved()
    {
      return proved;
    }

    @Override
    public Markup getMarkup()
    {
      return Markup.UNICODE;
    }

    @Override
    public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException
    {

      ZEves zEves = ZEvesCore.getZEves();
      if (!zEves.isRunning()) {
        return null;
      }

      try {
        Object result = zEves.getApi().getTheorem(theoremName);
        if (result == null) {
          return "Theorem " + theoremName + " cannot be found in Z/EVES.";
        }
        return result.toString();
      }
      catch (ZEvesException e) {
        throw new CoreException(ZEvesUIPlugin.newErrorStatus(e.getMessage(), e));
      }
    }

    @Override
    public String loadDescription(IProgressMonitor monitor) throws CoreException
    {
      return "Theorem " + theoremName;
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

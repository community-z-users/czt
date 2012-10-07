
package net.sourceforge.czt.eclipse.ui.perspective;

import net.sourceforge.czt.eclipse.util.CztUI;

import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class ZPerspectiveFactory implements IPerspectiveFactory
{
  private static final String ID_RESOURCE_PERSPECTIVE = "org.eclipse.ui.resourcePerspective";

  private static final String ID_JAVA_PERSPECTIVE = "org.eclipse.jdt.ui.JavaPerspective";

  private static final String ID_JAVA_BROWSING_PERSPECTIVE = "org.eclipse.jdt.ui.JavaBrowsingPerspective";

  private static final String ID_JAVA_HIERARCHY_PERSPECTIVE = "org.eclipse.jdt.ui.JavaHierarchyPerspective";

  private static final String ID_CONSOLE_VIEW = IConsoleConstants.ID_CONSOLE_VIEW;

  private static final String ID_SEARCH_VIEW = NewSearchUI.SEARCH_VIEW_ID;

  private static final String ID_NEW_FOLDER_WIZARD = "org.eclipse.ui.wizards.new.folder";

  private static final String ID_NEW_FILE_WIZARD = "org.eclipse.ui.wizards.new.file";

  private static final String ID_NEW_UNTITLED_TEXTFILE_WIZARD = "org.eclipse.ui.editors.wizards.UntitledTextFileWizard";

  public ZPerspectiveFactory()
  {
    super();
  }

  public void createInitialLayout(IPageLayout layout)
  {
    // Get the fEditor area.
    String editorArea = layout.getEditorArea();

    // Put the navigate view on the left.
    layout.addView(IPageLayout.ID_RES_NAV, IPageLayout.LEFT, 0.25f, editorArea);

    /* Put the Z Character Map view on the bottom with the Conversion view,
     * Problems view, Tasks view, bookmarks view and the console view.
     */
    IFolderLayout bottom = layout.createFolder("bottom", IPageLayout.BOTTOM,
        0.75f, editorArea);
    bottom.addView(CztUI.ID_CHARMAP); //$NON-NLS-1$
    bottom.addView(CztUI.ID_CONVERSIONVIEW); //$NON-NLS-1$
    bottom.addView(IPageLayout.ID_PROBLEM_VIEW); //$NON-NLS-1$
    bottom.addPlaceholder(ID_CONSOLE_VIEW); //$NON-NLS-1$

    // Put the Outline view on the right.
    layout
        .addView(IPageLayout.ID_OUTLINE, IPageLayout.RIGHT, 0.75f, editorArea);

    // Add shortcuts for self and other perspectives
    layout.addPerspectiveShortcut(CztUI.ID_PERSPECTIVE); //$NON-NLS-1$
    layout.addPerspectiveShortcut(ID_RESOURCE_PERSPECTIVE); //$NON-NLS-1$
    layout.addPerspectiveShortcut(ID_JAVA_PERSPECTIVE); //$NON-NLS-1$
    layout.addPerspectiveShortcut(ID_JAVA_BROWSING_PERSPECTIVE); //$NON-NLS-1$
    layout.addPerspectiveShortcut(ID_JAVA_HIERARCHY_PERSPECTIVE); //$NON-NLS-1$

    // Add shortcuts for the character view and other views
    layout.addShowViewShortcut(IPageLayout.ID_BOOKMARKS); //$NON-NLS-1$
    layout.addShowViewShortcut(IPageLayout.ID_OUTLINE); //$NON-NLS-1$
    layout.addShowViewShortcut(IPageLayout.ID_PROBLEM_VIEW); //$NON-NLS-1$
    layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET); //$NON-NLS-1$
    layout.addShowViewShortcut(IPageLayout.ID_RES_NAV); //$NON-NLS-1$
    layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST); //$NON-NLS-1$
    layout.addShowViewShortcut(ID_CONSOLE_VIEW); //$NON-NLS-1$
    layout.addShowViewShortcut(ID_SEARCH_VIEW); //$NON-NLS-1$
    layout.addShowViewShortcut(CztUI.ID_CHARMAP); //$NON-NLS-1$

    // Add action sets
    layout.addActionSet(IPageLayout.ID_NAVIGATE_ACTION_SET); //$NON-NLS-1$

    // Add shortcuts for new wizards
    layout.addNewWizardShortcut(CztUI.ID_NEW_CZT_PROJECT_WIZARD);
    layout.addNewWizardShortcut(CztUI.ID_NEW_CZT_SPECIFICATION_WIZARD);
    layout.addNewWizardShortcut(ID_NEW_FOLDER_WIZARD); //$NON-NLS-1$
    layout.addNewWizardShortcut(ID_NEW_FILE_WIZARD); //$NON-NLS-1$
    layout.addNewWizardShortcut(ID_NEW_UNTITLED_TEXTFILE_WIZARD); //$NON-NLS-1$
  }
}

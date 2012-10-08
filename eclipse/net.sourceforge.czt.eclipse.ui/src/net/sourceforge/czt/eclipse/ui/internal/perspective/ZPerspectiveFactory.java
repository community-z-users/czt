
package net.sourceforge.czt.eclipse.ui.internal.perspective;

import net.sourceforge.czt.eclipse.ui.CztUI;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;


/**
 * Defines layout of Z perspective.
 * 
 * @author Andrius Velykis
 */
public class ZPerspectiveFactory implements IPerspectiveFactory
{

  private static final String ID_NAVIGATOR_FOLDER = CztUIPlugin.PLUGIN_ID + ".navigatorFolder";

  private static final String ID_OUTPUT_FOLDER = CztUIPlugin.PLUGIN_ID + ".outputFolder";

  private static final String ID_OUTLINE_FOLDER = CztUIPlugin.PLUGIN_ID + ".outlineFolder";
  

  public void createInitialLayout(IPageLayout layout)
  {

    String editorArea = layout.getEditorArea();

    // put project explorer on the left
    IFolderLayout navFolder = layout.createFolder(ID_NAVIGATOR_FOLDER, IPageLayout.LEFT, 0.25f, editorArea);
    navFolder.addView(IPageLayout.ID_PROJECT_EXPLORER);
    navFolder.addPlaceholder("org.eclipse.ui.views.ResourceNavigator"); //$NON-NLS-1$

    // put the Z Character Map view on the bottom with the Conversion view and various IDE views
    IFolderLayout outputFolder = layout.createFolder(ID_OUTPUT_FOLDER, IPageLayout.BOTTOM, 0.75f, editorArea);
    outputFolder.addView(CztUI.CHARMAP_VIEW_ID);
    outputFolder.addPlaceholder(CztUI.CONVERSION_VIEW_ID);
    outputFolder.addView(IPageLayout.ID_PROBLEM_VIEW);
    outputFolder.addPlaceholder(NewSearchUI.SEARCH_VIEW_ID);
    outputFolder.addPlaceholder(IConsoleConstants.ID_CONSOLE_VIEW);
    outputFolder.addPlaceholder(IPageLayout.ID_BOOKMARKS);

    // put outline on the right
    IFolderLayout outlineFolder = layout.createFolder(ID_OUTLINE_FOLDER, IPageLayout.RIGHT, 0.75f, editorArea);
    outlineFolder.addView(IPageLayout.ID_OUTLINE);

    // Add action sets
    layout.addActionSet(IPageLayout.ID_NAVIGATE_ACTION_SET);

    // views - CZT
    layout.addShowViewShortcut(CztUI.CHARMAP_VIEW_ID);
    layout.addShowViewShortcut(CztUI.CONVERSION_VIEW_ID);

    // views - search
    layout.addShowViewShortcut(NewSearchUI.SEARCH_VIEW_ID);

    // views - debugging
    layout.addShowViewShortcut(IConsoleConstants.ID_CONSOLE_VIEW);

    // views - standard workbench
    layout.addShowViewShortcut(IPageLayout.ID_BOOKMARKS);
    layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
    layout.addShowViewShortcut(IPageLayout.ID_PROBLEM_VIEW);
    layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);
    layout.addShowViewShortcut(IPageLayout.ID_PROJECT_EXPLORER);
    layout.addShowViewShortcut("org.eclipse.pde.runtime.LogView"); //$NON-NLS-1$

    // new actions - Java project creation wizard
    layout.addNewWizardShortcut(CztUI.CZT_PROJECT_WIZARD_ID);
    layout.addNewWizardShortcut(CztUI.Z_SPEC_WIZARD_ID);
    layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.folder");//$NON-NLS-1$
    layout.addNewWizardShortcut("org.eclipse.ui.wizards.new.file");//$NON-NLS-1$
    layout.addNewWizardShortcut("org.eclipse.ui.editors.wizards.UntitledTextFileWizard");//$NON-NLS-1$

  }
}

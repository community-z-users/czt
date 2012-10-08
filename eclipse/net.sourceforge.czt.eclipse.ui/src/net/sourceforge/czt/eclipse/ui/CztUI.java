package net.sourceforge.czt.eclipse.ui;

import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.swt.graphics.Image;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.internal.outline.NodeIconVisitor;
import net.sourceforge.czt.eclipse.ui.internal.outline.TermLabelVisitorFactory;

/**
 * CZT UI component references.
 * 
 * @author Andrius Velykis
 * @author Chengdong Xu
 */
public final class CztUI
{

  private CztUI() {}

  /**
   * The id of the Character Map view
   * (value {@code net.sourceforge.czt.eclipse.ui.views.ZCharMap}).
   */
  public static final String CHARMAP_VIEW_ID = "net.sourceforge.czt.eclipse.ui.views.ZCharMap";

  /**
   * The id of the Z conversion page view
   * (value {@code net.sourceforge.czt.eclipse.ui.views.ZConversion}).
   */
  public static final String CONVERSION_VIEW_ID = "net.sourceforge.czt.eclipse.ui.views.ZConversion";

  /**
   * The id of the new CZT project wizard
   * (value {@code net.sourceforge.czt.eclipse.ui.wizards.CztProject}).
   */
  public static final String CZT_PROJECT_WIZARD_ID = "net.sourceforge.czt.eclipse.ui.wizards.CztProject";

  /**
   * The id of the new Z specification wizard
   * (value {@code net.sourceforge.czt.eclipse.ui.wizards.ZSpecification}).
   */
  public static final String Z_SPEC_WIZARD_ID = "net.sourceforge.czt.eclipse.ui.wizards.ZSpecification";
  
  
  public static String getTermLabel(Term term) {
    
    if (term == null) {
      return null;
    }
    
    return term.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
  }
  
  public static Image getTermImage(ResourceManager resourceManager, Term term) {
    
    if (term == null || resourceManager == null) {
      return null;
    }
    
    return term.accept(new NodeIconVisitor(resourceManager));
  }

}

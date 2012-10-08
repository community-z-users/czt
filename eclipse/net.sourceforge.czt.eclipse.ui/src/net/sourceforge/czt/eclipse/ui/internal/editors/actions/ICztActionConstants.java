package net.sourceforge.czt.eclipse.ui.internal.editors.actions;

/**
 * Action ids for standard actions, for groups in the menu bar, and
 * for actions in context menus of CZT fEditor and views.
 * 
 * <p>
 * This class may be instantiated; it is not intended to be subclassed.
 * </p>
 */
public interface ICztActionConstants
{
    //Edit menu
  
    /**
     * Edit menu: name of standard Goto Declaration action
     * (value {@code net.sourceforge.czt.eclipse.ui.editor.goToDeclaration}).
     */
    public static final String GO_TO_DECLARATION = "net.sourceforge.czt.eclipse.ui.editor.goToDeclaration"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard Highlight Enclosing action
     * (value {@code net.sourceforge.czt.eclipse.ui.editor.expandSelection}).
     */
    public static final String HIGHLIGHT_ENCLOSING_ELEMENT = "net.sourceforge.czt.eclipse.ui.editor.expandSelection"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard Highlight Last action
     * (value {@code net.sourceforge.czt.eclipse.ui.editor.contractSelection}).
     */
    public static final String RESTORE_LAST_HIGHLIGHT = "net.sourceforge.czt.eclipse.ui.editor.contractSelection"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard ConvertTo LaTeX action
     * (value {@code net.sourceforge.czt.eclipse.ui.convert.latex}).
     */
    public static final String CONVERT_TO_LATEX = "net.sourceforge.czt.eclipse.ui.convert.latex"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard ConvertTo Old LaTeX action
     * (value {@code net.sourceforge.czt.eclipse.ui.convert.oldlatex}).
     */
    public static final String CONVERT_TO_OLD_LATEX = "net.sourceforge.czt.eclipse.ui.convert.oldlatex"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard ConvertTo Unicode action
     * (value {@code net.sourceforge.czt.eclipse.ui.convert.unicode}).
     */
    public static final String CONVERT_TO_UNICODE = "net.sourceforge.czt.eclipse.ui.convert.unicode"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard ConvertTo XML action
     * (value {@code net.sourceforge.czt.eclipse.ui.convert.xml}).
     */
    public static final String CONVERT_TO_XML = "net.sourceforge.czt.eclipse.ui.convert.xml"; //$NON-NLS-1$
    
    /**
     * Edit menu: name of standard Goto Matching Bracket action
     * (value {@code net.sourceforge.czt.eclipse.ui.editor.goToMatchingBracket}).
     */
    public static final String GOTO_MATCHING_BRACKET= "net.sourceforge.czt.eclipse.ui.editor.goToMatchingBracket"; //$NON-NLS-1$

}

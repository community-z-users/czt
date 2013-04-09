package net.sourceforge.czt.eclipse.ui.internal.editors.hover;

import java.math.BigInteger;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfo;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.NameInfoResolver;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.preferences.ZEditorConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.Selector;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.ZName;
import org.eclipse.jface.text.DefaultTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * The ZTextHover provides the text hover support for Z editors. It is used 
 * for showing popup on annotations appearing in the edito text.
 * <p>
 * The hover extends default one, and displays messages for all annotations. 
 * It excludes annotations specified in 
 * {@link ZTextHover#isIncludedZ(Annotation)}, such as projection annotations.
 * </p>
 * <p>
 * If the text hover does not provide information no hover
 * popup is shown.</p>
 * <p>
 * The order of things displayed in hover is the following:
 * <ul>
 *   <li>If Z term under the hover is highlighted, it displays the highlighting
 *       information.</li>
 *   <li>Otherwise, available annotation messages are displayed.</li>
 *   <li>If no annotation/marker messages are available, Z term type is 
 *       displayed in the popup.</li>
 * </ul></p>
 * 
 * @see org.eclipse.jface.text.ITextHover
 * @see org.eclipse.jface.text.DefaultTextHover
 * 
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZTextHover extends DefaultTextHover
{

  private ITextEditor fTextEditor;

  private Visitor<String> termHighlightInfoVisitor;

  public ZTextHover(ISourceViewer sourceViewer, ITextEditor editor)
  {
    super(sourceViewer);
    this.fTextEditor = editor;
    termHighlightInfoVisitor = new TermHighlightInfoVisitor(fTextEditor);
  }

  private ITextEditor getEditor()
  {
    return this.fTextEditor;
  }

  /**
   * @see org.eclipse.jface.text.ITextHover#getHoverInfo(org.eclipse.jface.text.ITextViewer,
   *      org.eclipse.jface.text.IRegion)
   */
  @Override
  public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion)
  {
    if (hoverRegion == null) {
      return null;
    }

    // See term highlight info first
    String termHighlight = getTermHighlightInfo(hoverRegion.getOffset());
    if (termHighlight != null) {
      return termHighlight;
    }

    // ask parent to render other annotations
    // TODO: HANDLE deprecated!
    @SuppressWarnings("deprecation")
	String annInfo = super.getHoverInfo(textViewer, hoverRegion);
    if (annInfo != null) {
      return annInfo;
    }

    // Display the type of a name
    String info = getInfoOfTerm(getTermOfRegion(hoverRegion));
    if (info != null) {
      return info;
    }

    return null;
  }

  /**
   * @see org.eclipse.jface.text.ITextHover#getHoverRegion(org.eclipse.jface.text.ITextViewer,
   *      int)
   */
  @Override
  public IRegion getHoverRegion(ITextViewer textViewer, int offset)
  {
    if (!CztUIPlugin.getDefault().getPreferenceStore()
        .getBoolean(ZEditorConstants.SHOW_HOVER)) {
      return null;
    }

    return new Region(offset, 1);
  }

  private String getTermHighlightInfo(int offset)
  {
    if (getEditor() instanceof ZEditor) {
      ZEditor editor = (ZEditor) getEditor();
      if (editor.getTermHighlightAnnotation() == null)
        return null;

      Selector selector = ((ZEditor) getEditor()).getTermHighlightSelector();
      if (selector == null)
        return null;

      Term term = selector.current();
      if (term == null)
        return null;

      LocAnn locAnn = term.getAnn(LocAnn.class);
      if (locAnn != null) {
        BigInteger start = locAnn.getStart();
        BigInteger length = locAnn.getLength();
        if ((start != null) && (length != null)) {
          if ((start.intValue() <= offset) && (start.intValue() + length.intValue() >= offset)) {
            return term.accept(termHighlightInfoVisitor);
          }
        }
      }
    }

    return null;
  }

  private String getInfoOfTerm(Term term)
  {
    if (term == null)
      return null;

    if (term instanceof ZName) {
      Map<ZName, NameInfo> nameInfoMap = ((ZEditor) getEditor()).getParsedData().getNameInfoMap();
      NameInfo info = NameInfoResolver.findInfo(nameInfoMap, (ZName) term);
      if (info != null) {
        return info.getType();
      }

//      return ((ZName)term).getId() + info.getType();
      return ((ZName) term).getId();
    }

//    TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);
//    if (typeAnn != null) {
//      if (typeAnn.getType() != null) {
//        return typeAnn.getType().accept(new PrintVisitor());
//      }
//    }

    return null;
  }

  private Term getTermOfRegion(IRegion region)
  {
    if (getEditor() instanceof ZEditor) {
      Selector selector = ((ZEditor) getEditor()).getParsedData().createTermSelector();
      if (selector != null) {
        int offset = region.getOffset();
        int length = region.getLength();
        Position pos = new Position(offset, length);
        Term term = selector.getTerm(pos);
        return term;
      }
    }
    return null;
  }

  @Override
  protected boolean isIncluded(Annotation annotation)
  {
    return isIncludedZ(annotation);
  }

  public static boolean isIncludedZ(Annotation annotation)
  {
    String type = annotation.getType();
    if ("org.eclipse.projection".equals(type)) {
      return false;
    }

    return true;
  }
}

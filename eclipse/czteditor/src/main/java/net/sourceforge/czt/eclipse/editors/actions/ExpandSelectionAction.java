
package net.sourceforge.czt.eclipse.editors.actions;

import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.IZAnnotationType;
import net.sourceforge.czt.eclipse.util.Selector;

import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

public class ExpandSelectionAction extends TextEditorAction
{

  public ExpandSelectionAction(ResourceBundle bundle, String prefix,
      ITextEditor editor)
  {
    super(bundle, prefix, editor);
  }

  public ExpandSelectionAction(ResourceBundle bundle, String prefix,
      ITextEditor editor, int style)
  {
    super(bundle, prefix, editor, style);
  }

  public void run()
  {
    if (!(getTextEditor() instanceof ZEditor))
      return;

    ZEditor editor = (ZEditor) getTextEditor();
    if (editor.getTermSelector() == null)
      editor.setTermSelector(new Selector(editor.getParsedData().getSpec()));

    Selector selector = editor.getTermSelector();
    Term selectedTerm = selector.current();
    if (selectedTerm == null) {
      ITextSelection selection = (ITextSelection) editor.getSelectionProvider()
          .getSelection();
      selectedTerm = selector.getTerm(new Position(selection.getOffset(),
          selection.getLength()));
    }
    else
      selectedTerm = selector.next();

    if (selectedTerm == null) {
      return;
    }

    Position decl_pos = editor.getParsedData().getTermPosition(selectedTerm);
    if (decl_pos != null) {
      IAnnotationModel annotationModel = editor.getDocumentProvider()
          .getAnnotationModel(editor.getEditorInput());
      if (annotationModel == null)
        return;

      Annotation annotation = new Annotation(IZAnnotationType.TERMHIGHLIGHT,
          false, String.valueOf(selectedTerm));

      synchronized (editor.getAnnotationLock(annotationModel)) {
        if (annotationModel instanceof IAnnotationModelExtension) {
          Map<Annotation, Position> map = new HashMap<Annotation, Position>();
          map.put(annotation, decl_pos);
          ((IAnnotationModelExtension) annotationModel).replaceAnnotations(
              new Annotation[]{editor.getTermHighlightAnnotation()}, map);
        }
        else {
          editor.removeTermHighlightAnnotation();
          annotationModel.addAnnotation(annotation, decl_pos);
        }
        editor.setTermHighlightAnnotation(annotation);
      }
    }
  }
}

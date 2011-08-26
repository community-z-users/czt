package net.sourceforge.czt.eclipse.editors.zeditor;

import net.sourceforge.czt.eclipse.editors.IZReconcilingListener;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.preferences.ZEditorConstants;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.session.Markup;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;


public class ZEditorUtil {

  public static int getCaretPosition(ZEditor editor)
  {
    return editor.getViewer().getTextWidget().getCaretOffset();
  }

  public static boolean setCaretPosition(ZEditor editor, int position)
  {
    try {
      editor.getViewer().getTextWidget().setCaretOffset(position);
      editor.getViewer().getTextWidget().setSelection(position);
    }
    catch (IllegalArgumentException ex) {
      // invalid, but ignore?
      return false;
    }

    return true;
  }

  public static IResource getEditorResource(IEditorPart editor)
  {

    if (editor == null) {
      return null;
    }

    return (IResource) ((IAdaptable) editor.getEditorInput()).getAdapter(IResource.class);
  }

  public static IDocument getDocument(ITextEditor editor)
  {

    if (editor == null || editor.getDocumentProvider() == null) {
      return null;
    }

    return editor.getDocumentProvider().getDocument(editor.getEditorInput());
  }
  
  public static boolean hasErrors(ParsedData parsedData) {
    
    if (parsedData == null) {
      return true;
    }
    
    for (CztError err : parsedData.getErrors()) {
      if (err.getErrorType() == ErrorType.ERROR) {
        return true;
      }
    }
    
    return false;
  }
  
  public static String getEditorFont(Markup markup) {
    if (Markup.UNICODE == markup) {
      return ZEditorConstants.FONT_UNICODE;
    }
    else if (Markup.LATEX == markup) {
      return ZEditorConstants.FONT_LATEX;
    }
    
    return JFaceResources.TEXT_FONT;
  }

  public static void runOnReconcile(final ZEditor editor, final ReconcileRunnable callback)
  {
    callback.setEditor(editor);
    editor.addReconcileListener(callback);
  }

  public static abstract class ReconcileRunnable implements IZReconcilingListener
  {

    private ZEditor editor;

    public void setEditor(ZEditor editor)
    {
      this.editor = editor;
    }

    @Override
    public void reconciled(ParsedData parsedData, boolean forced, IProgressMonitor progressMonitor)
    {
      // remove itself from listeners - this was one-shot event
      editor.removeReconcileListener(this);
      run(parsedData);
    }

    @Override
    public void aboutToBeReconciled()
    {
    }

    protected abstract void run(ParsedData parsedData);
  }

}

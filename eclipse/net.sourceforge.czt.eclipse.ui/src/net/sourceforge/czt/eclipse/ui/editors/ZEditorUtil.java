package net.sourceforge.czt.eclipse.ui.editors;

import java.math.BigInteger;

import net.sourceforge.czt.eclipse.core.compile.IZCompileData;
import net.sourceforge.czt.eclipse.ui.internal.editors.IZReconcilingListener;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.preferences.ZEditorConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.session.Markup;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;


public class ZEditorUtil {

  public static int getCaretPosition(IZEditor editor)
  {
    return editor.getViewer().getTextWidget().getCaretOffset();
  }

  public static boolean setCaretPosition(IZEditor editor, int position)
  {
    try {
      StyledText text = editor.getViewer().getTextWidget(); 
      text.setCaretOffset(position);
      text.setSelection(position);
      text.showSelection();
      editor.getViewer().setSelectedRange(position, 0);
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
    
    IEditorInput input = editor.getEditorInput();
    if (input instanceof IAdaptable) {
      return (IResource) input.getAdapter(IResource.class); 
    }

    return null;
  }

  public static IDocument getDocument(ITextEditor editor)
  {

    if (editor == null || editor.getDocumentProvider() == null) {
      return null;
    }

    return editor.getDocumentProvider().getDocument(editor.getEditorInput());
  }
  
  public static boolean hasErrors(IZCompileData parsedData) {
    
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
  
  public static String getFileType(Markup markup) {
    if (markup != null) {
      switch (markup) {
        case LATEX: return IZFileType.FILETYPE_LATEX;
        case UNICODE: return IZFileType.FILETYPE_UTF8;
        default: return null;
      }
    }
    
    return null;
  }
  
  public static void runOnReconcile(final IZEditor editor, final ReconcileRunnable callback)
  {
    runOnReconcile(editor, editor.getDocumentVersion(), callback);
  }
  
  public static void runOnReconcile(final IZEditor editor, BigInteger minDocumentVersion, 
      final ReconcileRunnable callback)
  {
    // TODO better synchronization?
    // TODO investigate the typecast
    ZEditor zeditor = (ZEditor) editor;
    callback.editor = zeditor;
    callback.minDocumentVersion = minDocumentVersion;
    zeditor.addReconcileListener(callback);
    
    // check maybe this version is already correct
    ParsedData parsedData = zeditor.getParsedData();
    if (parsedData.getDocumentVersion().compareTo(minDocumentVersion) >= 0) {
      zeditor.removeReconcileListener(callback);
      callback.run(parsedData);
    }
  }

  public static abstract class ReconcileRunnable implements IZReconcilingListener
  {

    private ZEditor editor;
    private BigInteger minDocumentVersion;

    @Override
    public void reconciled(ParsedData parsedData, boolean forced, IProgressMonitor progressMonitor)
    {
      if (parsedData.getDocumentVersion().compareTo(minDocumentVersion) >= 0) {
        // remove itself from listeners - this was one-shot event
        editor.removeReconcileListener(this);
        run(parsedData);
      }
    }

    @Override
    public void aboutToBeReconciled() {}

    protected abstract void run(IZCompileData parsedData);
  }

}

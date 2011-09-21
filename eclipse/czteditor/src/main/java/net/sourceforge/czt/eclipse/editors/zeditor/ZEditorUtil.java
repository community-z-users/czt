package net.sourceforge.czt.eclipse.editors.zeditor;

import java.math.BigInteger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.IZReconcilingListener;
import net.sourceforge.czt.eclipse.editors.ZDialectSupport;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.preferences.ZEditorConstants;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.custom.StyledText;
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
  
  public static String getFileType(Markup markup) {
    if (markup != null) {
      switch (markup) {
        case LATEX: return IZFileType.FILETYPE_LATEX;
        case UNICODE: return IZFileType.FILETYPE_UTF8;
      }
    }
    
    return null;
  }
  
  public static String print(Term term, SectionManager sectInfo, String sectName, Markup markup,
      int textWidth, boolean display) throws CommandException
  {

    SectionManager sectMan = sectInfo.clone();

    // TODO externalise preferences?
    sectMan.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, String.valueOf(textWidth));
    sectMan.setProperty(PrintPropertiesKeys.PROP_PRINTING_ONTHEFLY_SECTION_NAME, sectName);

    if ("zeves".equals(ZDialectSupport.INSTANCE.getCurrentDialect())) {
      sectMan.setProperty(PrintPropertiesKeys.PROP_PRINT_ZEVES, String.valueOf(true));
    }
    
    // set pretty-printing for structured goals
    sectMan.setProperty(PrintPropertiesKeys.PROP_PRINTING_STRUCTURED_GOAL, String.valueOf(true));
    
    String keyId = "zeditor-utils-print";
    sectMan.put(new Key<Term>(keyId, Term.class), term);
    CztPrintString out = sectMan.get(getPrintKey(keyId, markup));

    return tidyPrinted(out.toString(), markup, display);
  }
  
  private static Key<? extends CztPrintString> getPrintKey(String keyId, Markup markup)
  {
    switch (markup) {
      case UNICODE :
        return new Key<UnicodeString>(keyId, UnicodeString.class);
      case ZML :
        return new Key<XmlString>(keyId, XmlString.class);
        // use LaTeX by default
      case LATEX :
      default :
        return new Key<LatexString>(keyId, LatexString.class);
    }
  }
  
  public static String tidyPrinted(String result, Markup markup, boolean display)
  {
    result = result.replace("[ ", "[").replace(" ]", "]")//.replace(" [", "[")
                   .replace(" ,", ",").replace(" ;", ";")
                   .replace("( ", "(").replace(" )", ")")
                   .replace("{ ", "{").replace(" }", "}")
                   .replace(" : ", ": ");

    if (markup == Markup.LATEX) {
      result = result.replace("\\_ \\_ ", "\\_\\_");

      if (display) {
        // clear \t0 .. \t9 symbols
        for (int index = 0; index <= 9; index++) {
          result = result.replace("\\t" + index, "");
        }
      }
    }

    return result;
  }

  public static void runOnReconcile(final ZEditor editor, final ReconcileRunnable callback)
  {
    runOnReconcile(editor, editor.getDocumentVersion(), callback);
  }
  
  public static void runOnReconcile(final ZEditor editor, BigInteger minDocumentVersion, 
      final ReconcileRunnable callback)
  {
    // TODO better synchronization?
    callback.editor = editor;
    callback.minDocumentVersion = minDocumentVersion;
    editor.addReconcileListener(callback);
    
    // check maybe this version is already correct
    ParsedData parsedData = editor.getParsedData();
    if (parsedData.getDocumentVersion().compareTo(minDocumentVersion) >= 0) {
      editor.removeReconcileListener(callback);
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

    protected abstract void run(ParsedData parsedData);
  }

}

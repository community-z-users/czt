
package net.sourceforge.czt.eclipse.editors.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.util.IZMarker;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IFileEditorInput;

/**
 * @author Chengdong Xu
 */
public class ZCompiler
{
  private static ZCompiler fInstance;

  private ZEditor fEditor = null;

  private final String DEFAULT_SECTION_NAME = "NEWSECTION";

  private String sectionName_ = DEFAULT_SECTION_NAME;

  private ParsedData fParsedData = null;

  /**
   * Constructor
   */
  private ZCompiler()
  {
    fInstance = this;
  }

  public static ZCompiler getInstance()
  {
    if (fInstance == null)
      fInstance = new ZCompiler();
    return fInstance;
  }

  /**
   * Parse the input in an fEditor
   */
  public ParsedData parse()
  {
    ZEditor editor = getEditor();
    IDocument document = editor.getDocumentProvider().getDocument(
        editor.getEditorInput());
    fParsedData = new ParsedData(editor);
    Spec parsed = null;
    List<CztError> errors = new ArrayList<CztError>();
    
    SectionManager sectMan = CZTPlugin.getDefault().getSectionManager();
    
    final String name = ((IFileEditorInput) editor
        .getEditorInput()).getFile().getName();
    final Source source = new StringSource(document.get(), name);
    source.setMarkup(editor.getMarkup()); // or Markup.UNICODE
    source.setEncoding(editor.getEncoding()); // for Unicode
    
    try {
      sectMan.put(new Key(this.getCurrentSection(), Source.class), source);
      parsed = (Spec) sectMan
          .get(new Key(this.getCurrentSection(), Spec.class));
      if (parsed != null) {
        for (Sect sect : parsed.getSect()) {
          if (sect instanceof ZSect) {
            sectMan.get(new Key(((ZSect) sect).getName(),
                                SectTypeEnvAnn.class));
          }
        }
      
        if (parsed.getSect().size() > 0) {
          fParsedData.addData(parsed, sectMan, document);
        }
      }
      
      try {
        ParseException parseException = (ParseException)
          sectMan.get(new Key(source.getName(), ParseException.class));
        if (parseException != null) {
          errors.addAll(parseException.getErrors());
        }
      }
      catch (CommandException ce) {
        // TODO Is ignoring OK?
      }
    } catch (CommandException ce) {
      errors.clear();
      Throwable cause = ce.getCause();
      
/*
      if (cause instanceof ParseException) {
        System.out.println("ParseErrorException starts");
        List<CztError> parseErrors = ((ParseException) cause).getErrorList();
        errors.addAll(parseErrors);
        System.out.println("ParseErrorException finishes");
      }
      else if (cause instanceof TypeErrorException) {
        System.out.println("TypeErrorException starts");
        List<ErrorAnn> typeErrors = ((TypeErrorException) cause).errors();
        errors.addAll(typeErrors);
        System.out.println("TypeErrorException finishes");
      }
*/
      if (cause instanceof CztErrorList) {
        errors.addAll(((CztErrorList) cause).getErrors());
      }
      else if (cause instanceof IOException) {
        String ioError = "Input output error: " + cause.getMessage();
        System.out.println(ioError);
      }
      else {
        String otherError = cause + getClass().getName();
        System.out.println(otherError);
      }
    }
    
    fParsedData.setErrors(errors);
    
    return fParsedData;
  }

  /** Which section evaluations are being done in. */
  public String getCurrentSection()
  {
    return this.sectionName_;
  }

  public void setCurrentSection(String sectName)
  {
    if (sectName == null)
      this.sectionName_ = this.DEFAULT_SECTION_NAME;
    else if (sectName.equals("") || sectName.contains("_"))
      this.sectionName_ = this.DEFAULT_SECTION_NAME;
    else
      this.sectionName_ = sectName;
  }

  public ZEditor getEditor()
  {
    return this.fEditor;
  }

  public void setEditor(ZEditor editor)
  {
    this.fEditor = editor;
  }

  public ParsedData getParsedData()
  {
    return this.fParsedData;
  }
}

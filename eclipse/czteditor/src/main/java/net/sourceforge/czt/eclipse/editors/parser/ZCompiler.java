
package net.sourceforge.czt.eclipse.editors.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

import org.eclipse.core.resources.IFile;
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
    
    SectionManager sectMan = CZTPlugin.getDefault().getSectionManager();

    final IFile file = ((IFileEditorInput) editor.getEditorInput()).getFile();
    final String name = file.getName();
    final Source source = new StringSource(document.get(), name);
    source.setMarkup(editor.getMarkup()); // or Markup.UNICODE
    source.setEncoding(editor.getEncoding()); // for Unicode

    // MarkU: set czt.path to the directory that contains this file
    String path = file.getLocation().toString();
    assert path.endsWith(name);
    String dir = path.substring(0, path.lastIndexOf(name));
    //System.out.println("DEBUG: setting czt.path to "+dir);
    sectMan.setProperty("czt.path", dir);

    Spec parsed = null;
    List<CztError> errors = new ArrayList<CztError>();

    // set the source for parsing and checking
    sectMan.put(new Key<Source>(this.getCurrentSection(), Source.class), source);

    try {
      // do the parsing
      parsed = sectMan.get(new Key<Spec>(this.getCurrentSection(), Spec.class));
    } catch (CommandException ce) {
      errors.addAll(handleException(ce));
    }

    if (parsed != null) {
      for (Sect sect : parsed.getSect()) {
        if (sect instanceof ZSect) {
          try {
            // typecheck sections
            sectMan.get(new Key<SectTypeEnvAnn>(((ZSect) sect).getName(), SectTypeEnvAnn.class));
          } catch (CommandException ce) {
            errors.addAll(handleException(ce));
          }
        }
      }

      if (parsed.getSect().size() > 0) {
        fParsedData.addData(parsed, sectMan, document);
      }
    }

    try {
      // check for parse exceptions
      ParseException parseException = (ParseException) sectMan.get(
          new Key<ParseException>(source.getName(), ParseException.class));
      
      if (parseException != null) {
        errors.addAll(parseException.getErrors());
      }
    } catch (CommandException ce) {
      // TODO Is ignoring OK?
      CZTPlugin.log("Unexpected error in Z compiler: " + ce.getMessage(), ce);
    }

    fParsedData.setErrors(errors);

    return fParsedData;
  }

  private List<? extends CztError> handleException(CommandException ex)
  {

	  Throwable cause = ex.getCause();
	  if (cause == null) {
		  // use the exception itself
		  cause = ex;
	  }
	  
//    if (cause instanceof ParseException) {
//      return ((ParseException) cause).getErrorList();
//    }
//
//    if (cause instanceof TypeErrorException) {
//      return ((TypeErrorException) cause).errors();
//    }

    if (cause instanceof CztErrorList) {
      return ((CztErrorList) cause).getErrors();
    }

    if (cause instanceof IOException) {
      CZTPlugin.log("Input output error: " + cause.getMessage(), cause);
    }
    else {
      CZTPlugin.log("Unknown error in Z compiler: " + String.valueOf(cause), cause);
    }

    return Collections.<CztError> emptyList();
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

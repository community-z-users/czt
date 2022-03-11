
package net.sourceforge.czt.eclipse.ui.internal.editors.parser;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.eclipse.core.parser.StringFileSource;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.typecheck.z.SectWarningsAnn;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IFileEditorInput;

/**
 * @author Chengdong Xu
 */
public enum ZCompiler
{
  
  INSTANCE;

  public static final String DEFAULT_SECTION_NAME = "NEWSECTION";

  private String sectionName_ = DEFAULT_SECTION_NAME;

  public static ZCompiler getInstance()
  {
    return INSTANCE;
  }

  /**
   * Parse the input in an fEditor
   */
  public ParsedData parse(ZEditor editor, BigInteger documentVersion)
  {
    IDocument document = editor.getDocumentProvider().getDocument(
        editor.getEditorInput());
    
    SectionManager sectMan = CztUIPlugin.getDefault().getSectionManager();
    
    // init dynamic sources from other editors
    initEditorSourcesCommand(sectMan);
    
    final IFile file = ((IFileEditorInput) editor.getEditorInput()).getFile();
    final String name = file.getName();
    // The document version was retrieved before the document contents, which 
    // will ensure the document is up-to-date or newer for that version.
    final Source source = new StringFileSource(document.get(), file.getLocation().toOSString());
    source.setName(name);
    source.setMarkup(editor.getMarkup()); // or Markup.UNICODE
    source.setEncoding(editor.getEncoding()); // for Unicode

    // MarkU: set czt.path to the directory that contains this file
    IPath path = file.getLocation();
    if (path != null) {
      IPath dirPath = path.removeLastSegments(1).addTrailingSeparator();
      String dir = dirPath.toString();
      
      //System.out.println("DEBUG: setting czt.path to "+dir);
      sectMan.setProperty(SourceLocator.PROP_CZT_PATH, dir);
    }

    ParsedData parsedData = new ParsedData(documentVersion, sectMan);
    
    Spec parsed = null;
    List<CztError> errors = new ArrayList<CztError>();

    // set the source for parsing and checking
    sectMan.put(new Key<Source>(this.getCurrentSection(), Source.class), source);

    try {
      // do the parsing
      parsed = sectMan.get(new Key<Spec>(this.getCurrentSection(), Spec.class));
    } catch (CommandException ce) {
      errors.addAll(handleException(ce, sectMan.getDialect()));
    }

    if (parsed != null) {
      for (Sect sect : parsed.getSect()) {
        if (sect instanceof ZSect) {
          
          ZSect zSect = (ZSect) sect;
          
          try {
            // typecheck sections
            sectMan.get(new Key<SectTypeEnvAnn>(zSect.getName(), SectTypeEnvAnn.class));
          } catch (CommandException ce) {
            errors.addAll(handleException(ce, sectMan.getDialect()));
          }
          
          // check for warnings after typechecking
          SectWarningsAnn warnings = zSect.getAnn(SectWarningsAnn.class);
          if (warnings != null) {
            errors.addAll(warnings.getWarnings());
          }
          
          // TODO warnings about parents?
        }
      }

      if (parsed.getSect().size() > 0) {
        parsedData.setData(parsed, document);
      }
    }

    try {
      // check for parse exceptions
      ParseException parseException = sectMan.get(
          new Key<ParseException>(source.getName(), ParseException.class));
      
      if (parseException != null) {
        errors.addAll(parseException.getErrors());
      }
    } catch (CommandException ce) {
      // TODO Is ignoring OK?
      CztUIPlugin.log("Unexpected error in " + sectMan.getDialect().toString() + " compiler : " + ce.getMessage(), ce);
    }

    parsedData.setErrors(errors);

    return parsedData;
  }

  private List<? extends CztError> handleException(CommandException ex, Dialect dialect)
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
      CztUIPlugin.log("Input output error: " + cause.getMessage(), cause);
    }
    else {
      CztUIPlugin.log("Unknown error in " + dialect.toString() + " compiler: " + String.valueOf(cause), cause);
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
      this.sectionName_ = DEFAULT_SECTION_NAME;
    else if (sectName.equals("") || sectName.contains("_"))
      this.sectionName_ = DEFAULT_SECTION_NAME;
    else
      this.sectionName_ = sectName;
  }
  
  /**
   * Initializes the section manager to use a dynamic source locator, which utilizes content from
   * editors, instead of saved files, if available. This allows for re-parsing using the most
   * up-to-date parents (otherwise if they are not saved, the changes are not used).
   * 
   * @param sectMan
   */
  private void initEditorSourcesCommand(SectionManager sectMan) {

    Command sourceCmd = sectMan.getCommand(Source.class);
    if (sourceCmd.getClass().equals(SourceLocator.class)) {
      // replace the original source locator with a dynamic one
      sectMan.putCommand(Source.class, new DocumentSourceLocator());
    }
  }

}

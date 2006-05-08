package net.sourceforge.czt.eclipse.editors.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.Spec;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IFileEditorInput;

/**
 * @author Chengdong Xu
 */
public class ZCompiler {
	private static ZCompiler fInstance;
	private ZCompilerMessageParser fCompMsgParser;
	private ZEditor fEditor = null;
	private final String DEFAULT_SECTION_NAME = "NEWSECTION";
	private String sectionName_ = DEFAULT_SECTION_NAME;
	private ParsedData fParsedData = null;
	
	/**
	 * Constructor
	 */
	private ZCompiler() {
		fCompMsgParser = new ZCompilerMessageParser();
		fInstance = this;
	}
	
	public static ZCompiler getInstance() {
		if (fInstance == null)
			fInstance = new ZCompiler();
		return fInstance;
	}
	
	/**
	 * Parse the input in an editor
	 */
	public ParsedData parse() {
		ZEditor editor = getEditor();
		IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		this.fParsedData = new ParsedData(editor.getEditorInput().getName());
		SectionManager sectMan = CZTPlugin.getDefault().getSectionManager();
		List<CztError> errors = new ArrayList<CztError>();
		
		Source source = new StringSource(document.get(), ((IFileEditorInput)editor.getEditorInput()).getFile().getName());
		source.setMarkup(editor.getMarkup());     // or Markup.UNICODE
		System.out.println(source.getMarkup());
		source.setEncoding(editor.getEncoding());   // for Unicode
		System.out.println(source.getEncoding());
		
		Spec parsed = null;
		
		try {
			sectMan.put(new Key(this.getCurrentSection(), Source.class), source);
			parsed = (Spec) sectMan.get(new Key(this.getCurrentSection(), Spec.class));
			if (parsed != null)
				errors.addAll(TypeCheckUtils.typecheck(parsed, sectMan));

			if (parsed.getSect().size() > 0)	        
		        this.fParsedData.addData(parsed, sectMan, document);
		} catch (CommandException ce) {
			errors.clear();
			Throwable cause = ce.getCause();
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
		    else if (cause instanceof IOException) {
		        String ioError = "Input output error: " + cause.getMessage();
		        System.out.println(ioError);
		    }
		    else {
		        String otherError = cause + getClass().getName();
		        System.out.println(otherError);
		    }
		}
		
		// now display any parse errors or typecheck errors.
//		StringBuffer out = new StringBuffer();
//		out.append(message);
		
//		if (errors != null && errors.size() > 0) {
			//append each error
//			for (int i=0; i<errors.size(); i++)
//				out.append("\n" + errors.get(i).toString());
//		}
		
		// prints out the information
		//CZTConsoleUtilities.outputToConsole(out.toString());
//		System.out.println(out.toString());
		
		// parse the buffer to find the errors and create markers
		try {
			createMarkers(errors, ((IFileEditorInput)editor.getEditorInput()).getFile(), editor.getDocumentProvider().getDocument(editor.getEditorInput()));
//			createMarkers(errors, (IResource)source);
		} catch (CoreException ce) {
			ce.printStackTrace();
		}
		
		this.fEditor.setParsedData(this.fParsedData);
		return this.fParsedData;
	}

	/**
	 * Create markers according to the compiler output
	 */
	protected void createMarkers(List<CztError> errors, IResource resource, IDocument document) throws CoreException {
		// first delete all the previous markers
		resource.deleteMarkers(IMarker.PROBLEM, false, 0);

		ZCompilerMessageParser compMsgParser = getZCompilerMessageParser();
		compMsgParser.parseCompilerMessage(document, resource, errors);
	}

	/** Which section evaluations are being done in. */
	public String getCurrentSection() {
		return this.sectionName_;
	}
	
	public void setCurrentSection(String sectName) {
		if (sectName == null)
			this.sectionName_ = this.DEFAULT_SECTION_NAME;
		else if (sectName.equals("") || sectName.contains("_"))
			this.sectionName_ = this.DEFAULT_SECTION_NAME;
		else
			this.sectionName_ = sectName;
	}
	
	private ZCompilerMessageParser getZCompilerMessageParser() {
		if (this.fCompMsgParser == null)
			this.fCompMsgParser = new ZCompilerMessageParser();
		
		return this.fCompMsgParser;
	}
	
	public ZEditor getEditor() {
		return this.fEditor;
	}
	
	public void setEditor(ZEditor editor) {
		this.fEditor = editor;
	}
	
	public ParsedData getParsedData() {
		return this.fParsedData;
	}
}

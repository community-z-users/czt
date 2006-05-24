/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.parser;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.eclipse.util.IZMarker;
import net.sourceforge.czt.parser.util.CztError;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.texteditor.MarkerUtilities;

/**
 * @author Chengdong Xu
 */
public class ZCompilerMessageParser {
    protected static final String ERROR = "error"; //$NON-NLS-1$

    protected static final String WARNING = "warning"; //$NON-NLS-1$

    private IResource fResource = null;
    private IDocument fDocument = null;
    
	/**
	 * 
	 */
    public void parseCompilerMessage(IDocument document, IResource resource, List<CztError> errors)
            throws CoreException {
        this.fResource = resource;
        this.fDocument = document;
        for (int i=0; i<errors.size(); i++) {
        	parseError(errors.get(i));
        }
    }

    
	/**
     * @param error a Czt error
     */
	protected void parseError(CztError error)
			throws CoreException {
		String message = error.getMessage();
		int line = error.getLine();
		int column = error.getColumn();
		int start = error.getStart();
		int length = error.getLength();
		int end;
		
		try {
			if (start < 0)
				start = this.fDocument.getLineOffset(line) + column;
			else
				line = this.fDocument.getLineOfOffset(start);
			
			if (length < 0)
				length = this.fDocument.getLineLength(line) - column;
		} catch(BadLocationException ble) {
			ble.printStackTrace();
		}
		
		end = start + length - 1;
		
		setMarker(message, line + 1, start, end);
	}
	
    /**
     * @param message
     * @param lineNumber
     * @param charStart
     * @param charEnd
     * @throws CoreException
     */
    protected void setMarker(String message, int lineNumber, int charStart, int charEnd) throws CoreException {
    	Map<String, Object> attributes = new HashMap<String, Object>();
    	
    	attributes.put(IMarker.SEVERITY,
    			new Integer(IMarker.SEVERITY_ERROR));
    	attributes.put(IMarker.PRIORITY,
    			new Integer(IMarker.PRIORITY_HIGH));
    	attributes.put(IMarker.LINE_NUMBER,
    			new Integer(lineNumber));
    	attributes.put(IMarker.CHAR_START,
    			new Integer(charStart));
    	attributes.put(IMarker.CHAR_END,
    			new Integer(charEnd));
    	attributes.put(IMarker.MESSAGE,
    			message);
    	
    	MarkerUtilities.createMarker(this.fResource, attributes,
    			IZMarker.PROBLEM);
    }
}

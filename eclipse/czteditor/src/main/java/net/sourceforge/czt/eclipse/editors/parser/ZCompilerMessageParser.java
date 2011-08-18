package net.sourceforge.czt.eclipse.editors.parser;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.eclipse.util.IZMarker;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ErrorType;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZCompilerMessageParser
{

  private IResource fResource = null;

  private IDocument fDocument = null;

  public void parseCompilerMessage(IDocument document, IResource resource,
      List<CztError> errors) throws CoreException
  {
    this.fResource = resource;
    this.fDocument = document;
    
    List<Entry<String, Map<String, Object>>> markers = new ArrayList<Entry<String, Map<String, Object>>>();
    for (int i = 0; i < errors.size(); i++) {
      markers.add(parseError(errors.get(i)));
    }
    
    createMarkers(markers);
  }

  /**
   * @param error a Czt error
   */
  protected Entry<String, Map<String, Object>> parseError(CztError error)
  {
    ErrorType errorType = error.getErrorType();
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
    } catch (BadLocationException ble) {
      ble.printStackTrace();
    }

    end = start + length;

    int severity = ErrorType.ERROR.equals(errorType) ? IMarker.SEVERITY_ERROR : IMarker.SEVERITY_WARNING;
    return setMarker(severity, message, line + 1, start, end);
  }

  /**
   * @param message
   * @param lineNumber
   * @param charStart
   * @param charEnd
   * @throws CoreException
   */
  private Entry<String, Map<String, Object>> setMarker(int severity, String message,
      int lineNumber, int charStart, int charEnd)
  {
    Map<String, Object> attributes = new HashMap<String, Object>();

    attributes.put(IMarker.SEVERITY, new Integer(severity));
    attributes.put(IMarker.PRIORITY, new Integer(IMarker.PRIORITY_HIGH));
    attributes.put(IMarker.LINE_NUMBER, new Integer(lineNumber));
    attributes.put(IMarker.CHAR_START, new Integer(charStart));
    attributes.put(IMarker.CHAR_END, new Integer(charEnd));
    attributes.put(IMarker.MESSAGE, message);

    // mark all markers and create later in batch mode to avoid too many refresh events
//    MarkerUtilities.createMarker(this.fResource, attributes, IZMarker.PROBLEM);
    return new SimpleEntry<String, Map<String, Object>>(IZMarker.PROBLEM, attributes);
  }
  
  public void createMarkers(final List<Entry<String, Map<String, Object>>> markers)
      throws CoreException
  {

    IWorkspaceRunnable r = new IWorkspaceRunnable()
    {
      public void run(IProgressMonitor monitor) throws CoreException
      {
        for (Entry<String, Map<String, Object>> markerEntry : markers) {
          IMarker marker = fResource.createMarker(markerEntry.getKey());
          marker.setAttributes(markerEntry.getValue());
        }
      }
    };

    fResource.getWorkspace().run(r, null, IWorkspace.AVOID_UPDATE, null);
  }
}

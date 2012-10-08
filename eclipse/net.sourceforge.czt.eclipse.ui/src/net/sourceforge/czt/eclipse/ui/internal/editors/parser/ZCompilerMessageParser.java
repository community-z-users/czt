package net.sourceforge.czt.eclipse.ui.internal.editors.parser;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.compile.IZProblemSeverityProvider;
import net.sourceforge.czt.eclipse.ui.compile.ZProblemSeverity;
import net.sourceforge.czt.eclipse.ui.internal.util.IZMarker;
import net.sourceforge.czt.eclipse.ui.util.MarkerUtil;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ErrorType;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZCompilerMessageParser
{

  // the ID of problem severity providers extension point
  private static final String SEVERITY_PROVIDERS_ID = "net.sourceforge.czt.eclipse.ui.problemSeverityProviders";
  
  private final List<IZProblemSeverityProvider> providers = new ArrayList<IZProblemSeverityProvider>();
  
  public ZCompilerMessageParser()
  {
    loadSeverityProviders();
  }

  /*
   * Loads the available severity providers from an extension point
   */
  private void loadSeverityProviders()
  {
    IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(
        SEVERITY_PROVIDERS_ID);

    try {
      for (IConfigurationElement e : config) {
        final Object o = e.createExecutableExtension("class");
        if (o instanceof IZProblemSeverityProvider) {
          providers.add((IZProblemSeverityProvider) o);
        }
      }
    }
    catch (CoreException ex) {
      CztUIPlugin.log(ex);
    }
  }

  public void parseCompilerMessage(String dialect, IDocument document, IResource resource,
      List<CztError> errors) throws CoreException
  {
    List<Entry<String, Map<String, Object>>> markers = new ArrayList<Entry<String, Map<String, Object>>>();
    for (CztError error : errors) {
      Entry<String, Map<String, Object>> markerInfo = parseError(dialect, document, error);
      if (markerInfo != null) {
        markers.add(markerInfo);
      }
    }
    
    createMarkers(resource, markers);
  }

  /**
   * @param error a Czt error
   */
  private Entry<String, Map<String, Object>> parseError(String dialect, IDocument document, CztError error)
  {
    ErrorType errorType = error.getErrorType();
    if (errorType == ErrorType.WARNING) {
      // check the severity preferences for warnings
      // for example, a user may choose to ignore certain warnings, or display them as errors
      ZProblemSeverity severity = getSeverityPreference(dialect, error);
      if (severity != null) {
        switch (severity) {
          case ERROR: {
            errorType = ErrorType.ERROR;
            break;
          }
          case WARNING: {
            errorType = ErrorType.WARNING;
            break;
          }
          case IGNORE: {
            // ignore this
            return null;
          }
        }
      }
    } else {
      // errors are always kept
    }
    
    String message = error.getMessage();
    int line = error.getLine();
    int column = error.getColumn();
    int start = error.getStart();
    int length = error.getLength();
    
    if (line < 0) {
      line = 0;
    } else if (line >= document.getNumberOfLines()) {
      line = document.getNumberOfLines() - 1;
      column = 0;
    }
    
    if (column < 0) {
      column = 0;
    }

    try {
      if (start < 0)
        start = document.getLineOffset(line) + column;
      else
        line = document.getLineOfOffset(start);

      if (length < 0)
        length = document.getLineLength(line) - column;
    } catch (BadLocationException ble) {
      ble.printStackTrace();
    }

    int end = start + length;

    int severity = errorType == ErrorType.WARNING ? IMarker.SEVERITY_WARNING : IMarker.SEVERITY_ERROR;
    return setMarker(severity, message, line + 1, start, end);
  }
  
  /*
   * Checks the providers whether a specific severity is indicated for the error.
   * Returns null if no preference is given.
   */
  private ZProblemSeverity getSeverityPreference(final String dialect, final CztError err) {
    
    for (final IZProblemSeverityProvider provider : providers) {

      final ZProblemSeverity[] severity = new ZProblemSeverity[1];

      // run safely - implementation can come from other plugins
      ISafeRunnable runnable = new ISafeRunnable()
      {
        @Override
        public void handleException(Throwable exception)
        {
          CztUIPlugin.log(exception);
        }

        @Override
        public void run() throws Exception
        {
          severity[0] = provider.getSeverity(dialect, err);
        }
      };

      SafeRunner.run(runnable);
      
      if (severity[0] != null) {
        // found explicit severity
        // TODO check if multiple extensions can have preference on the same error?
        return severity[0];
      }
    }
    
    return null;
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
    attributes.put(IMarker.MESSAGE, MarkerUtil.adaptMarkerValue(message));

    // mark all markers and create later in batch mode to avoid too many refresh events
//    MarkerUtilities.createMarker(this.fResource, attributes, IZMarker.PROBLEM);
    return new SimpleEntry<String, Map<String, Object>>(IZMarker.PROBLEM, attributes);
  }
  
  private void createMarkers(final IResource resource,
      final List<Entry<String, Map<String, Object>>> markers) throws CoreException
  {

    IWorkspaceRunnable r = new IWorkspaceRunnable()
    {
      public void run(IProgressMonitor monitor) throws CoreException
      {
        for (Entry<String, Map<String, Object>> markerEntry : markers) {
          IMarker marker = resource.createMarker(markerEntry.getKey());
          marker.setAttributes(markerEntry.getValue());
        }
      }
    };

    resource.getWorkspace().run(r, null, IWorkspace.AVOID_UPDATE, null);
  }
  
}

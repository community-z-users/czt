package net.sourceforge.czt.eclipse.zeves.ui.editor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.core.document.IPositionProvider;
import net.sourceforge.czt.eclipse.core.document.TermPositionProvider;
import net.sourceforge.czt.eclipse.ui.util.TextUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecContext;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.ui.editor.ZEvesMarkers.MarkerInfo;
import net.sourceforge.czt.text.Position;

/**
 * 
 * @author Andrius Velykis
 */
public class EditorZEvesExecContext implements ZEvesExecContext
{

  private final Map<String, EditorContext> fileContexts = new HashMap<String, EditorContext>();
  
  private static final long FLUSH_INTERVAL = 500;
  
  public EditorZEvesExecContext() {}
  
  public EditorZEvesExecContext(String file, IResource fileResource, IDocument document) {
    fileContexts.put(file, initFileContext(fileResource, document));
  }
  
  @Override
  public Position adaptFullLine(String file, Position pos)
  {
    IDocument document = getFileContext(file).document;

    if (document == null) {
      return pos;
    }

    try {
      int line = document.getLineOfOffset(pos.getOffset());
      int lineStart = document.getLineOffset(line);
      if (lineStart >= pos.getOffset()) {
        // already full line
        return pos;
      }

      // starting in the middle of the line - get the next line
      if (line < document.getNumberOfLines() - 1) {
        int nextLine = line + 1;
        int nextLineStart = document.getLineOffset(nextLine);
        int posEnd = pos.getEndOffset();
        if (nextLineStart <= posEnd) {
          return Position.createStartEnd(nextLineStart, posEnd);
        }
      }

    }
    catch (BadLocationException e) {
      // ignore
    }

    // invalid - return previous
    return pos;
  }

  @Override
  public IPositionProvider<? super Term> getTermPositions(String file)
  {
    return getFileContext(file).posProvider;
  }

  @Override
  public boolean addMessage(String file, Position pos, String message, ZEvesMessageType type)
  {

    EditorContext context = getFileContext(file);

    if (context.markers == null) {
      return false;
    }

    org.eclipse.jface.text.Position ePos = TextUtil.jfacePos(pos);

    try {

      switch (type) {

        case ERROR : {
          context.markers.createErrorMarker(ePos, message, IMarker.SEVERITY_ERROR);
          return true;
        }

        case WARNING : {
          context.markers.createErrorMarker(ePos, message, IMarker.SEVERITY_WARNING);
          return true;
        }

        case INFO : {
          context.markers.createErrorMarker(ePos, message, IMarker.SEVERITY_INFO);
          return true;
        }

        case RESULT : {
          context.markers.createResultMarker(ePos, message);
          return true;
        }

        case RESULT_TRUE : {
          context.markers.createResultTrueMarker(ePos, message);
          return true;
        }
      }

    }
    catch (CoreException ce) {
      ZEvesUIPlugin.getDefault().log(ce);
      return false;
    }

    return false;
  }

  @Override
  public boolean addStatus(String file, Position pos, ZEvesStatus type)
  {
    EditorContext context = getFileContext(file);
    
    if (context.markers == null) {
      return false;
    }
    
    MarkerId markerId = new MarkerId(pos, type);
    
    if (!context.markerCache.containsKey(markerId)) {
      try {
        MarkerInfo marker = createStatusMarker(context.markers, pos, type);
        context.markerCache.put(markerId, marker);
        
        // try flushing after updating the status to provide a timely feedback to the user
        context.tryFlush();
        
        return true;
      }
      catch (CoreException ce) {
        ZEvesUIPlugin.getDefault().log(ce);
        return false;
      }
    }
    
    return false;
  }

  @Override
  public boolean removeStatus(String file, Position pos, ZEvesStatus type)
  {
    EditorContext context = getFileContext(file);
    
    if (context.markers == null) {
      return false;
    }

    MarkerId markerId = new MarkerId(pos, type);

    MarkerInfo marker = context.markerCache.remove(markerId);
    if (marker != null) {
      context.markers.deleteMarker(marker);
      return true;
    }
    
    return false;
  }

  @Override
  public boolean clearMarkers(String file)
  {
    EditorContext context = getFileContext(file);

    if (context.markers == null) {
      return false;
    }

    try {
      context.markers.clearMarkers();
      return true;
    }
    catch (CoreException ce) {
      ZEvesUIPlugin.getDefault().log(ce);
      return false;
    }
  }
  
  @Override
  public void completed(String file)
  {
    // flush markers
    getFileContext(file).flush();
  }

  private EditorContext getFileContext(String file) {
    EditorContext context = fileContexts.get(file);
    if (context == null) {
      context = initFileContext(file);
      fileContexts.put(file, context);
    }
    
    return context;
  }
  
  private EditorContext initFileContext(String file)
  {

    IFile fileResource = null;
    List<IFile> files = ResourceUtil.findFile(file);
    if (files.size() > 0) {
      // take the first one found
      // TODO support multiple resources (e.g. the same file is several times in the workspace)?
      fileResource = files.get(0);
    }

    IDocument document = null;
    if (fileResource != null) {
      TextFileDocumentProvider documentProvider = new TextFileDocumentProvider();
      try {
        documentProvider.connect(fileResource);
        document = documentProvider.getDocument(fileResource);
      }
      catch (CoreException e) {
        // ignore?
        ZEvesUIPlugin.getDefault().log(e);
      }
    }
    
    return initFileContext(fileResource, document);
  }
  
  private static EditorContext initFileContext(IResource fileResource, IDocument document)
  {
    ZEvesMarkers fileMarkers = fileResource != null
        ? new ZEvesMarkers(fileResource, document)
        : null;

    IPositionProvider<Term> posProvider = new TermPositionProvider(document);

    return new EditorContext(document, posProvider, fileMarkers);
  }
  
  private MarkerInfo createStatusMarker(ZEvesMarkers markers, Position pos, ZEvesStatus type) throws CoreException {
    
    org.eclipse.jface.text.Position ePos = TextUtil.jfacePos(pos);
    
    switch (type) {
      case FAILED: return markers.createStatusMarker(ePos, ZEvesMarkers.STATUS_FAILED);
      
      case FINISHED: return markers.createStatusMarker(ePos, ZEvesMarkers.STATUS_FINISHED);
      
      case UNFINISHED: return markers.createStatusMarker(ePos, ZEvesMarkers.STATUS_UNFINISHED);
      
      case UNPROCESSED: return markers.createProcessMarker(ePos);
      
      default: throw new CoreException(
          ZEvesUIPlugin.newErrorStatus("Invalid Z/EVES command status type: " + type, null));
    }
  }
  

  private static class EditorContext
  {
    private final IDocument document;

    private final IPositionProvider<? super Term> posProvider;

    private final ZEvesMarkers markers;

    private final Map<MarkerId, MarkerInfo> markerCache = new HashMap<MarkerId, MarkerInfo>();

    private long lastFlush = 0;

    public EditorContext(IDocument document,
        IPositionProvider<? super Term> posProvider,
        ZEvesMarkers markers)
    {
      super();
      this.document = document;
      this.posProvider = posProvider;
      this.markers = markers;
    }

    public void tryFlush()
    {
      if (System.currentTimeMillis() - lastFlush > FLUSH_INTERVAL) {
        flush();
      }
    }

    public void flush()
    {
      if (markers != null) {
        markers.flushPendingMarkers();
      }

      lastFlush = System.currentTimeMillis();
    }
  }
  

  private static class MarkerId
  {
    private final Position pos;

    private final ZEvesStatus type;

    public MarkerId(Position pos, ZEvesStatus type)
    {
      super();
      this.pos = pos;
      this.type = type;
    }

    @Override
    public int hashCode()
    {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((pos == null) ? 0 : pos.hashCode());
      result = prime * result + ((type == null) ? 0 : type.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj)
    {
      if (this == obj)
        return true;
      if (obj == null)
        return false;
      if (getClass() != obj.getClass())
        return false;
      MarkerId other = (MarkerId) obj;
      if (pos == null) {
        if (other.pos != null)
          return false;
      }
      else if (!pos.equals(other.pos))
        return false;
      if (type != other.type)
        return false;
      return true;
    }
  }

}

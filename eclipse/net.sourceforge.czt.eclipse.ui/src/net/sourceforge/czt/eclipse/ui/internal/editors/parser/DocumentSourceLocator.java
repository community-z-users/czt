package net.sourceforge.czt.eclipse.ui.internal.editors.parser;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.core.document.DocumentUtil;
import net.sourceforge.czt.eclipse.core.parser.StringFileSource;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;

/**
 * An extension of the default {@link SourceLocator} for CZT, which uses current contents of the
 * files, which are open in editors. The default SourceLocator uses saved files, however this class
 * replaces the saved files with copies from editors, where the files are edited - it may be an
 * unsaved updated version of the file.
 * 
 * @author Andrius Velykis
 */
public class DocumentSourceLocator extends SourceLocator
{

  @Override
  protected boolean doCompute(String name, SectionManager manager) throws CommandException
  {
    if (!super.doCompute(name, manager)) {
      // default source computation failed - do not do anything more
      return false;
    }
    
    Key<Source> key = new Key<Source>(name, Source.class);
    if (!manager.isCached(key)) {
      // strange - should not happen if the computation was successful
      return false;
    }
    
    Source source = manager.get(key);
    // check if we can resolve the path of the given source
    String path = DocumentUtil.getPath(source);
    if (path == null) {
      // unable to determine source path - keep the old source
      return true;
    }
    
    // go through each of the open editors and check if they are editing the found path
    for (IEditorPart editor : PlatformUtil.getOpenEditors()) {
      if (editor instanceof ITextEditor) {
        
        IResource resource = ZEditorUtil.getEditorResource(editor);
        if (resource != null) {
          
          if (path.equals(resource.getLocation().toOSString())) {
            // same resource - now get the document
            IDocument document = ZEditorUtil.getDocument((ITextEditor) editor);
            if (document != null) {
              // use the document for the source
              // replace the source - so remove the previous one
              manager.removeKey(key);
              manager.put(key, createFileSource(path, document.get(), source));
              return true;
            }
          }
        }
      }
    }
    
    return true;
  }
  
  private Source createFileSource(String path, String content, Source prevSource) {
    Source source = new StringFileSource(content, path);
    source.setName(prevSource.getName());
    source.setEncoding(prevSource.getEncoding());
    source.setMarkup(prevSource.getMarkup());
    return source;
  }

  

}

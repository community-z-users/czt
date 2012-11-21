package net.sourceforge.czt.eclipse.ui.editors;

import java.math.BigInteger;

import net.sourceforge.czt.eclipse.core.compile.IZCompileData;
import net.sourceforge.czt.session.Markup;

import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * 
 * @author Andrius Velykis
 */
public interface IZEditor extends ITextEditor
{

  public Markup getMarkup();

  public IZCompileData getParsedData();

  public BigInteger getDocumentVersion();

  public void forceReconcile();
  
  public ISourceViewer getViewer();

}

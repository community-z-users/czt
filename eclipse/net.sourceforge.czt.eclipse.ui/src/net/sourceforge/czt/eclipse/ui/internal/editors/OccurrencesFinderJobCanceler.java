/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.IDocumentProvider;

/**
 * Cancels the occurrences finder job upon document changes.
 * @since 3.0
 * 
 * @author Chengdong Xu
 */
public class OccurrencesFinderJobCanceler
    implements
      IDocumentListener,
      ITextInputListener
{

  private ZEditor fEditor;

  /**
   * 
   */
  public OccurrencesFinderJobCanceler(ZEditor editor)
  {
    fEditor = editor;
  }

  public void install()
  {
    ISourceViewer sourceViewer = fEditor.getViewer();
    if (sourceViewer == null)
      return;

    StyledText text = sourceViewer.getTextWidget();
    if (text == null || text.isDisposed())
      return;

    sourceViewer.addTextInputListener(this);

    IDocument document = sourceViewer.getDocument();
    if (document != null)
      document.addDocumentListener(this);
  }

  public void uninstall()
  {
    ISourceViewer sourceViewer = fEditor.getViewer();
    if (sourceViewer != null)
      sourceViewer.removeTextInputListener(this);

    IDocumentProvider documentProvider = fEditor.getDocumentProvider();
    if (documentProvider != null) {
      IDocument document = documentProvider.getDocument(fEditor
          .getEditorInput());
      if (document != null)
        document.removeDocumentListener(this);
    }
  }

  /**
   * @see org.eclipse.jface.text.IDocumentListener#documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent)
   */
  public void documentAboutToBeChanged(DocumentEvent event)
  {
    OccurrencesFinderJob job = fEditor.getOccurrencesFinderJob();
    if (job != null)
      job.doCancel();
  }

  /**
   * @see org.eclipse.jface.text.IDocumentListener#documentChanged(org.eclipse.jface.text.DocumentEvent)
   */
  public void documentChanged(DocumentEvent event)
  {

  }

  /**
   * @see org.eclipse.jface.text.ITextInputListener#inputDocumentAboutToBeChanged(org.eclipse.jface.text.IDocument, org.eclipse.jface.text.IDocument)
   */
  public void inputDocumentAboutToBeChanged(IDocument oldInput,
      IDocument newInput)
  {
    if (oldInput == null)
      return;

    oldInput.removeDocumentListener(this);
  }

  /**
   * @see org.eclipse.jface.text.ITextInputListener#inputDocumentChanged(org.eclipse.jface.text.IDocument, org.eclipse.jface.text.IDocument)
   */
  public void inputDocumentChanged(IDocument oldInput, IDocument newInput)
  {
    if (newInput == null)
      return;

    newInput.addDocumentListener(this);
  }

}

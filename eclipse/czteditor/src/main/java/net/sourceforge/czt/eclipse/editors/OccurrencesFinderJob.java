/**
 * 
 */

package net.sourceforge.czt.eclipse.editors;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.IZAnnotationType;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.link.LinkedModeModel;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.ui.texteditor.IDocumentProvider;

/**
 * Finds and marks occurrence annotations.
 * @since 3.0
 * 
 * @author Chengdong Xu
 */
public class OccurrencesFinderJob extends Job
{

  private ZEditor fEditor;

  private IDocument fDocument;

  private Term fSelectedTerm;

  private boolean fCanceled = false;

  private IProgressMonitor fProgressMonitor;

  public OccurrencesFinderJob(ZEditor editor, Term selection)
  {
    //		super(JavaEditorMessages.JavaEditor_markOccurrences_job_name);
    super("MarkOccurrencesJob");
    fEditor = editor;
    fSelectedTerm = selection;
    fDocument = editor.getDocumentProvider().getDocument(
        editor.getEditorInput());
  }

  // cannot use cancel() because it is declared final
  void doCancel()
  {
    fCanceled = true;
    cancel();
  }

  private boolean isCanceled()
  {
    return fCanceled || fProgressMonitor.isCanceled()
        || LinkedModeModel.hasInstalledModel(fDocument);
  }

  /**
   * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
   */
  @Override
  public IStatus run(IProgressMonitor progressMonitor)
  {
    fProgressMonitor = progressMonitor;

    if (isCanceled())
      return Status.CANCEL_STATUS;

    if (fEditor == null)
      return Status.CANCEL_STATUS;

    if (fEditor.getParsedData().getSpec() == null)
      return Status.CANCEL_STATUS;

    if (fSelectedTerm == null)
      return Status.CANCEL_STATUS;

    ITextViewer textViewer = fEditor.getViewer();
    if (textViewer == null)
      return Status.CANCEL_STATUS;

    IDocument document = textViewer.getDocument();
    if (document == null)
      return Status.CANCEL_STATUS;

    IDocumentProvider documentProvider = fEditor.getDocumentProvider();
    if (documentProvider == null)
      return Status.CANCEL_STATUS;

    IAnnotationModel annotationModel = documentProvider
        .getAnnotationModel(fEditor.getEditorInput());
    if (annotationModel == null)
      return Status.CANCEL_STATUS;

    // Finds all occurrences mark annotations
    Map<Annotation, Position> annotationMap = new HashMap<Annotation, Position>();
    String message = null;
    if (fSelectedTerm instanceof ZDeclName)
      message = ((ZDeclName) fSelectedTerm).getWord();
    else if (fSelectedTerm instanceof ZRefName)
      message = ((ZRefName) fSelectedTerm).getWord();
    else
      message = null;

    computeOccurrenceAnnotations(annotationMap, fEditor.getParsedData()
        .getSpec(), fSelectedTerm, message);

    if (isCanceled())
      return Status.CANCEL_STATUS;

    synchronized (fEditor.getAnnotationLock(annotationModel)) {
      if (annotationModel instanceof IAnnotationModelExtension) {
        ((IAnnotationModelExtension) annotationModel).replaceAnnotations(
            fEditor.getOccurrenceAnnotations(), annotationMap);
      }
      else {
        fEditor.removeOccurrenceAnnotations();
        Iterator iter = annotationMap.entrySet().iterator();
        while (iter.hasNext()) {
          Map.Entry mapEntry = (Map.Entry) iter.next();
          if (mapEntry.getValue() != null)
            annotationModel.addAnnotation((Annotation) mapEntry.getKey(),
                (Position) mapEntry.getValue());
        }
      }
      fEditor.setOccurrenceAnnotations((Annotation[]) annotationMap.keySet()
          .toArray(new Annotation[annotationMap.keySet().size()]));
    }

    return Status.OK_STATUS;
  }

  private void computeOccurrenceAnnotations(Map<Annotation, Position> map,
      Term term, Term selected, String message)
  {
    if (term == null)
      return;
    //		String annotationType = "net.sourceforge.czt.eclipse.occurrence";

    for (Object child : term.getChildren()) {
      if (child == null)
        continue;
      if (child instanceof Term) {
        if (child.equals(selected)) {
          map.put(new Annotation(IZAnnotationType.OCCURRENCE, false, message), //$NON-NLS-1$
              fEditor.getParsedData().getTermPosition((Term) child));
        }
        else if (child instanceof ZRefName) {
          if (selected.equals(((ZRefName) child).getDecl())) {
            map.put(
                new Annotation(IZAnnotationType.OCCURRENCE, false, message), //$NON-NLS-1$
                fEditor.getParsedData().getTermPosition((Term) child));
          }
        }
        else
          computeOccurrenceAnnotations(map, (Term) child, selected, message);
      }
    }
  }
}

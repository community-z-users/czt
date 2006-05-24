package net.sourceforge.czt.eclipse.editors.hover;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.eclipse.util.IZAnnotationType;

import org.eclipse.jface.text.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.projection.AnnotationBag;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.texteditor.AnnotationPreference;

/** 
 * The ZAnnotationHover provides the hover support for Z editors
 * Provides a hover popup which appears on top of a Z editor with relevant
 * display information. If the annotation hover does not provide information no
 * hover popup is shown.
 * <p>
 * Clients may implement this interface.
 * </p>
 *
 * @see org.eclipse.ui.IEditorPart
 * @see org.eclipse.jface.text.IAnnotationHover
 *
 * @since 2.0
 * @author Chengdong Xu
 */
 
public class ZAnnotationHover implements IAnnotationHover {

	private static class ZAnnotationHoverType {
	}

	public static final ZAnnotationHoverType VERTICAL_RULER_HOVER= new ZAnnotationHoverType();
	public static final ZAnnotationHoverType TEXT_RULER_HOVER= new ZAnnotationHoverType();
	public static final ZAnnotationHoverType OVERVIEW_RULER_HOVER= new ZAnnotationHoverType();

//	private IPreferenceStore fStore= CZTPlugin.getDefault().getCombinedPreferenceStore();
	private ZAnnotationHoverType fType;

	public ZAnnotationHover(ZAnnotationHoverType type) {
		Assert.isTrue(VERTICAL_RULER_HOVER.equals(type) || TEXT_RULER_HOVER.equals(type) || OVERVIEW_RULER_HOVER.equals(type));
		fType= type;
	}

	private IAnnotationModel getAnnotationModel(ISourceViewer viewer) {
		if (viewer instanceof ISourceViewerExtension2) {
			ISourceViewerExtension2 extension= (ISourceViewerExtension2) viewer;
			return extension.getVisualAnnotationModel();
		}
		return viewer.getAnnotationModel();
	}
	
	private boolean isRulerLine(Position position, IDocument document, int line) {
		if (position.getOffset() > -1 && position.getLength() > -1) {
			try {
				return line == document.getLineOfOffset(position.getOffset());
			} catch (BadLocationException x) {
			}
		}
		System.out.println("isRulerLine end");
		return false;
	}

	@SuppressWarnings("unused")
	private boolean isDuplicateZAnnotation(Map messagesAtPosition, Position position, String message) {
		if (messagesAtPosition.containsKey(position)) {
			Object value= messagesAtPosition.get(position);
			if (message.equals(value))
				return true;

			if (value instanceof List) {
				List messages= (List)value;
				if  (messages.contains(message))
					return true;
				else
					messages.add(message);
			}
			else {
				ArrayList messages= new ArrayList();
				messages.add(value);
				messages.add(message);
				messagesAtPosition.put(position, messages);
			}
		} 
		else
			messagesAtPosition.put(position, message);
		
		return false;
	}

/*
	private boolean includeAnnotation(Annotation annotation, Position position, HashMap messagesAtPosition) {
		AnnotationPreference preference= getAnnotationPreference(annotation);
		if (preference == null)
			return false;

		if (VERTICAL_RULER_HOVER.equals(fType)) {
			String key= preference.getVerticalRulerPreferenceKey();
			// backward compatibility
			if (key != null && !fStore.getBoolean(key))
				return false;
		}
		else if (OVERVIEW_RULER_HOVER.equals(fType)) {
			String key= preference.getOverviewRulerPreferenceKey();
			if (key == null || !fStore.getBoolean(key))
				return false;
		}
		else if (TEXT_RULER_HOVER.equals(fType)) {
			String key= preference.getTextPreferenceKey();
			if (key != null) {
				if (!fStore.getBoolean(key))
					return false;
			} else {
				key= preference.getHighlightPreferenceKey();
				if (key == null || !fStore.getBoolean(key))
					return false;
			}
		}

		String text= annotation.getText();
		return (text != null && !isDuplicateZAnnotation(messagesAtPosition, position, text));
	}
*/
	private List getZAnnotationsForLine(ISourceViewer viewer, int line) {
		IAnnotationModel model= getAnnotationModel(viewer);
		if (model == null)
			return null;

		IDocument document= viewer.getDocument();
		List zAnnotations= new ArrayList();
		HashMap messagesAtPosition= new HashMap();
		Iterator iterator= model.getAnnotationIterator();

		while (iterator.hasNext()) {
			Annotation annotation= (Annotation) iterator.next();
			if (!annotation.getType().equals(IZAnnotationType.ERROR))
				continue;
			Position position= model.getPosition(annotation);
			if (position == null)
				continue;

			if (!isRulerLine(position, document, line))
				continue;

			if (annotation instanceof AnnotationBag) {
				AnnotationBag bag= (AnnotationBag) annotation;
				Iterator e= bag.iterator();
				while (e.hasNext()) {
					annotation= (Annotation) e.next();
					position= model.getPosition(annotation);
//					if (position != null && includeAnnotation(annotation, position, messagesAtPosition))
					if (position != null)
						zAnnotations.add(annotation);
				}
				continue;
			}

//			if (includeAnnotation(annotation, position, messagesAtPosition))
				zAnnotations.add(annotation);
		}

		return zAnnotations;
	}

	/*
	 * @see IVerticalRulerHover#getHoverInfo(ISourceViewer, int)
	 */
	public String getHoverInfo(ISourceViewer sourceViewer, int lineNumber) {
		List zAnnotations= getZAnnotationsForLine(sourceViewer, lineNumber);
		if (zAnnotations != null) {

			if (zAnnotations.size() == 1) {

				// optimization
				Annotation annotation= (Annotation) zAnnotations.get(0);
				String message= annotation.getText();
				if (message != null && message.trim().length() > 0)
					return formatSingleMessage(message);

			} else {

				List messages= new ArrayList();

				Iterator e= zAnnotations.iterator();
				while (e.hasNext()) {
					Annotation annotation= (Annotation) e.next();
					String message= annotation.getText();
					if (message != null && message.trim().length() > 0)
						messages.add(message.trim());
				}

				if (messages.size() == 1)
					return formatSingleMessage((String) messages.get(0));

				if (messages.size() > 1)
					return formatMultipleMessages(messages);
			}
		}
		
		return null;
	}

	/*
	 * Formats a message as text.
	 */
	private String formatSingleMessage(String message) {
/*		
		StringBuffer buffer= new StringBuffer();
		HTMLPrinter.addPageProlog(buffer);
		HTMLPrinter.addParagraph(buffer, HTMLPrinter.convertToHTMLContent(message));
		HTMLPrinter.addPageEpilog(buffer);
		return buffer.toString();
*/
		
		return message;
	}

	/*
	 * Formats multiple message as text.
	 */
	private String formatMultipleMessages(List messages) {
/*		
		StringBuffer buffer= new StringBuffer();
		HTMLPrinter.addPageProlog(buffer);
		HTMLPrinter.addParagraph(buffer, HTMLPrinter.convertToHTMLContent(JavaUIMessages.JavaAnnotationHover_multipleMarkersAtThisLine));

		HTMLPrinter.startBulletList(buffer);
		Iterator e= messages.iterator();
		while (e.hasNext())
			HTMLPrinter.addBullet(buffer, HTMLPrinter.convertToHTMLContent((String) e.next()));
		HTMLPrinter.endBulletList(buffer);

		HTMLPrinter.addPageEpilog(buffer);
		return buffer.toString();
*/

		StringBuffer buffer = new StringBuffer();
		buffer.append("Multiple markers at this line:\n");

		Iterator e = messages.iterator();
		while (e.hasNext()) {
			buffer.append("\t- " + (String)e.next() + "\n");
		}

		return buffer.toString();
	}

	/**
	 * Returns the annotation preference for the given annotation.
	 *
	 * @param annotation the annotation
	 * @return the annotation preference or <code>null</code> if none
	 */
	private AnnotationPreference getAnnotationPreference(Annotation annotation) {
		return EditorsUI.getAnnotationPreferenceLookup().getAnnotationPreference(annotation);
	}
}

/*******************************************************************************
 * Copyright (c) 2000, 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.preferences.ZEditorConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.IZAnnotationType;
import net.sourceforge.czt.z.util.ZString;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IPainter;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.ITextViewerExtension4;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationPainter;
import org.eclipse.jface.text.source.IAnnotationAccess;
import org.eclipse.jface.text.source.IOverviewRuler;
import org.eclipse.jface.text.source.ISharedTextColors;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.AnnotationPainter.IDrawingStrategy;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.AnnotationPreference;

/**
 * Support class used by Z editors to draw and update decorations on the
 * source viewer and its rulers. An instance of this class must be 
 * configured with the needed preference keys and helper objects before
 * it can be used.
 * <p>
 * Once configured, an instance may be installed (see
 * {@link #install(IPreferenceStore) install}) on a preference store, from then
 * on monitoring the configured preference settings and changing the respective
 * decorations. Calling {@link #uninstall() uninstall} will unregister the
 * listeners with the preferences store and must be called before changing the
 * preference store by another call to <code>install</code>.<br>
 * {@link #dispose() dispose} will uninstall the support and remove any
 * decorations from the viewer. It is okay to reuse a
 * <code>SourceViewerDecorationSupport</code> instance after disposing it.
 * </p>
 */
public class ZSpecDecorationSupport
{

  /**
   * Draws a Z schema box around a schema using the first box rendering style.
   */
  private final class FirstBoxRenderingStrategy implements IDrawingStrategy
  {
    /*
     * @see org.eclipse.jface.text.source.AnnotationPainter.IDrawingStrategy#draw(org.eclipse.jface.text.source.Annotation, org.eclipse.swt.graphics.GC, org.eclipse.swt.custom.StyledText, int, int, org.eclipse.swt.graphics.Color)
     */
    public void draw(Annotation annotation, GC gc, StyledText textWidget,
        int offset, int length, Color color)
    {
      int lineWidth = getSchemaBoxLineWidth();

      if (length == 0) {
        if (gc != null)
          gc.setLineWidth(lineWidth);
        fgIBeamStrategy.draw(annotation, gc, textWidget, offset, length, color);
        // reset the line width for other decoration
        if (gc != null)
          gc.setLineWidth(0);
        return;
      }

      if (gc != null) {
        IDocument document = fSourceViewer.getDocument();
        int boxWidth = textWidget.getClientArea().width - 10;
        int lineHeight = textWidget.getLineHeight(offset);
        int endHeight = 10; // the length of the right vertical line.

        try {
          // the line containing the annotation
          int annLine = document.getLineOfOffset(offset);
          Point left = textWidget.getLocationAtOffset(offset);
          ITypedRegion partition = null;

          try {
            if (document instanceof IDocumentExtension3) {
              IDocumentExtension3 extension3 = (IDocumentExtension3) document;
              partition = extension3.getPartition(IZPartitions.Z_PARTITIONING,
                  offset, false);
            }
            else {
              partition = document.getPartition(offset);
            }

          } catch (BadPartitioningException bpe) {
            partition = null;
          }

          if (partition == null) {
            return;
          }

          String schema_type = partition.getType();

          int start_line = document.getLineOfOffset(partition.getOffset());
          int end_line = document.getLineOfOffset(partition.getOffset()
              + partition.getLength());

          // set the preferred color for the schema box
          gc.setForeground(color);
          gc.setLineWidth(lineWidth);

          if (annLine == start_line) { // tell whether it is the start line
            Point line_end = textWidget.getLocationAtOffset(offset + length);
            if (IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight - 1, left.x, left.y
                  + lineHeight);
              // draw the horizontal line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
              // draw the end vertical line
              gc.drawLine(boxWidth - lineWidth + 1,
                  line_end.y + lineHeight - 1, boxWidth - lineWidth + 1,
                  line_end.y + lineHeight - 1 + endHeight);

            }
            else if (IZPartitions.Z_PARAGRAPH_UNICODE_GENAX
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight / 2, left.x, left.y
                  + lineHeight - 1);
              // draw the first line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight / 2, left_line_end.x,
                  line_end.y + lineHeight / 2);
              gc.drawLine(line_end.x, line_end.y + lineHeight / 2, boxWidth,
                  line_end.y + lineHeight / 2);
              // draw the second line
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
            }
            else if (IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight - 1, left.x, left.y
                  + lineHeight);
              // draw the first line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight / 2, left_line_end.x,
                  line_end.y + lineHeight / 2);
              gc.drawLine(line_end.x, line_end.y + lineHeight / 2, boxWidth,
                  line_end.y + lineHeight / 2);
              // draw the second line
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
              // draw the end vertical line
              gc.drawLine(boxWidth - lineWidth + 1,
                  line_end.y + lineHeight / 2, boxWidth - lineWidth + 1,
                  line_end.y + lineHeight - 1 + endHeight);
            }
          }
          else if (annLine == end_line) { // tell whether it is the end line
            Point line_end = textWidget.getLocationAtOffset(offset + length);
            gc.drawLine(left.x, left.y, left.x, left.y + lineHeight / 2);
            if (IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA
                .equalsIgnoreCase(schema_type)
                || IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH
                    .equalsIgnoreCase(schema_type)) {
              // draw the line from the start of the line using left.x, otherwise use line_end.x
              gc.drawLine(left.x, line_end.y + lineHeight / 2, boxWidth,
                  line_end.y + lineHeight / 2);
              // draw the end vertical line
              gc.drawLine(boxWidth - lineWidth + 1, line_end.y + lineHeight / 2
                  - endHeight, boxWidth - lineWidth + 1, line_end.y
                  + lineHeight / 2);
            }
          }
          else {
            // draw middle lines
            if (ZString.VL.equalsIgnoreCase(String.valueOf(document
                .getChar(offset)))) {
              // draw the predicate line
              Point predicate = textWidget.getLocationAtOffset(offset);
              if (boxWidth > predicate.x)
                gc.drawLine(predicate.x, predicate.y + lineHeight / 2,
                    predicate.x + (boxWidth - predicate.x) / 2, predicate.y
                        + lineHeight / 2);
            }
            // draw the left line
            gc.drawLine(left.x, left.y, left.x, left.y + lineHeight);
          }

          gc.setLineWidth(0);

        } catch (BadLocationException ble) {
          ble.printStackTrace();
          return;
        }
      }
      else {
        // force the AnnotationPainter to redraw the non-text part of the box.
        final int contentLength = textWidget.getCharCount();
        if (offset >= contentLength) {
          textWidget.redraw();
          return;
        }

        int endOfRedrawnLine = textWidget.getLineAtOffset(offset) + 2;
        if (endOfRedrawnLine >= textWidget.getLineCount()) {
          /*
           * Panic code: should not happen, as offset is not the last offset,
           * and there is a delimiter character at offset.
           */
          textWidget.redraw();
          return;
        }

        int endOfRedrawnLineOffset = textWidget
            .getOffsetAtLine(endOfRedrawnLine);
        length = endOfRedrawnLineOffset - offset;

        textWidget.redrawRange(offset, length, true);
      }
    }
  }

  /**
   * Draws a Z schema box around a schema using the second box rending style.
   */
  private final class SecondBoxRenderingStrategy implements IDrawingStrategy
  {
    /*
     * @see org.eclipse.jface.text.source.AnnotationPainter.IDrawingStrategy#draw(org.eclipse.jface.text.source.Annotation, org.eclipse.swt.graphics.GC, org.eclipse.swt.custom.StyledText, int, int, org.eclipse.swt.graphics.Color)
     */
    public void draw(Annotation annotation, GC gc, StyledText textWidget,
        int offset, int length, Color color)
    {
      int lineWidth = getSchemaBoxLineWidth();

      if (length == 0) {
        if (gc != null)
          gc.setLineWidth(lineWidth);
        fgIBeamStrategy.draw(annotation, gc, textWidget, offset, length, color);
        // reset the line width for other decoration
        if (gc != null)
          gc.setLineWidth(0);
        return;
      }

      if (gc != null) {
        IDocument document = fSourceViewer.getDocument();
        int boxWidth = textWidget.getClientArea().width - 10;
        int lineHeight = textWidget.getLineHeight(offset);

        try {
          // the line containing the annotation
          int annLine = document.getLineOfOffset(offset);
          Point left = textWidget.getLocationAtOffset(offset);
          ITypedRegion partition = null;

          try {
            if (document instanceof IDocumentExtension3) {
              IDocumentExtension3 extension3 = (IDocumentExtension3) document;
              partition = extension3.getPartition(IZPartitions.Z_PARTITIONING,
                  offset, false);
            }
            else {
              partition = document.getPartition(offset);
            }

          } catch (BadPartitioningException bpe) {
            partition = null;
          }

          if (partition == null) {
            return;
          }

          String schema_type = partition.getType();

          int start_line = document.getLineOfOffset(partition.getOffset());
          int end_line = document.getLineOfOffset(partition.getOffset()
              + partition.getLength());

          // set the preferred color for the schema box
          gc.setForeground(color);
          gc.setLineWidth(lineWidth);

          if (annLine == start_line) { // tell whether it is the start line
            Point line_end = textWidget.getLocationAtOffset(offset + length);
            if (IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight - 1, left.x, left.y
                  + lineHeight);
              // draw the horizontal line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
            }
            else if (IZPartitions.Z_PARAGRAPH_UNICODE_GENAX
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight / 2, left.x, left.y
                  + lineHeight - 1);
              // draw the first line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight / 2, left_line_end.x,
                  line_end.y + lineHeight / 2);
              gc.drawLine(line_end.x, line_end.y + lineHeight / 2, boxWidth,
                  line_end.y + lineHeight / 2);
              // draw the second line
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
            }
            else if (IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH
                .equalsIgnoreCase(schema_type)) {
              // draw the left line
              gc.drawLine(left.x, left.y + lineHeight - 1, left.x, left.y
                  + lineHeight);
              // draw the horizontal line
              Point left_line_end = textWidget.getLocationAtOffset(offset + 1);
              gc.drawLine(left.x, line_end.y + lineHeight - 1, left_line_end.x,
                  line_end.y + lineHeight - 1);
              gc.drawLine(line_end.x, line_end.y + lineHeight - 1, boxWidth,
                  line_end.y + lineHeight - 1);
            }
          }
          else if (annLine == end_line) { // tell whether it is the end line
            Point line_end = textWidget.getLocationAtOffset(offset + length);
            gc.drawLine(left.x, left.y, left.x, left.y + lineHeight / 2);
            if (IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA
                .equalsIgnoreCase(schema_type)
                || IZPartitions.Z_PARAGRAPH_UNICODE_GENAX
                    .equalsIgnoreCase(schema_type)
                || IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH
                    .equalsIgnoreCase(schema_type))
              // draw the line from the start of the line using left.x, otherwise use line_end.x
              gc.drawLine(left.x, line_end.y + lineHeight / 2, boxWidth,
                  line_end.y + lineHeight / 2);
          }
          else {
            // draw middle lines
            if (ZString.VL.equalsIgnoreCase(String.valueOf(document
                .getChar(offset)))) {
              // draw the predicate line
              Point predicate = textWidget.getLocationAtOffset(offset);
              if (boxWidth > predicate.x)
                gc.drawLine(predicate.x, predicate.y + lineHeight / 2,
                    predicate.x + (boxWidth - predicate.x) / 2, predicate.y
                        + lineHeight / 2);
            }
            // draw the left line
            gc.drawLine(left.x, left.y, left.x, left.y + lineHeight);
          }

          gc.setLineWidth(0);

        } catch (BadLocationException ble) {
          ble.printStackTrace();
          return;
        }
      }
      else {
        // force the AnnotationPainter to redraw the non-text part of the box.
        final int contentLength = textWidget.getCharCount();
        if (offset >= contentLength) {
          textWidget.redraw();
          return;
        }

        int endOfRedrawnLine = textWidget.getLineAtOffset(offset) + 2;
        if (endOfRedrawnLine >= textWidget.getLineCount()) {
          /*
           * Panic code: should not happen, as offset is not the last offset,
           * and there is a delimiter character at offset.
           */
          textWidget.redraw();
          return;
        }

        int endOfRedrawnLineOffset = textWidget
            .getOffsetAtLine(endOfRedrawnLine);
        length = endOfRedrawnLineOffset - offset;

        textWidget.redrawRange(offset, length, true);
      }
    }
  }

  /**
   * Draws an iBeam at the given offset, the length is ignored.
   *
   * @since 3.0
   */
  private static final class IBeamStrategy implements IDrawingStrategy
  {
    /*
     * @see org.eclipse.jface.text.source.AnnotationPainter.IDrawingStrategy#draw(org.eclipse.jface.text.source.Annotation, org.eclipse.swt.graphics.GC, org.eclipse.swt.custom.StyledText, int, int, org.eclipse.swt.graphics.Color)
     */
    public void draw(Annotation annotation, GC gc, StyledText textWidget,
        int offset, int length, Color color)
    {
      if (gc != null) {

        Point left = textWidget.getLocationAtOffset(offset);
        int x1 = left.x;
        int y1 = left.y;

        gc.setForeground(color);
        gc.drawLine(x1, y1, x1, left.y + textWidget.getLineHeight(offset) - 1);

      }
      else {
        /*
         * The length for IBeam's is always 0, which causes no redraw to occur in
         * StyledText#redraw(int, int, boolean). We try to normally redraw at length of one,
         * and up to the line start of the next line if offset is at the end of line. If at
         * the end of the document, we redraw the entire document as the offset is behind
         * any content.
         */
        final int contentLength = textWidget.getCharCount();
        if (offset >= contentLength) {
          textWidget.redraw();
          return;
        }

        char ch = textWidget.getTextRange(offset, 1).charAt(0);
        if (ch == '\r' || ch == '\n') {
          // at the end of a line, redraw up to the next line start
          int nextLine = textWidget.getLineAtOffset(offset) + 1;
          if (nextLine >= textWidget.getLineCount()) {
            /*
             * Panic code: should not happen, as offset is not the last offset,
             * and there is a delimiter character at offset.
             */
            textWidget.redraw();
            return;
          }

          int nextLineOffset = textWidget.getOffsetAtLine(nextLine);
          length = nextLineOffset - offset;
        }
        else {
          length = 1;
        }

        textWidget.redrawRange(offset, length, true);
      }
    }
  }

  /**
   * The null drawing strategy.
   * @since 3.0
   */
  private static IDrawingStrategy fgNullStrategy = new AnnotationPainter.NullStrategy();

  /**
   * The iBeam drawing strategy.
   * @since 3.0
   */
  private static IDrawingStrategy fgIBeamStrategy = new IBeamStrategy();

  /**
   * The schema box drawing strategy.
   */
  private IDrawingStrategy fgSchemaBoxStyle1Strategy = new FirstBoxRenderingStrategy();

  /**
   * The schema box drawing strategy.
   */
  private IDrawingStrategy fgSchemaBoxStyle2Strategy = new SecondBoxRenderingStrategy();

  /** The viewer */
  private ISourceViewer fSourceViewer;

  /** The viewer's overview ruler */
  private IOverviewRuler fOverviewRuler;

  /** The annotation access */
  private IAnnotationAccess fAnnotationAccess;

  /** The shared color manager */
  private ISharedTextColors fSharedTextColors;

  /** The fEditor's annotation painter */
  private AnnotationPainter fAnnotationPainter;

  /** Map with annotation type preference per annotation type */
  private Map fAnnotationTypeKeyMap = new HashMap();

  /** Preference key for the schema box painter line width */
  private String fSchemaBoxLineWidthKey;

  /** Preference value for the schema box painter line width */
  private int fSchemaBoxLineWidth = 0;

  /** The property change listener */
  private IPropertyChangeListener fPropertyChangeListener;

  /** The preference store */
  private IPreferenceStore fPreferenceStore;

  /**
   * Creates a new decoration support for the given viewer.
   *
   * @param sourceViewer the source viewer
   * @param overviewRuler the viewer's overview ruler
   * @param annotationAccess the annotation access
   * @param sharedTextColors the shared text color manager
   */
  public ZSpecDecorationSupport(ISourceViewer sourceViewer,
      IOverviewRuler overviewRuler, IAnnotationAccess annotationAccess,
      ISharedTextColors sharedTextColors)
  {
    fSourceViewer = sourceViewer;
    fOverviewRuler = overviewRuler;
    fAnnotationAccess = annotationAccess;
    fSharedTextColors = sharedTextColors;
  }

  /**
   * Installs this decoration support on the given preference store. It assumes
   * that this support has completely been configured.
   *
   * @param store the preference store
   */
  public void install(IPreferenceStore store)
  {
    fPreferenceStore = store;
    if (fPreferenceStore != null) {
      fPropertyChangeListener = new IPropertyChangeListener()
      {
        public void propertyChange(PropertyChangeEvent event)
        {
          handlePreferenceStoreChanged(event);
        }
      };
      fPreferenceStore.addPropertyChangeListener(fPropertyChangeListener);
    }

    updateTextDecorations();
    updateOverviewDecorations();
  }

  /**
   * Updates the text decorations for all configured annotation types.
   */
  private void updateTextDecorations()
  {
    StyledText widget = fSourceViewer.getTextWidget();
    if (widget == null || widget.isDisposed())
      return;

    Iterator e = fAnnotationTypeKeyMap.keySet().iterator();
    while (e.hasNext()) {
      Object type = e.next();
      Object style = getAnnotationDecorationType(type);
      if (style != AnnotationPreference.STYLE_NONE)
        showAnnotations(type, false, false);
      else
        hideAnnotations(type, false, false);
      if (areAnnotationsHighlighted(type))
        showAnnotations(type, true, false);
      else
        hideAnnotations(type, true, false);

    }
    updateAnnotationPainter();
  }

  /**
   * Returns the annotation decoration style used for the show in text preference for
   * a given annotation type.
   *
   * @param annotationType the annotation type being looked up
   * @return the decoration style for <code>type</code>
   * @since 3.0
   */
  private Object getAnnotationDecorationType(Object annotationType)
  {
    if (areAnnotationsShown(annotationType) && fPreferenceStore != null) {
      AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
          .get(annotationType);
      if (info != null) {
        String key = info.getTextStylePreferenceKey();
        if (key != null)
          return fPreferenceStore.getString(key);
      }
    }

    return AnnotationPreference.STYLE_NONE;
  }

  /**
   * Updates the annotation overview for all configured annotation types.
   */
  public void updateOverviewDecorations()
  {
    if (fOverviewRuler != null) {
      Iterator e = fAnnotationTypeKeyMap.keySet().iterator();
      while (e.hasNext()) {
        Object type = e.next();
        if (isAnnotationOverviewShown(type))
          showAnnotationOverview(type, false);
        else
          hideAnnotationOverview(type, false);
      }
      fOverviewRuler.update();
    }
  }

  /**
   * Uninstalls this support from the preference store it has previously been
   * installed on. If there is no such preference store, this call is without
   * effect.
   */
  public void uninstall()
  {
    if (fPreferenceStore != null) {
      fPreferenceStore.removePropertyChangeListener(fPropertyChangeListener);
      fPropertyChangeListener = null;
      fPreferenceStore = null;
    }
  }

  /**
   * Disposes this decoration support. Internally calls
   * <code>uninstall</code>.
   */
  public void dispose()
  {
    uninstall();
    updateTextDecorations();
    updateOverviewDecorations();

    fOverviewRuler = null;

    // Painters got disposed in updateTextDecorations() or by the PaintManager
    fAnnotationPainter = null;

    if (fAnnotationTypeKeyMap != null) {
      fAnnotationTypeKeyMap.clear();
      fAnnotationTypeKeyMap = null;
    }
  }

  /**
   * Sets the preference keys for the annotation painter.
   *
   * @param type the annotation type
   * @param colorKey the preference key for the color
   * @param editorKey the preference key for the presentation in the text area
   * @param overviewRulerKey the preference key for the presentation in the overview  ruler
   * @param layer the layer
   */
  public void setAnnotationPainterPreferenceKeys(Object type, String colorKey,
      String editorKey, String overviewRulerKey, int layer)
  {
    AnnotationPreference info = new AnnotationPreference(type, colorKey,
        editorKey, overviewRulerKey, layer);
    fAnnotationTypeKeyMap.put(type, info);
  }

  /**
   * Sets the preference info for the annotation painter.
   * @param info the preference info to be set
   */
  public void setAnnotationPreference(AnnotationPreference info)
  {
    fAnnotationTypeKeyMap.put(info.getAnnotationType(), info);
  }

  private int getSchemaBoxLineWidth()
  {
    if (fPreferenceStore != null) {
      return fPreferenceStore
          .getInt(ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_WIDTH);
    }
    return 0;
  }

  /**
   * Returns the annotation preference for the given key.
   *
   * @param preferenceKey the preference key string
   * @return the annotation preference
   */
  private AnnotationPreference getAnnotationPreferenceInfo(String preferenceKey)
  {
    Iterator e = fAnnotationTypeKeyMap.values().iterator();
    while (e.hasNext()) {
      AnnotationPreference info = (AnnotationPreference) e.next();
      if (info != null && info.isPreferenceKey(preferenceKey))
        return info;
    }
    return null;
  }

  /*
   * @see AbstractTextEditor#handlePreferenceStoreChanged(PropertyChangeEvent)
   */
  protected void handlePreferenceStoreChanged(PropertyChangeEvent event)
  {
    String p = event.getProperty();

    if (ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_WIDTH.equals(p)) {
      if (fAnnotationPainter != null)
        fAnnotationPainter.paint(IPainter.CONFIGURATION);
      return;
    }

    AnnotationPreference info = getAnnotationPreferenceInfo(p);
    if (info != null) {
      if (info.getColorPreferenceKey().equals(p)) {
        Color color = getColor(info.getColorPreferenceKey());
        if (fAnnotationPainter != null) {
          fAnnotationPainter.setAnnotationTypeColor(info.getAnnotationType(),
              color);
          fAnnotationPainter.paint(IPainter.CONFIGURATION);
        }
        setAnnotationOverviewColor(info.getAnnotationType(), color);
        return;
      }

      if (info.getTextPreferenceKey().equals(p)
          || info.getTextStylePreferenceKey() != null
          && info.getTextStylePreferenceKey().equals(p)) {
        Object style = getAnnotationDecorationType(info.getAnnotationType());
        if (AnnotationPreference.STYLE_NONE != style)
          showAnnotations(info.getAnnotationType(), false, true);
        else
          hideAnnotations(info.getAnnotationType(), false, true);
        return;
      }

      if (info.getHighlightPreferenceKey() != null
          && info.getHighlightPreferenceKey().equals(p)) {
        if (areAnnotationsHighlighted(info.getAnnotationType()))
          showAnnotations(info.getAnnotationType(), true, true);
        else
          hideAnnotations(info.getAnnotationType(), true, true);
        return;
      }

      Object style = getAnnotationDecorationType(info.getAnnotationType());
      if (style != AnnotationPreference.STYLE_NONE)
        showAnnotations(info.getAnnotationType(), false, false);
      else
        hideAnnotations(info.getAnnotationType(), false, false);

      if (info.getOverviewRulerPreferenceKey().equals(p)) {
        if (isAnnotationOverviewShown(info.getAnnotationType()))
          showAnnotationOverview(info.getAnnotationType(), true);
        else
          hideAnnotationOverview(info.getAnnotationType(), true);
        return;
      }
    }
  }

  /**
   * Returns the shared color for the given key.
   *
   * @param key the color key string
   * @return the shared color for the given key
   */
  private Color getColor(String key)
  {
    if (fPreferenceStore != null) {
      RGB rgb = PreferenceConverter.getColor(fPreferenceStore, key);
      return getColor(rgb);
    }
    return null;
  }

  /**
   * Returns the shared color for the given RGB.
   *
   * @param rgb the RGB
   * @return the shared color for the given RGB
   */
  private Color getColor(RGB rgb)
  {
    return fSharedTextColors.getColor(rgb);
  }

  /**
   * Returns the color of the given annotation type.
   *
   * @param annotationType the annotation type
   * @return the color of the annotation type
   */
  private Color getAnnotationTypeColor(Object annotationType)
  {
    AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
        .get(annotationType);
    if (info != null)
      return getColor(info.getColorPreferenceKey());
    return null;
  }

  /**
   * Returns the layer of the given annotation type.
   *
   * @param annotationType the annotation type
   * @return the layer
   */
  private int getAnnotationTypeLayer(Object annotationType)
  {
    AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
        .get(annotationType);
    if (info != null)
      return info.getPresentationLayer();
    return 0;
  }

  /**
   * Enables annotations in the source viewer for the given annotation type.
   *
   * @param annotationType the annotation type
   * @param highlighting <code>true</code> if highlighting <code>false</code> if painting squiggles
   * @param updatePainter if <code>true</code> update the annotation painter
   * @since 3.0
   */
  private void showAnnotations(Object annotationType, boolean highlighting,
      boolean updatePainter)
  {
    if (fSourceViewer instanceof ITextViewerExtension2) {
      if (fAnnotationPainter == null) {
        fAnnotationPainter = createAnnotationPainter();
        if (fSourceViewer instanceof ITextViewerExtension4) {
          ((ITextViewerExtension4) fSourceViewer)
              .addTextPresentationListener(fAnnotationPainter);
        }
        ITextViewerExtension2 extension = (ITextViewerExtension2) fSourceViewer;
        extension.addPainter(fAnnotationPainter);
      }
      fAnnotationPainter.setAnnotationTypeColor(annotationType,
          getAnnotationTypeColor(annotationType));
      if (highlighting)
        fAnnotationPainter.addHighlightAnnotationType(annotationType);
      else
        fAnnotationPainter.addAnnotationType(annotationType,
            getAnnotationDecorationType(annotationType));

      if (updatePainter)
        updateAnnotationPainter();
    }
  }

  /**
   * Creates and configures the annotation painter and configures.
   * @return an annotation painter
   * @since 3.0
   */
  protected AnnotationPainter createAnnotationPainter()
  {
    AnnotationPainter painter = new AnnotationPainter(fSourceViewer,
        fAnnotationAccess);

    // TODO add extension point for drawing strategies?
    painter.addDrawingStrategy(AnnotationPreference.STYLE_NONE, fgNullStrategy);
    painter.addDrawingStrategy(AnnotationPreference.STYLE_IBEAM,
        fgIBeamStrategy);
    painter.addDrawingStrategy(
        ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_1,
        fgSchemaBoxStyle1Strategy);
    painter.addDrawingStrategy(
        ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_2,
        fgSchemaBoxStyle2Strategy);

    return painter;
  }

  /**
   * Updates the annotation painter.
   * @since 3.0
   */
  private void updateAnnotationPainter()
  {
    if (fAnnotationPainter == null)
      return;

    fAnnotationPainter.paint(IPainter.CONFIGURATION);
    if (!fAnnotationPainter.isPaintingAnnotations()) {
      if (fSourceViewer instanceof ITextViewerExtension2) {
        ITextViewerExtension2 extension = (ITextViewerExtension2) fSourceViewer;
        extension.removePainter(fAnnotationPainter);
      }
      if (fSourceViewer instanceof ITextViewerExtension4)
        ((ITextViewerExtension4) fSourceViewer)
            .removeTextPresentationListener(fAnnotationPainter);

      fAnnotationPainter.deactivate(true);
      fAnnotationPainter.dispose();
      fAnnotationPainter = null;
    }
  }

  /**
   * Hides annotations in the source viewer for the given annotation type.
   *
   * @param annotationType the annotation type
   * @param highlighting <code>true</code> if highlighting <code>false</code> if painting squiggles
   * @param updatePainter if <code>true</code> update the annotation painter
   * @since 3.0
   */
  private void hideAnnotations(Object annotationType, boolean highlighting,
      boolean updatePainter)
  {
    if (fAnnotationPainter != null) {
      if (highlighting)
        fAnnotationPainter.removeHighlightAnnotationType(annotationType);
      else
        fAnnotationPainter.removeAnnotationType(annotationType);

      if (updatePainter) {
        updateAnnotationPainter();
      }
    }
  }

  /**
   * Tells whether annotations are shown in the source viewer for the given type.
   *
   * @param annotationType the annotation type
   * @return <code>true</code> if the annotations are shown
   */
  private boolean areAnnotationsShown(Object annotationType)
  {
    if (fPreferenceStore != null) {
      AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
          .get(annotationType);
      if (info != null) {
        String key = info.getTextPreferenceKey();
        return key != null && fPreferenceStore.getBoolean(key);
      }
    }

    return false;
  }

  /**
   * Tells whether annotations are highlighted in the source viewer for the given type.
   *
   * @param annotationType the annotation type
   * @return <code>true</code> if the annotations are highlighted
   * @since 3.0
   */
  private boolean areAnnotationsHighlighted(Object annotationType)
  {
    if (fPreferenceStore != null) {
      AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
          .get(annotationType);
      if (info != null)
        return info.getHighlightPreferenceKey() != null
            && fPreferenceStore.getBoolean(info.getHighlightPreferenceKey());
    }
    return false;
  }

  /**
   * Tells whether annotation overview is enabled for the given type.
   *
   * @param annotationType the annotation type
   * @return <code>true</code> if the annotation overview is shown
   */
  private boolean isAnnotationOverviewShown(Object annotationType)
  {
    if (fPreferenceStore != null && fOverviewRuler != null) {
      AnnotationPreference info = (AnnotationPreference) fAnnotationTypeKeyMap
          .get(annotationType);
      if (info != null)
        return fPreferenceStore
            .getBoolean(info.getOverviewRulerPreferenceKey());
    }
    return false;
  }

  /**
   * Enable annotation overview for the given annotation type.
   *
   * @param annotationType the annotation type
   * @param update <code>true</code> if the overview should be updated
   */
  private void showAnnotationOverview(Object annotationType, boolean update)
  {
    if (fOverviewRuler != null) {
      fOverviewRuler.setAnnotationTypeColor(annotationType,
          getAnnotationTypeColor(annotationType));
      fOverviewRuler.setAnnotationTypeLayer(annotationType,
          getAnnotationTypeLayer(annotationType));
      fOverviewRuler.addAnnotationType(annotationType);
      if (update)
        fOverviewRuler.update();
    }
  }

  /**
   * Hides the annotation overview for the given type.
   * @param annotationType the annotation type
   * @param update <code>true</code> if the overview should be updated
   */
  private void hideAnnotationOverview(Object annotationType, boolean update)
  {
    if (fOverviewRuler != null) {
      fOverviewRuler.removeAnnotationType(annotationType);
      if (update)
        fOverviewRuler.update();
    }
  }

  /**
   * Hides the annotation overview.
   */
  public void hideAnnotationOverview()
  {
    if (fOverviewRuler != null) {
      Iterator e = fAnnotationTypeKeyMap.keySet().iterator();
      while (e.hasNext())
        fOverviewRuler.removeAnnotationType(e.next());
      fOverviewRuler.update();
    }
  }

  /**
   * Sets the annotation overview color for the given annotation type.
   *
   * @param annotationType the annotation type
   * @param color the color
   */
  private void setAnnotationOverviewColor(Object annotationType, Color color)
  {
    if (fOverviewRuler != null) {
      fOverviewRuler.setAnnotationTypeColor(annotationType, color);
      fOverviewRuler.update();
    }
  }
}

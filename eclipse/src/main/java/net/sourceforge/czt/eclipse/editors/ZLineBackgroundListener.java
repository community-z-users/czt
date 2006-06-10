
package net.sourceforge.czt.eclipse.editors;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.IZColorConstants;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.swt.custom.LineBackgroundEvent;
import org.eclipse.swt.custom.LineBackgroundListener;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 */
public class ZLineBackgroundListener implements LineBackgroundListener
{

  private ITextEditor fEditor;

  public ZLineBackgroundListener(ITextEditor editor)
  {
    super();
    this.fEditor = editor;
  }

  public void lineGetBackground(LineBackgroundEvent event)
  {
    StyledText text = (StyledText) event.getSource();

    IDocument document = this.fEditor.getDocumentProvider().getDocument(
        this.fEditor.getEditorInput());
    ITypedRegion[] partitions = CZTPlugin.getDefault().getCZTTextTools().getPartitions(document, IZPartitions.Z_PARTITIONING);

    //		Vector styles = new Vector();

    Color bgColor = CZTPlugin.getDefault().getCZTColorManager().getColor(
        IZColorConstants.BACKGROUND);
    for (int i = 0; i < partitions.length; i++) {
      ITypedRegion partition = partitions[i];
      if (partition.getType().startsWith("__z_paragraph_")) {

        StyleRange[] styles = text.getStyleRanges(partition.getOffset(),
            partition.getLength());
        // need modifications

        for (StyleRange style : styles) {

          style.background = bgColor;
        }
        text.setStyleRanges(styles);

        //				System.out.println("From " + partition.getOffset() + " to " + partition.getLength() + 
        //						" type: " + partition.getType());
      }
    }

    text.redraw();
    //text.setLineBackground(5, 2, CZTPlugin.getDefault().getCZTColorManager().getColor(IZColorConstants.BACKGROUND));

  }

}

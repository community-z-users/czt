/**
 * Created on 2005-10-19
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;

/**
 * @author Chengdong Xu
 */
public class ZDocumentSetupParticipant_Latex
    implements
      IDocumentSetupParticipant
{

  /**
   */
  public ZDocumentSetupParticipant_Latex()
  {
  }

  /* (non-Javadoc)
   * @see org.eclipse.core.filebuffers.IDocumentSetupParticipant#setup(org.eclipse.jface.text.IDocument)
   */
  public void setup(IDocument document)
  {
//    System.out.println("ZDocumentSetupParticipant_Latex.setup starts");
    if (document instanceof IDocumentExtension3) {
      IDocumentExtension3 extension3 = (IDocumentExtension3) document;
      IDocumentPartitioner partitioner = new FastPartitioner(CztUIPlugin
          .getDefault().getZPartitionScanner(IZFileType.FILETYPE_LATEX),
          ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX);
      extension3.setDocumentPartitioner(IZPartitions.Z_PARTITIONING, partitioner);
      partitioner.connect(document);
    }
  }
}
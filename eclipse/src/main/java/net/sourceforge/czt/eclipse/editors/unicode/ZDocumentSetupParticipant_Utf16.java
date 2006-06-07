
package net.sourceforge.czt.eclipse.editors.unicode;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;

/** 
 * @author Chengdong Xu
 */
public class ZDocumentSetupParticipant_Utf16
    implements
      IDocumentSetupParticipant
{

  /**
   */
  public ZDocumentSetupParticipant_Utf16()
  {
  }

  /* (non-Javadoc)
   * @see org.eclipse.core.filebuffers.IDocumentSetupParticipant#setup(org.eclipse.jface.text.IDocument)
   */
  public void setup(IDocument document)
  {
    if (document instanceof IDocumentExtension3) {
      IDocumentExtension3 extension3 = (IDocumentExtension3) document;
      IDocumentPartitioner partitioner = new FastPartitioner(CZTPlugin
          .getDefault().getZPartitionScanner(IZFileType.FILETYPE_UTF16),
          ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE);
      extension3.setDocumentPartitioner(CZTPlugin.Z_PARTITIONING, partitioner);
      partitioner.connect(document);
    }
  }
}

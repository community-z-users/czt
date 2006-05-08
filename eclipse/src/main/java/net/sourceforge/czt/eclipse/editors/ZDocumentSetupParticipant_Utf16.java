package net.sourceforge.czt.eclipse.editors;

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
public class ZDocumentSetupParticipant_Utf16 implements
		IDocumentSetupParticipant {

	/**
	 */
	public ZDocumentSetupParticipant_Utf16() {
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.filebuffers.IDocumentSetupParticipant#setup(org.eclipse.jface.text.IDocument)
	 */
	public void setup(IDocument document) {
		if (document instanceof IDocumentExtension3) {
			IDocumentExtension3 extension3= (IDocumentExtension3) document;
			IDocumentPartitioner partitioner= new FastPartitioner(
					CZTPlugin.getDefault().getZedPartitionScanner(
							IZFileType.FILETYPE_UTF16),
							ZPartitionScanner.Z_PARTITION_TYPES_UTF16);
			extension3.setDocumentPartitioner(
					CZTPlugin.Z_PARTITIONING, partitioner);
			partitioner.connect(document);
		}
	}
}

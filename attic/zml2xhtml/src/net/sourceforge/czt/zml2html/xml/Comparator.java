package net.sourceforge.czt.zml2html.xml;

import org.w3c.dom.Document;

/**
 * Comparator instances compare two SmartDocuments 
 * and report on equality based on the documents
 * and their particular matching algorithm.
 *
 */
public interface Comparator
{
    public boolean isEqual(Document doc1, Document doc2);

    public ActionReport getActionReport();
}

package net.sourceforge.czt.zml2html.testing;

import java.util.Hashtable;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import java.util.List;
import java.util.ArrayList;
import org.apache.xpath.*;
import org.w3c.dom.Element;
import org.w3c.dom.Document;
import org.w3c.dom.DOMException;
import java.util.Hashtable;
import java.util.Enumeration;
import java.util.Iterator;

public class CommentHashtable extends Hashtable
{
    // ids start at 1
    private int commentCount;

    private boolean modified;

    private Comment cachedLatestApprovalComment = null;
    private Comment cachedLatestDisapprovalComment = null;

    public CommentHashtable()
    {
    }

    public CommentHashtable(ZMLDocument zmlDoc)
    {
	commentCount = 0;
	modified = false;
	load(zmlDoc);
    }

    private Comment getLatestTypedComment(int type)
    {
        Enumeration commentEnum = elements();
	Comment latestTypedComment = null;
	while (commentEnum.hasMoreElements()) {
	    Comment comment = (Comment)commentEnum.nextElement();
	    if (comment.type == type) {
		if (latestTypedComment == null || comment.id > latestTypedComment.id) {
		    latestTypedComment = comment;
		}
	    }
	}
	return latestTypedComment;
    }

    /**
     * Returns the comment with <code>type=Comment.TYPE_APPROVAL</code>
     * that has the highest id, or <code>null</code> if none exists.
     */
    public Comment getLatestApprovalComment()
    {    
	if (!isModified() && cachedLatestApprovalComment != null)
	    return cachedLatestApprovalComment;
           
	cachedLatestApprovalComment  = getLatestTypedComment(Comment.TYPE_APPROVAL);
	return cachedLatestApprovalComment;
    }

    /**
     * Returns the comment with <code>type=Comment.TYPE_DISAPPROVAL</code>
     * that has the highest id, or <code>null</code> if none exists.
     */
    public Comment getLatestDisapprovalComment()
    {
	if (!isModified() && cachedLatestDisapprovalComment != null)
	    return cachedLatestDisapprovalComment;
           
	cachedLatestDisapprovalComment  = getLatestTypedComment(Comment.TYPE_DISAPPROVAL);
	return cachedLatestDisapprovalComment;
    }

    public boolean isApproved()
    {
	Comment latestApprovalComment = getLatestApprovalComment();
	Comment latestDisapprovalComment = getLatestDisapprovalComment();

	if (latestApprovalComment == null ||
	    latestDisapprovalComment != null && latestApprovalComment.id < latestDisapprovalComment.id)
	    return false;
	return true;
    }

    public boolean isDisapproved()
    {
	Comment latestApprovalComment = getLatestApprovalComment();
	Comment latestDisapprovalComment = getLatestDisapprovalComment();

	if (latestDisapprovalComment == null || isApproved())
	    return false;
	return true;	
    }

    public boolean isModified()
    {
	return modified;
    }

    private void load(ZMLDocument zmlDoc)
    {
	List matches;

	try {
	    // find comment list. there should be at most one.
	    matches = zmlDoc.getNodesByXPath("Z:Spec/Z:Anns/zml2html:comment-list[1]/zml2html:comment");

	    Iterator iter = matches.iterator();

	    while (iter.hasNext()) {
		Element commentElement = (Element)iter.next();

		String id = null;
		String author = null;
		String text = null;
		String type = null;
		String date = null;

		NodeList nl = commentElement.getChildNodes();

		for (int i = 0; i < nl.getLength(); i++) {
		    Node commentChildNode = nl.item(i);
		    if (commentChildNode.getNodeType() == Node.ELEMENT_NODE) {
			Element commentChildElement = (Element)commentChildNode;
			String name = commentChildElement.getLocalName();
			String value = ZMLDocument.getElementText(commentChildElement);
			if (name.equals("id")) {
			    id = value;
			} else if (name.equals("author")) {
			    author = value;
			} else if (name.equals("text")) {
			    text = value;
			} else if (name.equals("type")) {
			    type = value;
			} else if (name.equals("date")) {
			    date = value;
			}
		    }
		}

		Comment comment = new Comment(author, text, type);
		int intId = Integer.parseInt(id);
		comment.setId(intId);
		if (commentCount < intId)
		    commentCount = intId;
		add(comment);
	    }

	} catch (javax.xml.transform.TransformerException te) {
	    te.printStackTrace();
	}
    }

    public Element getAsElement(Document dom)
    {
	Element annsElement = null;
	try {	    
	    annsElement = dom.createElementNS(ZMLDocument.ZML_NAMESPACE_URI, "Anns");
	    Element commentListElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:comment-list");
	    annsElement.appendChild(commentListElement);
	    Enumeration commentsEnum = elements();
	    while (commentsEnum.hasMoreElements()) {
		Comment comment = (Comment)commentsEnum.nextElement();
		Element commentElement = comment.getAsElement(dom);
		commentListElement.appendChild(commentElement);		
	    }
	} catch (DOMException de) {
	    de.printStackTrace();
	}
	return annsElement;
    }

    public void delete(int id)
    {
	modified = true;
	remove(new Integer(id));
    }

    public int add(Comment comment) 
    {
	int id;
	if (comment.id == -1) {
	    id = ++commentCount;
	    comment.id = id;
	}
	else
	    id = comment.id;

	put(new Integer(id), comment);

	modified = true;

	return id;
    }

}




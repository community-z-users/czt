package net.sourceforge.czt.zml2html.testing;

import java.util.Date;

import org.w3c.dom.Node;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Text;
import org.w3c.dom.DOMException;

/**
 * A comment associated with a <code>TestCase</code>.
 *
 * <code>Comment</code>s are typed to be either <code>TYPE_APPROVED</code>,
 * <code>TYPE_DISAPPROVED</code> or <code>TYPE_COMMENT</code>.
 */
public class Comment
{
    public static final int TYPE_APPROVAL = 0;
    public static final int TYPE_DISAPPROVAL = 1;
    public static final int TYPE_COMMENT = 2;
    public static final int TYPE_INVALID_COMMENT_TYPE = 3;

    public static final String APPROVAL_DESC = "approval";
    public static final String DISAPPROVAL_DESC = "disapproval";
    public static final String COMMENT_DESC = "comment";

    public Date date;
    public String author = "system";
    public String text = "";
    public int id;
    public int type;

    public Comment(String author, String text, String typeDesc)
    {
	this.id = -1;
	this.author = author;
	this.text = text;
	this.type = getType(typeDesc);
    }

    public void setId(int id)
    {
	this.id = id;
    }

    public boolean isApproval()
    {
	return (type == TYPE_APPROVAL);
    }

    public boolean isDisapproval()
    {
	return (type == TYPE_DISAPPROVAL);
    }

    public boolean isComment()
    {
	return (type == TYPE_COMMENT);
    }
    
    private int getType(String typeDesc)	
    {
	if (typeDesc.equals(APPROVAL_DESC)) {
	    return TYPE_APPROVAL;
	} else if (typeDesc.equals(DISAPPROVAL_DESC)) {
	    return TYPE_DISAPPROVAL;
	} else if (typeDesc.equals(COMMENT_DESC)) {
	    return TYPE_COMMENT;
	} else
	    return TYPE_INVALID_COMMENT_TYPE;
    }

    private String getTypeDesc(int type)
    {
	String typeDesc = null;
	switch (type) {
	case TYPE_APPROVAL:
	    typeDesc = APPROVAL_DESC; break;
	case TYPE_DISAPPROVAL:
	    typeDesc = DISAPPROVAL_DESC; break;
	case TYPE_COMMENT:
	    typeDesc = COMMENT_DESC; break;
	}
	return typeDesc;
    }

    public String toString()
    {
	return "[id:"+id+" author:"+author+" type:"+type+"]";
    }

    public Element getAsElement(Document dom)
    {
	Element commentElement = null;
	try {
	    commentElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:comment");
	    Element idElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:id");
	    Element authorElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:author");
	    Element typeElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:type");
	    Element textElement = dom.createElementNS(ZMLDocument.ZML_ZML2HTML_TESTING_NAMESPACE_URI, "zml2html:text");
	    Text idText = dom.createTextNode(""+id);
	    Text authorText = dom.createTextNode(author);
	    String typeTextValue = getTypeDesc(type);
	    Text typeText = dom.createTextNode(typeTextValue);
	    Text textText = dom.createTextNode(text);
	    idElement.appendChild(idText);
	    authorElement.appendChild(authorText);
	    typeElement.appendChild(typeText);
	    textElement.appendChild(textText);
	    commentElement.appendChild(idElement);
	    commentElement.appendChild(authorElement);
	    commentElement.appendChild(typeElement);
	    commentElement.appendChild(textElement);
	} catch (DOMException de) {
	    de.printStackTrace();
	}
	return commentElement;
    }

    /**
     * Returns a new Element Node owned by the given {@link org.w3c.dom.Document Document} that
     * describes the Comment.
     * 
     * @param doc The Document in which the created node will be inserted
     *
     * @return An element node describing the comment
     *
     */
    public Node getCommentAsNode(Document doc) {
	Element idNode = doc.createElement("zml2html:id");
	Element commentNode = doc.createElement("zml2html:comment");	
	Element authorNode = doc.createElement("zml2html:author");
	Element textNode = doc.createElement("zml2html:text");
	
	Text authorText = doc.createTextNode(author);
	Text textText = doc.createTextNode(text);
	
	authorNode.appendChild(authorText);
	textNode.appendChild(textText);

	commentNode.appendChild(authorNode);
	commentNode.appendChild(textNode);

	return commentNode;
    }
}




package net.sourceforge.czt.zml2html.xml;

/*** Import list needs to be cleaned up,
     along with the rest of this class
***/
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.ParserConfigurationException;

import java.io.IOException;
import java.io.File;

import java.util.Stack;
import java.util.Iterator;


/**
 * Decides on the equality of two Nodes based on
 * a generic equality algorithm.
 */
public class EqualityComparator implements Comparator
{
    public static int indent = 0;
    public static Stack location = new Stack();

    /**
     *
     */
    public EqualityComparator() {}

    public boolean isEqual(Document doc1, Document doc2)
    {
	return isEqualNode(doc1, doc2);
    }

    public ActionReport getActionReport()
    {
	return null;
    }

   public static boolean isEqualNode(Node n1, Node n2) {
	
	String testname = n1.getNodeName();
	String nodeTypeName = getNodeTypeName(n1);
	pushLocation(testname);

	println("==>Entering ["+getLocation()+"] ("+nodeTypeName+")");

	try {

	    if (!isIntEqual(n1.getNodeType(), n2.getNodeType(), "NodeType equality"))
		return false;
	    
	    if (!isNullOrEqual(n1.getNodeName(), n2.getNodeName(), "NodeName equality"))
		return false;
	    
	    if (!isNullOrEqual(n1.getLocalName(), n2.getLocalName(), "Local Name equality"))
		return false;
	    
	    if (!isNullOrEqual(n1.getNamespaceURI(), n2.getNamespaceURI(), "NamespaceURI equality"))
		return false;
	    
	    if (!isNullOrEqual(n1.getPrefix(), n2.getPrefix(), "Prefix equality"))
		return false;
	    
	    if (!isNullOrEqual(n1.getNodeValue(), n2.getNodeValue(), "NodeValue equality"))
		return false;

	    NamedNodeMap n1AttMap = n1.getAttributes();
	    NamedNodeMap n2AttMap = n2.getAttributes();
	    if (!isEqualNamedNodeMap(n1AttMap, n2AttMap, testname))
		return false;
	    
	    NodeList n1ChildNodes = n1.getChildNodes();
	    NodeList n2ChildNodes = n2.getChildNodes();
	    if (!isEqualNodeList(n1ChildNodes, n2ChildNodes, testname))
		return false;
	} finally {
	    popLocation();
	}

	return true;
    }


    private static boolean isNullOrEqual(String o1, String o2, String testname) {
      if (o1 != null)
	  o1 = o1.trim();
      if (o2 != null)
	  o2 = o2.trim();

      if ((o1 == null && o2 == null) | (o1 != null && o1.equals(o2))) {
	  println("passed "+testname+" ("+o1+")");
	  return true;
      }
      println("FAILED "+testname+" ("+o1+"<=>"+o2+")");
      return false;
    }

    private static boolean isIntEqual(int i1, int i2, String testname) {
	if (i1==i2) {
	    println("passed "+testname+" ("+i1+"<=>"+i2+")");	    
	    return true;
	}
	println("faield "+testname+" ("+i1+"<=>"+i2+")");	    
	return false;       
    }

    private static boolean isEqualNodeList(NodeList n1, NodeList n2, String testname) {

	print("Comparing Child Nodes: " + getLocation());
	if (n2 != null)
	    //	    System.out.print(" ("+n2.getLength()+" nodes to compare to)");
	    //	System.out.println();
	    
	if (n1 == null && n2 == null) {
	    passed(testname, "childlists are both null");
	    return true;
	}

	if (n1.getLength() == 0 && n2.getLength() == 0) {
	    passed(testname, "childlists are both of length 0");
	    return true;
	}
	
	if (n1.getLength() != n2.getLength()) {
	    failed(testname, "getLength() not the same for list1 and list2");
	    return false;
	}
	for (int i = 0; i < n1.getLength(); i++) {
	    Node curNode = n1.item(i);
	    boolean foundMatch = false;
	    String nodeToMatchLocation = getLocation()+"/"+curNode.getNodeName();
	    println("----- trying to match child node '"+nodeToMatchLocation+"' -----");
	    Node compNode = n2.item(i);
	    if (isEqualNode(curNode, compNode))
		foundMatch = true;

	    /*
	    for (int j = 0; j < n2.getLength(); j++) {		
		Node compNode = n2.item(j);
		if (isEqualNode(curNode, compNode)) {
		    foundMatch = true;
		    break;
		}
	    }
	    */
	    println("----- done trying to match child node '"+nodeToMatchLocation+"' -----");
	    if (!foundMatch) {
	        failed(testname, "no matching element found for child named "+n1.item(i).getNodeName());
		return false;
	    }
	}
	return true;

    }

    private static boolean isEqualNamedNodeMap(NamedNodeMap m1, NamedNodeMap m2, String testname) {
	if (m1 == null && m2 == null) {
	    passed(testname, "attribute lists are NULL");
	    return true;	
	}
	String lengthInfo = "("+m1.getLength()+"<=>"+m2.getLength()+")";
	if (m1.getLength() != m2.getLength()) {
	    failed(testname, "attribute lists are not same length "+lengthInfo);
	    return false;
	}
	for (int i = 0; i < m1.getLength(); i++) {
	    Node curNode = m1.item(i);
	    boolean foundMatch = false;
	    String nodeToMatchLocation = getLocation()+"/"+curNode.getNodeName();
	    println("+++++ trying to match attribute node '"+nodeToMatchLocation+
		    "' ("+m2.getLength()+" nodes to compare to) +++++");
	    for (int j = 0; i < m2.getLength(); j++) {
		Node compNode = m2.item(j);
		//		System.out.println(j);
		if (isEqualNode(curNode, compNode)) {
		    foundMatch = true;
		    break;
		}
	    }
	    println("+++++ done trying to match attribute node '"+nodeToMatchLocation+"'  +++++");
	    if (!foundMatch) {
	        failed(testname, "no matching element found for node named "+m1.item(i).getNodeName());
		return false;
	    }
	}
	passed(testname, "");
	return true;
    }

    public static void failed(String testname, String text) {
	println("FAILED ["+testname+"] "+text);
    }
    
    public static void passed(String testname, String text) {
	println("passed ["+testname+"] "+text);
    }

    public static void println(String text) {
	print(text);
	//	System.out.println();
    }

    public static void print(String text) {
	/*
	for (int i = 0; i < indent; i++)
	    System.out.print("  ");
	System.out.print(text);
	*/
    }
    
    public static String getLocation() {
	Iterator i = location.iterator();
	String location = "";
	while (i.hasNext()) {
	    location += (String)i.next();
	    if (i.hasNext())
		location += "/";
	}
	return location;
    }

    public static String popLocation() {
	indent--;
	return (String)location.pop();
    }

    public static void pushLocation(String local) {
	location.push(local);
	indent++;
    }

    public static String getNodeTypeName(Node node) {
	int nodeType = node.getNodeType();
	switch(nodeType) {
	case Node.ATTRIBUTE_NODE:
	    return "ATTRIBUTE_NODE";
	case Node.CDATA_SECTION_NODE:
	    return "CDATA_SECTION_NODE";
	case Node.COMMENT_NODE:
	    return "COMMENT_NODE";
	case Node.DOCUMENT_FRAGMENT_NODE:
	    return "DOCUMENT_FRAGMENT_NODE";
	case Node.DOCUMENT_NODE:
	    return "DOCUMENT_NODE";
	case Node.DOCUMENT_TYPE_NODE:
	    return "DOCUMENT_TYPE_NODE";
	case Node.ELEMENT_NODE:
	    return "ELEMENT_NODE";
	case Node.ENTITY_REFERENCE_NODE:
	    return "ENTITY_REFERENCE_NODE";
	case Node.NOTATION_NODE:
	    return "NOTATION_NODE";
	case Node.PROCESSING_INSTRUCTION_NODE:
	    return "PROCESSING_INSTRUCTION_NODE";
	case Node.TEXT_NODE:
	    return "TEXT_NODE";
        default: 
	    return "NodeType is set to an undefined value";
	}
    }

}



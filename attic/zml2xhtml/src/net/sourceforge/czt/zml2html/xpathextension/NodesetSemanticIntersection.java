package net.sourceforge.czt.zml2html.xpathextension;

import java.util.Hashtable;

import org.apache.xpath.NodeSet;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class NodesetSemanticIntersection
{   

  public static boolean isInSubstitutionGroup(NodeList nl1, NodeList nl2)
    {
	NodeSet ns1 = new NodeSet(nl1);
	NodeSet ns2 = new NodeSet(nl2);

	for (int i = 0; i < ns1.getLength(); i++) {
	    Node n = ns1.elementAt(i);
	    if (containsElementWithName(ns2, n.getLocalName()) == false)
		return false;
	}
	
	return true;
    } 
    
    public static boolean containsElementWithName(NodeSet ns2, String localName)
    {
	//      System.out.println("looking for "+localName);	

      for (int k = 0; k < ns2.getLength(); k++) {
	  //       	System.out.println(ns2.elementAt(k).getLocalName());
	if (localName.equals(ns2.elementAt(k).getLocalName()))
	  return true;
      }

      //      System.out.println("not found");

      return false;
    }
}


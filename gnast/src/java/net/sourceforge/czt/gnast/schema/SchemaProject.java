/**
Copyright 2003 Petra Malik
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/



/*
Requirements with respect to the XML schema:
- xs:element either global, used with ref attribute, or have a build
  in or simple type.
- xs:sequence always without arguments (no minOccurs or maxOccurs)
- no xs:restriction
*/
package net.sourceforge.czt.gnast.schema;

import java.io.*;
import java.util.*;
import java.util.logging.Logger;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;

import org.apache.xpath.XPathAPI;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.traversal.NodeIterator;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import net.sourceforge.czt.gnast.*;

/**
 * A Schema project.
 * Parses an XML Schema and identifies all classes
 * to be generated.
 *
 * @author Petra Malik
 * @czt.todo Handle namespaces correcly.
 * @czt.todo Provide bindings properties in the gnast.properties file.
 */
public class SchemaProject implements GnastProject
{
  private static final String sClassName = "SchemaProject";
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast.schema" + "." + sClassName);

  /**
   * A mapping from XML schema types to java types.
   * It is also possible to map any string occuring
   * as a type to a class name.
   */
  private Properties mBindings = new Properties();

  private Document mDoc;
  /**
   * A mapping from class names to SchemaClass objects.
   */
  private Map mHash = new HashMap();

  /**
   * A mapping from enumeration names
   * to a list of all values of that enumeration.
   */
  private Map mEnum = new HashMap();

  /**
   * @param schemaFilename the XML Schema file name.
   * @param mappingFilename the mapping properties file name.
   * @czt.todo Set the binding for IDREF to Object.
   */
  public SchemaProject(String schemaFilename, String mappingFilename)
    throws FileNotFoundException, ParserConfigurationException,
	   SAXException, IOException, TransformerException,
	   XSDException
  {
    try {
      mBindings.load(new FileInputStream(mappingFilename));
    } catch(FileNotFoundException e) {
      sLogger.severe("Cannot find file " + mappingFilename + ".");
    } catch(java.io.IOException e) {
      sLogger.severe("Cannot read file " + mappingFilename + ".");
    }
    InputSource in = new InputSource(new FileInputStream(schemaFilename));
    DocumentBuilderFactory dfactory = DocumentBuilderFactory.newInstance();
    dfactory.setNamespaceAware(true);
    mDoc = dfactory.newDocumentBuilder().parse(in);

    // collecting all Ast classes
    NodeIterator nl = XPathAPI.selectNodeIterator(mDoc, "/xs:schema/xs:element | /xs:schema/xs:group");
    Node n;
    while ((n = nl.nextNode())!= null) {
      SchemaClass c = new SchemaClass(n);
      mHash.put(c.getName(), c);
    }

    // collecting all enumerations
    nl = XPathAPI.selectNodeIterator(mDoc, "//xs:simpleType[xs:restriction/@base = 'xs:string']");
    while ((n = nl.nextNode())!= null) {
      String enumName = getAttributeValue(n, "name");
      List enumValues = new ArrayList();
      if (enumName == null) getAttributeValue(n.getParentNode(), "name");
      // TODO error message if enumName == null
      NodeIterator valueIter = XPathAPI.selectNodeIterator(n, ".//xs:enumeration");
      Node valueNode;
      while ((valueNode = valueIter.nextNode())!= null) {
	enumValues.add(getAttributeValue(valueNode, "value"));
      }
      mEnum.put(enumName, enumValues);
    }
  }

  /**
   *
   */
  public static String getAttributeValue(Node node, String s)
  {
    String value = null;
    try {
      value = XPathAPI.selectSingleNode(node, "@"+s).getNodeValue();
    } catch(NullPointerException e) {
      value = null;
    } catch(TransformerException e) {
      throw new GnastException(e);
    }
    return value;
  }

  /**
   * A node containing the correct namespace information.
   */
  public Node getPropertyBindingNode(Node node)
  {
    Element ns = mDoc.createElement("namespace");
    ns.setAttribute("xmlns:jaxb", "http://java.sun.com/xml/ns/jaxb");
    ns.setAttribute("xmlns:xs", "http://www.w3.org/2001/XMLSchema");
    Node erg = null;
    try {
      erg = XPathAPI.selectSingleNode(node,
	      "./xs:annotation/xs:appinfo/jaxb:property", ns);
    } catch(TransformerException e) {
      throw new GnastException(e);
    }
    return erg;
  }

  /**
   * @return ... and <code>null<code> if <code>s</code> is <code>null</code>.
   */
  public static String removeNamespace(String s)
  {
    if (s == null) return null;
    try {
      String[] blubb = s.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
	return s;
      }
      if (blubb.length == 2) {
	return blubb[1];
      }
      if (blubb.length > 2) {
	System.err.println("Something strange happend " +
			   "while removing the namespace");
	return s;
      }
    } catch (Exception e) {
      throw new GnastException(e);
    }
    return s;
  }

  public Collection getAstClasses()
  {
    return mHash.values();
  }

  public Map getEnumerations()
  {
    return mEnum;
  }






  class SchemaClass extends AbstractGnastClass
  {
    /**
     * The name of this Schema class.
     */
    private String mName = null;

    /**
     * Is this class abstract?
     */
    private boolean mAbstract = false;

    /**
     * The base class of this Schema class.
     */
    private String mExtends = null;

    /**
     * Properties for this Schema class.
     */
    private List mProperties = null;

    /**
     *
     */
    private String mXSDType = null;

    /**
     * Constructor.
     *
     * @param node  The XML Schema node from which all the neccessary
     *              information is extracted.
     */
    SchemaClass(Node node)
      throws XSDException
    {
      parseName(node);
      parseAbstract(node);
      parseExtends(node);
      parseProperties(node);
    }

    public String getName()
    {
      return mName;
    }

    public boolean getNameEqualsType()
    {
      return mXSDType.endsWith(mName);
    }

    public String getImplName()
    {
      return getName() + "Impl";
    }

    public String getExtends()
    {
      String methodName = "getExtends";
      sLogger.entering(sClassName, methodName, mName);
      String erg = mExtends;
      sLogger.exiting(sClassName, methodName, erg);
      return erg;
    }

    public boolean isInstanceOf(String name)
    {
      boolean erg = false;
      String parent = getExtends();
      if (parent != null) {
	if (parent.equals(name)) return true;
	GnastClass c = (GnastClass) mHash.get(parent);
	if (c != null) {
	  erg = c.isInstanceOf(name);
	} else if (parent.equals("TermA")) {
	  erg = true;
	}
      }
      return erg;
    }

    public String getExtendsImpl()
    {
      String methodName = "getExtendsImpl";
      sLogger.entering(sClassName, methodName, mName);
      String erg = getExtends() + "Impl";
      sLogger.exiting(sClassName, methodName, erg);
      return erg;
    }

    public List getProperties()
    {
      String methodName = "getProperties";
      sLogger.entering(sClassName, methodName, mName);
      List erg = new Vector();
      erg.addAll(mProperties);
      sLogger.exiting(sClassName, methodName, erg);
      return erg;
    }

    public List getInheritedProperties()
    {
      String methodName = "getInheritedProperties";
      sLogger.entering(sClassName, methodName, mName);
      List erg = null;
      String ext = getExtends();
      if (ext != null) {
	GnastClass c = (GnastClass) mHash.get(ext);
	if (c != null) {
	  erg = c.getAllProperties();
	} else if (ext.equals("Term") || ext.equals("TermA")) {
	  erg = new ArrayList();
	}
      }
      sLogger.exiting(sClassName, methodName, erg);
      return erg;
    }

    private void parseExtends(Node node)
    {
      String methodName = "parseExtends";
      sLogger.entering(sClassName, methodName, node);
      String ext =
	removeNamespace(getAttributeValue(node, "substitutionGroup"));
      if (ext == null) {
	ext = "Term";
      }
      mExtends = ext;
      sLogger.fine(mName + " extends " + mExtends);
      sLogger.exiting(sClassName, methodName);
    }

    /**
     * Uses mExtends, so make use it is set prior to calling this method.
     */
    private void parseProperties(Node node)
      throws XSDException
    {
      String methodName = "parseProperties";
      sLogger.entering(sClassName, methodName, node);

      mProperties = new ArrayList();
      if (node.getNodeName().equals("xs:group")) {
	mProperties = collectProperties(node);
	return;
      }
      try {
	mXSDType = XPathAPI.selectSingleNode(node, "@type").getNodeValue();
	mProperties = collectAllProperties(XPathAPI.selectSingleNode(node,
 "//xs:schema/xs:complexType[@name=substring-after('" + mXSDType + "', ':')]"),
		         mExtends);
      } catch(NullPointerException e) {
	// the type attribute is not there
	String message = "The type attribute of a global XML Schema " +
	  "element, group, or type is either missing or invalid: ";
	message += node.toString();
	throw new XSDException(message);
      } catch(TransformerException e) {
	e.printStackTrace();
      }
      sLogger.fine("Properties for " + mName + " are " + mProperties);
      sLogger.exiting(sClassName, methodName);
    }

    /**
     * Identifies all properties that are children of that node.
     * For instance, given an xs:complexType node, this method
     * returns a list of all properties associated with this type
     * (not included inherited properties).
     *
     * @czt.todo This method should be static.
     */
    private List collectProperties(Node node)
      throws XSDException
    {
      final String methodName = "collectProperties";
      sLogger.entering(sClassName, methodName, node);

      List list = new ArrayList();
      String xpathexpr = ".//xs:choice | " +
	".//xs:element[not(parent::xs:choice)] | " +
	".//xs:attribute";
      NodeIterator nl = null;
      try {
	nl = XPathAPI.selectNodeIterator(node, xpathexpr);
      } catch(Exception e) {
	sLogger.fine("ERROR while getting the properties " +
		     "of a Schema class.");
	e.printStackTrace();
	throw new XSDException();
      }
      while ((node = nl.nextNode()) != null) {
	try {
	  SchemaProperty prop = new SchemaProperty(node);
	  sLogger.finer("Found property " + prop);
	  list.add(prop);
	} catch (XSDException e) {
	  XSDException exception =
	    new XSDException("Error while processing " + node.toString(), e);
	  sLogger.exiting(sClassName, methodName, exception);
	  throw exception;
	}
      }
      sLogger.exiting(sClassName, methodName, list);
      return list;
    }

    private void parseName(Node node)
      throws XSDException
    {
      try {
	mName = XPathAPI.selectSingleNode(node, "@name").getNodeValue();
      } catch(NullPointerException e) {
	String message = "The name attribute of a global XML Schema " +
	  "element, group, or type is missing: ";
	message += node.toString();
	sLogger.fine("Caught NullPointerException");
	throw new XSDException(message);
      } catch(TransformerException e) {
	sLogger.fine("Caught TransformerException");
	throw new GnastException(e);
      }
    }

    public boolean getAbstract()
    {
      return mAbstract;
    }

    private void parseAbstract(Node node)
    {
      boolean erg = false;
      try {
	Node n=XPathAPI.selectSingleNode(node, "@abstract");
	if (n != null && n.getNodeValue().equals("true")) erg = true;
      } catch(Exception e) {
	throw new GnastException(e);
      }
      mAbstract = erg;
    }

    /**
     * startNode is a xs:complexType nodes
     * @param end    the name of the complex type
     *               where the iteration is stopped
     * @throws NullPointerException if one of the arguments is <code>null</code>.
     */
    private List collectAllProperties(Node startNode, String end)
      throws XSDException
    {
      String methodName = "collectAllProperties";
      Object[] args = { startNode, end };
      sLogger.entering(sClassName, methodName, args);

      if (startNode == null || end == null) {
	NullPointerException e = new NullPointerException();
	sLogger.exiting(sClassName, methodName, e);
	throw e;
      }

      List erg = new Vector();
      try {
	String name =
	  XPathAPI.selectSingleNode(startNode, "@name").getNodeValue();
	if (name.equals(end)) {
	  sLogger.exiting(sClassName, methodName, erg);
	  return erg;
	}
	if (name.equals("TermA")) {
	  sLogger.fine("Updating extends to TermA");
	  mExtends = "TermA";
	  sLogger.exiting(sClassName, methodName, erg);
	  return erg;
	}
      } catch(Exception e) {
	System.err.println("No name found.");
	throw new XSDException();
      }
      erg.addAll(collectProperties(startNode));
      try {
	String ext = null;
	Node n = XPathAPI.selectSingleNode(startNode,
	      "./xs:complexContent/xs:extension/@base");
	if (n != null) ext = n.getNodeValue();
	if (ext != null) {
	  erg.addAll(collectAllProperties(XPathAPI.selectSingleNode(startNode,
   "//xs:schema/xs:complexType[@name=substring-after('" + ext + "', ':')]"),
          end));
	}
      } catch(Exception e) {
	XSDException exception =
	  new XSDException("Error while processing " + startNode, e);
	throw exception;
      }
      sLogger.exiting(sClassName, methodName, erg);
      return erg;
    }
  } // end SchemaClass




  /**
   * xs:element or xs:choice or xs:attribute
   */
  class SchemaProperty extends AbstractProperty
  {
    /**
     * The name of this property.
     *
     * @see #parseName(Node)
     */
    private String mName = null;
    
    /**
     * The type of this property.
     *
     * @see #parseType(Node)
     */
    private String mType = null;
    
    /**
     *
     */
    private boolean mAttribute = false;

    SchemaProperty(Node node)
      throws XSDException
    {
      parseName(node);
      parseType(node);
      if (node.getLocalName().equals("attribute")) {
	mAttribute = true;
      }
    }

    public boolean getAttribute()
    {
      return mAttribute;
    }

    /**
     * <p>Parses an xs:element, xs:choice, or xs:attribute node
     * and sets the name of this property appropriatly.<p>
     *
     * <p>The rules are as follows:  If there is a jaxb property customization,
     * take the value of the name attribute. ... </p>
     */
    private void parseName(Node node)
      throws XSDException
    {
      Node n = getPropertyBindingNode(node);
      if (n != null) mName = getAttributeValue(n, "name");
      if (mName == null) mName = getAttributeValue(node, "name");
      if (mName == null) {
	mName = removeNamespace(getAttributeValue(node, "ref"));
      }
      if (mName == null) {
	String message = "Cannot generate a getter method " +
	  "since there is neither a property customization, " +
	  "a name attribute, nor a ref attribute " +
	  "for the following node: ";
	message += node.toString();
	throw new XSDException(message);
      }
    }

    /**
     *
     * @czt.todo Check the values of attributes minOccurs and maxOccurs.
     *           So far, it is only checked whether these attributes are
     *           present or not.
     */
    public void parseType(Node node)
      throws XSDException
    {
      String erg = null;
      if (getAttributeValue(node, "maxOccurs") != null)
      {
	erg = "java.util.List";
      }
      if (erg == null) erg = removeNamespace(getAttributeValue(node, "ref"));
      if (erg == null) {
	String typeAttr = removeNamespace(getAttributeValue(node, "type"));
	if (typeAttr == null) {
	  String message = "There is neither a type nor a ref attribute " +
	    "for the following node:\n         ";
	  message += node.toString();
	  throw new XSDException(message);
	}
	erg = (String) mBindings.get(typeAttr);
	if (erg == null) {
	  String message = "Cannot find binding for " + typeAttr + "; assume it is a known class.";
	  erg = typeAttr;
	}
      }
      mType = erg;
    }
    
    public String getName()
    {
      return mName;
    }
    
    public String getType()
    {
      return mType;
    }
    
    public boolean getImmutable()
    {
      if (mName.equals("Name") ||
	  mName.equals("DeclName") ||
	  mName.equals("RefName")) return true;
      return false;
    }
  } // end class SchemaAttribute
} // end class SchemaProject

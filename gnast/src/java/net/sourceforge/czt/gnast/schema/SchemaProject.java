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
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String sClassName = "SchemaProject";

  /**
   * The logger used when logging information is provided.
   */
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast.schema" + "." + sClassName);

  /**
   * <p>A mapping from XML schema types to java types.
   * It is also possible to map any string occuring
   * as a type to a class name.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Properties mBindings = new Properties();

  private Properties mGnastProperties = new Properties();

  private Document mDoc;

  private Element mNamespaceNode;

  /**
   * A mapping from class names to SchemaClass objects.
   */
  private Map mHash = new HashMap();

  /**
   * A mapping from enumeration names
   * to a list of all values of that enumeration.
   */
  private Map mEnum = new HashMap();
  private Map mPackages = new HashMap();

  private String mTargetNamespace;
  private String mImportNamespace;

  private String mTargetPackage;
  private String mImportPackage;

  private ProjectProperties mProjectProperties;

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * @param schemaFilename the XML Schema file name.
   * @param mapping the mapping information.
   */
  public SchemaProject(String schemaFilename,
		       Properties mapping,
		       ProjectProperties projectProperties,
		       Properties gnastProperties)
    throws FileNotFoundException, ParserConfigurationException,
	   SAXException, IOException, XSDException
  {
    if (mapping != null) mBindings = mapping;
    if (gnastProperties != null) mGnastProperties = gnastProperties;
    mProjectProperties = projectProperties;
    InputSource in = new InputSource(new FileInputStream(schemaFilename));
    DocumentBuilderFactory dfactory = DocumentBuilderFactory.newInstance();
    dfactory.setNamespaceAware(true);
    mDoc = dfactory.newDocumentBuilder().parse(in);
    mNamespaceNode = mDoc.createElement("namespace");
    mNamespaceNode.setAttribute("xmlns:jaxb",
				"http://java.sun.com/xml/ns/jaxb");
    mNamespaceNode.setAttribute("xmlns:xs",
				"http://www.w3.org/2001/XMLSchema");

    Node schemaNode = selectSingleNode(mDoc, "/xs:schema");
    if (schemaNode != null) {
      mTargetNamespace = getNodeValue(schemaNode, "@targetNamespace");
      if (mTargetNamespace != null) {
	mTargetPackage = mGnastProperties.getProperty(mTargetNamespace);
      }
      mImportNamespace = getNodeValue(schemaNode, "xs:import/@namespace");
      if (mImportNamespace != null) {
	mImportPackage = mGnastProperties.getProperty(mImportNamespace);
      }

      Node n;

      // collecting all enumerations
      NodeIterator nl = selectNodeIterator(schemaNode,
		    "xs:simpleType[xs:restriction/@base = 'xs:string']");
      while ((n = nl.nextNode())!= null) {
	String enumName = getNodeValue(n, "@name");
	List enumValues = new ArrayList();
	if (enumName == null) getNodeValue(n.getParentNode(), "@name");
	// TODO error message if enumName == null
	NodeIterator valueIter = selectNodeIterator(n, ".//xs:enumeration");
	Node valueNode;
	while ((valueNode = valueIter.nextNode())!= null) {
	  enumValues.add(getNodeValue(valueNode, "@value"));
	}
	mEnum.put(enumName, enumValues);
      }

      // collecting all Ast classes
      nl = selectNodeIterator(schemaNode, "xs:element | xs:group");
      while ((n = nl.nextNode())!= null) {
	SchemaClass c = new SchemaClass(n);
	mHash.put(c.getName(), c);
      }
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ************** ACCESSING THE XPATH API *********************

  /**
   * Use the given XPath expression to select a single node.
   * A {@link GnastException} is thrown in case a transformer
   * error occurs.
   *
   * @param node the context node to start searching from.
   * @param xPathExpr the XPath expression.
   */
  public Node selectSingleNode(Node node, String xPathExpr)
  {
    try {
      return XPathAPI.selectSingleNode(node, xPathExpr, mNamespaceNode);
    } catch(TransformerException e) {
      throw new GnastException(e);
    }
  }
  public Node selectSingleNode(String xPathExpr)
  {
    return selectSingleNode(mDoc, xPathExpr);
  }

  /**
   * Use the given XPath expression to select a node list.
   * A {@link GnastException} is thrown in case a transformer
   * error occurs.
   */
  public NodeIterator selectNodeIterator(Node node, String xPathExpr)
  {
    try {
      return XPathAPI.selectNodeIterator(node, xPathExpr, mNamespaceNode);
    } catch(TransformerException e) {
      throw new GnastException(e);
    }
  }
  public NodeIterator selectNodeIterator(String xPathExpr)
  {
    return selectNodeIterator(mDoc, xPathExpr);
  }

  /**
   * Returns the attribute value of the attribute whos name is
   * <code>s</code> for the given node or <code>null</code> if
   * the attribute is not present.
   */
  public String getNodeValue(Node node, String s)
  {
    try {
      return selectSingleNode(node, s).getNodeValue();
    } catch(NullPointerException e) {
      return null;
    }
  }

  // ************* ACCESSING SPECIAL SCHEMA NODES ***************

  public Node getGlobalElementNode(String name)
  {
    return selectSingleNode(
          "//xs:schema/xs:element[@name='" + name + "']");
  }

  /**
   * Returns an xs:complexType node that has an attribute name
   * whos value is equal to <code>name</code>.
   *
   * @param name the name of the complex type to be returned.
   * @return an xs:complexType node that has an attribute name
   *         whos value is equal to <code>name</code>;
   *         <code>null</code> if such a node could not be found.
   */
  public Node getComplexTypeNode(String name)
  {
    return selectSingleNode(
          "//xs:schema/xs:complexType[@name='" + name + "']");
  }

  public String getPropertyBinding(Node node)
  {
    return getNodeValue(node,
	      "./xs:annotation/xs:appinfo/jaxb:property/@name");
  }

  /**
   * <p>Returns a list of all AST classes computed.</p>
   *
   * <p>For each global schema element, an AST class is
   * generated.</p>
   */
  public Map getAstClasses()
  {
    return mHash;
  }

  /**
   * Returns a Map of all enumerations found in the given
   * XML schema file.
   */
  public Map getEnumerations()
  {
    return mEnum;
  }

  public String getTargetNamespace()
  {
    return mTargetNamespace;
  }

  public String getImportNamespace()
  {
    return mImportNamespace;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  /**
   * This method asserts that there is at most one colon in the given string.
   * @return ... and <code>null<code> if <code>s</code> is <code>null</code>.
   */
  public String removeNamespace(String s)
  {
    if (s == null) return null;
    try {
      String[] blubb = s.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
	return s;
      } else {
	if (!mTargetNamespace.equals(mGnastProperties.getProperty(blubb[0]))) {
	  mPackages.put(blubb[1], mGnastProperties.getProperty(blubb[0]));
	  mPackages.put(blubb[1] + "Impl",
			mGnastProperties.getProperty(blubb[0]));
	}
	return blubb[1];
      }
    } catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * @return should never be <code>null</code>.
   */
  public String getPackageInfo(String type)
  {
    String result = "";
    if (mPackages.get(type) != null) {
      if (type.equals("Term") || type.equals("TermA")) {
	return "net.sourceforge.czt.core.ast";
      }
      if (type.equals("TermImpl") || type.equals("TermAImpl")) {
	return "net.sourceforge.czt.core.impl";
      }
      result = mGnastProperties.getProperty((String)mPackages.get(type));
      if (type.endsWith("Impl")) result = result + ".impl.";
      else result = result + ".ast.";
    }
    return result;
  }

  // ############################################################
  // ##################### INNER CLASSES ########################
  // ############################################################

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
     * Creates a new schema class from the node given.
     *
     * @param node  The XML Schema node from which all the neccessary
     *              information is extracted.
     */
    SchemaClass(Node node)
      throws XSDException
    {
      // parsing the name
      mName = getNodeValue(node, "@name");
      if (mName == null) {
	String message = "The name attribute of a global XML Schema " +
	  "element, group, or type is missing: ";
	message += node.toString();
	throw new XSDException(message);
      }

      // parsing whether this class is abstract
      String abstractAttribute = getNodeValue(node, "@abstract");
      if (new String("true").equals(getNodeValue(node, "@abstract")))
	mAbstract = true;
      else mAbstract = false;

      // parsing the substitution group attribute
      mExtends =
	removeNamespace(getNodeValue(node, "@substitutionGroup"));

      mProperties = new ArrayList();
      if (node.getNodeName().equals("xs:group")) {
	mProperties = collectProperties(node);
      }

      // parsing the type
      mXSDType = getNodeValue(node, "@type");
      if (mXSDType == null) {
	String message = "The type attribute for " + mName +
	  " is either missing or invalid.  " +
	  "Are you using unnamed types?  " +
	  "Unnamed types are currently not supported.";
	throw new XSDException(message);
      }

      // collecting properties
      mProperties = collectAllProperties(removeNamespace(mXSDType));

      if (mExtends == null) {
	mExtends = "Term";
      }
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
      String result = getPackageInfo(mExtends);
      result = result + mExtends;
      sLogger.exiting(sClassName, methodName, result);
      return result;
    }

    public String getPackage()
    {
      return mProjectProperties.getAstPackage();
    }

    public String getImplPackage()
    {
      return mProjectProperties.getImplPackage();
    }

    /**
     * Returns whether this gnast class is an instance of
     * the gnast class whos name is <code>name</code>.
     *
     * @param  name the name of the gnast class.
     * @return <code>true</code> if this class is an instance of
     *         a class named <code>name</code>;
     *         <code>false</code> otherwise.
     */
    public boolean isInstanceOf(String name)
    {
      boolean result = false;
      String parent = getExtends();
      if (parent != null) {
	if (parent.equals(name)) return true;
	GnastClass c = (GnastClass) mHash.get(parent);
	if (c != null) {
	  result = c.isInstanceOf(name);
	}
      }
      return result;
    }

    public String getImplExtends()
    {
      String methodName = "getExtendsImpl";
      sLogger.entering(sClassName, methodName, mName);
      String extendsImpl = mExtends + "Impl";
      String result = getPackageInfo(extendsImpl);
      result = result + extendsImpl;
      sLogger.exiting(sClassName, methodName, result);
      return result;
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

    /**
     * Uses mExtends and mName (in log messages and exceptions),
     * so make sure these are set prior to calling this method.
     *
     * @throws NullPointerException if <code>node</code> is <code>null</code>.
     */
    private void parseProperties(Node node)
      throws XSDException
    {
      String methodName = "parseProperties";
      sLogger.entering(sClassName, methodName, node);

      if (node == null) {
	NullPointerException e = new NullPointerException();
	sLogger.exiting(sClassName, methodName, e);
	throw e;
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
	nl = selectNodeIterator(node, xpathexpr);
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

    public boolean getAbstract()
    {
      return mAbstract;
    }

    /**
     * The search is stopped at mExtends.
     *
     * @param typeName  the name of the complex type
     *                  where the search is started.
     * @throws NullPointerException if one of the arguments is
     *                              <code>null</code>.
     * @czt.todo Currently, this method changes the member
     *           variable mExtends (when it finds a type whos
     *           name is TermA).  This is very dangerous and
     *           unintuitive.  Think of a better way to handle
     *           this.
     */
    private List collectAllProperties(String typeName)
      throws XSDException
    {
      String methodName = "collectAllProperties";
      sLogger.entering(sClassName, methodName, typeName);

      if (typeName == null) {
	NullPointerException e = new NullPointerException();
	sLogger.exiting(sClassName, methodName, e);
	throw e;
      }

      List erg = new Vector();

      if (typeName.equals("TermA")) {
	mExtends = "TermA";
      } else if (! typeName.equals(mExtends)) {
	Node startNode = getComplexTypeNode(typeName);
	if (startNode == null) {
	  sLogger.warning("Could not find definition of complex type "
			  + typeName
			  + "; proceeding anyway.");
	  sLogger.exiting(sClassName, methodName, erg);
	  return erg;
	}

	erg.addAll(collectProperties(startNode));
	Node n = selectSingleNode(startNode,
	      "./xs:complexContent/xs:extension/@base");
	if (n != null && n.getNodeValue() != null) {
	  String base = removeNamespace(n.getNodeValue());
	  erg.addAll(collectAllProperties(base));
	}
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
      mName = getPropertyBinding(node);
      if (mName == null) mName = getNodeValue(node, "@name");
      if (mName == null)
	mName = removeNamespace(getNodeValue(node, "@ref"));
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
      if (getNodeValue(node, "@maxOccurs") != null)
      {
	erg = "java.util.List";
      }
      if (erg == null) erg = removeNamespace(getNodeValue(node, "@ref"));
      if (erg == null) {
	String typeAttr = removeNamespace(getNodeValue(node, "@type"));
	if (typeAttr == null) {
	  String message = "There is neither a type nor a ref attribute " +
	    "for the following node:\n         ";
	  message += node.toString();
	  throw new XSDException(message);
	}
	erg = (String) mBindings.get(typeAttr);
	if (erg == null) {
	  erg = typeAttr;
	  if (mEnum.get(typeAttr) == null &&
	      getGlobalElementNode(typeAttr) == null) {
	    String message = "Cannot find binding for " +
	      getNodeValue(node, "@type") +
	      "; assume it is an existing class.";
	    sLogger.warning(message);
	  }
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
      String result = getPackageInfo(mType);
      result = result + mType;
      return result;
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

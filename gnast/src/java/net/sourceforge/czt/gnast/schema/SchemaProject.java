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
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.util.*;
import java.util.logging.Logger;
import java.util.regex.*;

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
 * Parses an XML Schema file and collects all classes
 * to be generated.
 *
 * @author Petra Malik
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
   * Access to the XPath API (should never be <code>null</code>).
   */
  XPath mXPath;

  /**
   * <p>A mapping from XML schema types to java types.
   * It is also possible to map any string occuring
   * as a type to a class name.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Properties mBindings = new Properties();

  private Document mDoc;

  /**
   * A mapping from class names to SchemaClass objects.
   * This map does only contain classes from this project.
   */
  private Map mHash = new HashMap();

  /**
   * Ast classes from other namespaces.
   */
  private Map mAstClasses = new HashMap();

  /**
   * A mapping from enumeration names
   * to a list of all values of that enumeration.
   * This map does only contain enumerations from this project.
   */
  private Map mEnum = new HashMap();

  /**
   * The project imported from the XML Schema.
   */
  private String mImportProject;

  private ProjectProperties mProject;
  private GlobalProperties mGlobal;

  /**
   * A mapping from namespace prefixes
   * to its associated namespaces.
   *
   * Should never be <code>null</code>.
   */
  private Properties mNSPrefixProps;

  /**
   * A mapping from objects that does not belong to the project
   * to be generated to its corresponding project names.
   */
  private final Properties mObjectProjectProps = new Properties();

  /**
   * A mapping from project names to the actual projects.
   */
  private final Map mProjects = new HashMap();

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
		       GlobalProperties globalProperties)
    throws FileNotFoundException, ParserConfigurationException,
	   SAXException, IOException, XSDException
  {
    mNSPrefixProps = collectNamespacePrefixes(schemaFilename);
    mGlobal = globalProperties;
    if (mapping != null) mBindings = mapping;
    mProject = projectProperties;
    InputSource in = new InputSource(new FileInputStream(schemaFilename));
    DocumentBuilderFactory dfactory = DocumentBuilderFactory.newInstance();
    dfactory.setNamespaceAware(true);
    mDoc = dfactory.newDocumentBuilder().parse(in);
    mXPath = new XPath(mDoc);
    Node schemaNode = mXPath.selectSingleNode(mDoc, "/xs:schema");
    if (schemaNode != null) {
      String importNamespace = mXPath.getNodeValue(schemaNode, "xs:import/@namespace");
      if (importNamespace != null) {
	mImportProject = mGlobal.getProjectName(importNamespace);
      }

      Node n;

      // collecting all enumerations
      NodeIterator nl = mXPath.selectNodeIterator(schemaNode,
		    "xs:simpleType[xs:restriction/@base = 'xs:string']");
      while ((n = nl.nextNode())!= null) {
	String enumName = mXPath.getNodeValue(n, "@name");
	List enumValues = new ArrayList();
	if (enumName == null) mXPath.getNodeValue(n.getParentNode(), "@name");
	// TODO error message if enumName == null
	NodeIterator valueIter = mXPath.selectNodeIterator(n, ".//xs:enumeration");
	Node valueNode;
	while ((valueNode = valueIter.nextNode())!= null) {
	  enumValues.add(mXPath.getNodeValue(valueNode, "@value"));
	}
	mEnum.put(enumName, enumValues);
      }

      // collecting all Ast classes
      nl = mXPath.selectNodeIterator(schemaNode, "xs:element | xs:group");
      while ((n = nl.nextNode())!= null) {
	SchemaClass c = new SchemaClass(n);
	mHash.put(c.getName(), c);
      }
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ************* ACCESSING SPECIAL SCHEMA NODES ***************

  public Node getGlobalElementNode(String name)
  {
    return mXPath.selectSingleNode(
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
    return mXPath.selectSingleNode(
          "//xs:schema/xs:complexType[@name='" + name + "']");
  }

  public String getPropertyBinding(Node node)
  {
    return mXPath.getNodeValue(node,
	      "./xs:annotation/xs:appinfo/jaxb:property/@name");
  }

  // *********************** OTHERS ************************

  /**
   * Returns the namespace that corresponds to the given prefix.
   */
  protected String getNamespace(String prefix)
  {
    return mNSPrefixProps.getProperty(prefix);
  }

  /**
   * Returns the name of the project that corresponds to the
   * given namespace.
   */
  protected String getProjectName(String namespace)
  {
    return mGlobal.getProjectName(namespace);
  }

  /**
   * Returns the project that has the given name.
   */
  protected Project getProject(String name)
  {
    return mGlobal.getProject(name);
  }

  /**
   * Returns the GnastClass with the given name.
   *
   * @param className the name of the GnastClass to be retrieved.
   *                  (it may contain the package name).
   * @return the GnastClass with that name, or <code>null</code>
   *         if a GnastClass with that name could not be found.
   * @czt.todo What about Term and TermA?
   * @czt.todo Should it really be possible to support names
   *           containing package info?
   */
  public GnastClass getAstClass(String className)
  {
    String methodName = "getAstClass";
    sLogger.entering(sClassName, methodName, className);

    String[] blubb = className.split("\\.");
    String name = blubb[blubb.length-1];
    GnastClass result = (GnastClass) mHash.get(name);
    if (result == null) {
      String projectName = mObjectProjectProps.getProperty(name);
      if (projectName != null) {
	Project project = getProject(projectName);
	if (project != null) result = project.getAstObject(name);
      }
    }
    sLogger.exiting(sClassName, methodName, result);
    return result;
  }

  /**
   * <p>Returns a mapping from class names to SchemaClass objects.</p>
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

  /**
   * Return the name of the imported project.
   */
  public String getImportProject()
  {
    return mImportProject;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  /**
   * <p>Collects all used namespace prefixes (defined via xmlns)
   * of an XML file into a map. The namespace prefix is used as
   * the key, its associated namespace is the value of the map.</p>
   *
   * <p>If the same prefix is used several times, only the last
   * occurrence is contained in the map.</p>
   *
   * @param filename the name of the (XML) file to be searched.
   * @return a map from string representing a namespace prefix
   *         to string representing its associated namespace.
   */
  public static Properties collectNamespacePrefixes(String filename)
  {
    final String methodName = "collectNamespacePrefixes";
    sLogger.entering(sClassName, methodName, filename);

    final Properties result = new Properties();
    Pattern p =
      Pattern.compile("xmlns:[a-zA-Z]+[\\s]*\\=\\s*\\\"[^\\\"]*\\\"");
    CharSequence seq;
    try {
      seq = file2CharSeq(filename);
    } catch(IOException e) {
      sLogger.warning("Cannot read " + filename);
      return null;
    }
    Matcher m = p.matcher(seq);
    while(m.find()) {
      String s = m.group();
      String[] blubb = s.split("\"");
      Pattern p2 = Pattern.compile("xmlns:[a-zA-Z]+[^a-zA-Z]");
      Matcher m2 = p2.matcher(blubb[0]);
      if (m2.find()) {
	String string = m2.group();
	result.setProperty(string.substring(6, string.length()-1), blubb[1]);
      }
    }
    sLogger.exiting(sClassName, methodName, result);
    return result;
  }

  /**
   * <p>Converts the contents of a file into a CharSequence
   * suitable for use by the regex package.</p>
   *
   * @param filename the name of the file to be converted.
   * @return a <code>CharSequence</code> of the contents of
   *         the given file.
   */
  public static CharSequence file2CharSeq(String filename)
    throws IOException
  {
    FileInputStream fis = new FileInputStream(filename);
    FileChannel fc = fis.getChannel();
    
    // Create a read-only CharBuffer on the file
    ByteBuffer bbuf = fc.map(FileChannel.MapMode.READ_ONLY, 0, (int)fc.size());
    CharBuffer cbuf = Charset.forName("8859_1").newDecoder().decode(bbuf);
    return cbuf;
  }

  /**
   * This method asserts that there is at most one colon in the given string.
   * @return ... and <code>null<code> if <code>s</code> is <code>null</code>.
   */
  public String removeNamespace(String s)
  {
    final String methodName = "removeNamespace";
    sLogger.entering(sClassName, methodName, s);
    if (s == null) return null;
    try {
      String[] blubb = s.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
	sLogger.exiting(sClassName, methodName, s);
	return s;
      } else {
	String prefix = blubb[0];
	String obj = blubb[1];
	String namespace = getNamespace(prefix);
	if (! namespace.equals("http://www.w3.org/2001/XMLSchema")) {
	  String projectName = getProjectName(namespace);
	  if (projectName == null) {
	    sLogger.warning("Cannot find project that corresponds to prefix "
			    + prefix);
	  } else if (!mProject.getName().equals(projectName)) {
	    mObjectProjectProps.setProperty(obj, projectName);
	    mObjectProjectProps.setProperty(obj + "Impl", projectName);
	  }
	}
	sLogger.exiting(sClassName, methodName, obj);
	return obj;
      }
    } catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * Returns the package of the given type, followed by a dot.
   *
   * @return should never be <code>null</code>.
   * @czt.todo Is this method really needed?
   */
  public String getPackageInfo(String type)
  {
    final String methodName = "getPackageInfo";
    sLogger.entering(sClassName, methodName, type);

    String result = "";
    String projectName = mObjectProjectProps.getProperty(type);
    if (projectName != null) {
      Project project = getProject(projectName);
      if (project != null) {
	if (type.equals("Term") || type.equals("TermA")) {
	  return "net.sourceforge.czt.core.ast.";
	}
	if (type.equals("TermImpl") || type.equals("TermAImpl")) {
	  return "net.sourceforge.czt.core.impl.";
	}
	if (type.endsWith("Impl")) result = project.getImplPackage() + ".";
	else result = project.getAstPackage() + ".";
      }
    }
    sLogger.exiting(sClassName, methodName, result);
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
      mName = mXPath.getNodeValue(node, "@name");
      if (mName == null) {
	String message = "The name attribute of a global XML Schema " +
	  "element, group, or type is missing: ";
	message += node.toString();
	throw new XSDException(message);
      }

      // parsing whether this class is abstract
      String abstractAttribute = mXPath.getNodeValue(node, "@abstract");
      if (new String("true").equals(mXPath.getNodeValue(node, "@abstract")))
	mAbstract = true;
      else mAbstract = false;

      // parsing the substitution group attribute
      mExtends =
	removeNamespace(mXPath.getNodeValue(node, "@substitutionGroup"));

      mProperties = new ArrayList();
      if (node.getNodeName().equals("xs:group")) {
	mProperties = collectProperties(node);
      }

      // parsing the type
      mXSDType = mXPath.getNodeValue(node, "@type");
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
      return mExtends;
    }

    public String getPackage()
    {
      return mProject.getAstPackage();
    }

    public String getImplPackage()
    {
      return mProject.getImplPackage();
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
      String result = mExtends + "Impl";
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
	GnastClass c = getAstClass(ext);
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
     * @czt.todo Should this method be static?
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
	nl = mXPath.selectNodeIterator(node, xpathexpr);
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
	  sLogger.warning("Cannot find definition of complex type "
			  + typeName
			  + "; proceeding anyway.");
	  sLogger.exiting(sClassName, methodName, erg);
	  return erg;
	}

	erg.addAll(collectProperties(startNode));
	Node n = mXPath.selectSingleNode(startNode,
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
      if (mName == null) mName = mXPath.getNodeValue(node, "@name");
      if (mName == null)
	mName = removeNamespace(mXPath.getNodeValue(node, "@ref"));
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
     * @czt.todo Don't use the xs namespace prefix explicitly.
     */
    public void parseType(Node node)
      throws XSDException
    {
      String result = null;
      if (mXPath.getNodeValue(node, "@maxOccurs") != null)
      {
	result = "java.util.List";
      } else if ("xs:choice".equals(node.getNodeName())) {
	result = "Object";
      } else {
	result = removeNamespace(mXPath.getNodeValue(node, "@ref"));
      }
      if (result == null) {
	String typeAttr = removeNamespace(mXPath.getNodeValue(node, "@type"));
	if (typeAttr == null) {
	  String message = "There is neither a type nor a ref attribute " +
	    "for the following node:\n         ";
	  message += node.toString();
	  throw new XSDException(message);
	}
	result = (String) mBindings.get(typeAttr);
	if (result == null) {
	  result = typeAttr;
	  if (mEnum.get(typeAttr) == null &&
	      getGlobalElementNode(typeAttr) == null) {
	    String message = "Cannot find binding for " +
	      mXPath.getNodeValue(node, "@type") +
	      "; assume it is an existing class.";
	    sLogger.warning(message);
	  }
	}
      }
      mType = result;
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

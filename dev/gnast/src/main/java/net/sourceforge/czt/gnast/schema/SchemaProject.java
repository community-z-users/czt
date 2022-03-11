/*
  Copyright (C) 2003, 2004, 2005, 2006, 2007 Petra Malik
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
- namespace prefixes are unique
*/
package net.sourceforge.czt.gnast.schema;

import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.logging.Logger;
import java.util.regex.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.*;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.traversal.NodeIterator;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import net.sourceforge.czt.gnast.*;
import net.sourceforge.czt.gnast.gen.*;

/**
 * A Schema project.
 * Parses an XML Schema file and collects all classes
 * to be generated.
 *
 * @author Petra Malik
 */
public class SchemaProject
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  private static final Logger LOGGER = Logger.getLogger(SchemaProject.class.getName());
  
  /**
   * Static instance of TransformerFactory since it is thread safe and may be expensive.
   */
  private static final TransformerFactory TRANSFORMER_FACTORY = TransformerFactory.newInstance();

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String CLASS_NAME = "SchemaProject";

  /**
   * Access to the XPath API (should never be <code>null</code>).
   */
  private XPath xPath_;

  /**
   * <p>A mapping from XML schema types to java types.
   * It is also possible to map any string occuring
   * as a type to a class name.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Properties bindings_ = new Properties();

  private Document document_;

  /** A flag for delayed initialisation of main values */
  private boolean init = false;
  
  /**
   * A mapping from class names to SchemaClass objects.
   * This map does only contain classes from this project.
   */
  private Map<String,SchemaClass> map_ = new HashMap<String,SchemaClass>();

  /**
   * A mapping from enumeration names
   * to a list of all values of that enumeration.
   * This map does only contain enumerations from this project.
   */
  private Map<String,List<String>> enum_ = new HashMap<String,List<String>>();

  private Map<String, List<String>> enumPackage_ = new HashMap<String, List<String>>();
  
  /**
   * The project imported from the XML Schema.
   */
  private Project importProject_;

  private GlobalProperties global_;

  /**
   * A mapping from namespace prefixes
   * to its associated namespaces.
   *
   * Should never be <code>null</code>.
   */
  private final Properties nsPrefixProps_;
  
  private final String nsAcronymn_;

  /**
   * A mapping from objects that does not belong to the project
   * to be generated to its corresponding project names.
   */
  private final Map<String,Project> objectProjectProps_ = new HashMap<String,Project>();

  /**
   * The target namespace of the schema.
   */
  private final String targetNamespace_;

  /**
   *
   */
  private Map<String, List<Object>> props_ =
    new HashMap<String, List<Object>>();

  /**
   * Give access to the underlying JProject...
   * TODO: what isn't SchemaProject a Project extension?
   */
  private JProject jproject_;
  
  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * @param url the XML Schema file location.
   * @param mapping the mapping information.
   */
  public SchemaProject(URL url,
                       Properties mapping,
                       GlobalProperties globalProperties,
                       Project proj)
    throws ParserConfigurationException,
           SAXException, IOException, XSDException
  {
    nsPrefixProps_ = collectNamespacePrefixes(url);
    global_ = globalProperties;
    if (mapping != null) bindings_ = mapping;
    
    InputStream urlStream = url.openStream();
    try {
      InputSource in = new InputSource(urlStream);
      DocumentBuilderFactory dfactory = DocumentBuilderFactory.newInstance();
      dfactory.setNamespaceAware(true);
      document_ = dfactory.newDocumentBuilder().parse(in);
    } finally {
      urlStream.close();
    }
    xPath_ = new XPath(document_);
    Node schemaNode = xPath_.selectSingleNode(document_, "/xs:schema");
    if (schemaNode != null) {
      targetNamespace_ = xPath_.getNodeValue(schemaNode, "@targetNamespace");
      nsAcronymn_ = getNameSpaceAcronymn(nsPrefixProps_, targetNamespace_);
      LOGGER.info("XPath target name space = " + targetNamespace_);
    }
    else
    {	
    	targetNamespace_ = null;
    	nsAcronymn_ = null;
    	LOGGER.warning("Could not define target name space");
    }
    jproject_ = proj;
  }
  
  private void ensureInit() {
    if (!init) {
      init = true;
      try {
        doInit();
        System.out.println("Initialised okay for " + getName());
      }
      catch (XSDException e) {
        throw new GnastException(e);
      }
    }
  }
  
  private void doInit() throws XSDException {
    
    Node schemaNode = xPath_.selectSingleNode(document_, "/xs:schema");
    if (schemaNode != null) {
      String importNamespace =
        xPath_.getNodeValue(schemaNode, "xs:import/@namespace");      
      if (importNamespace != null) {
        importProject_ = global_.getProjectName(importNamespace);
        //System.err.println("Import package = " + importProject_.getAstPackage());
      }
      
      Node n;

      // collecting all enumerations
      NodeIterator nl = xPath_.selectNodeIterator(schemaNode,
                    "xs:simpleType[xs:restriction/@base = 'xs:string']");
      while ((n = nl.nextNode()) != null) {
        String enumName = xPath_.getNodeValue(n, "@name");
        List<String> enumValues = new ArrayList<String>();
        if (enumName == null) xPath_.getNodeValue(n.getParentNode(), "@name");
        // TODO error message if enumName == null
        NodeIterator valueIter =
          xPath_.selectNodeIterator(n, ".//xs:enumeration");
        Node valueNode;
        while ((valueNode = valueIter.nextNode()) != null) {
          enumValues.add(xPath_.getNodeValue(valueNode, "@value"));
        }
        enum_.put(enumName, enumValues);
    	//System.err.println("Added enum for " + getBasePackage() + " = " + enumName);
    	List<String> enums = null;
    	if (enumPackage_.containsKey(getBasePackage()))
    	{
    		enums = enumPackage_.get(getBasePackage());
    	}
    	else
    	{
    		enums = new ArrayList<String>();
        	enumPackage_.put(getBasePackage(), enums);
    	}
    	enums.add(enumName);
      }
      
      // collecting all Ast classes
      nl = xPath_.selectNodeIterator(schemaNode, "xs:element");
      while ((n = nl.nextNode()) != null) {
        SchemaClass c = new SchemaClass(n, global_);
        map_.put(c.getName(), c);
      }
      
      System.out.println("Enums       = " + enum_.toString());
      System.out.println("EnumPackage = " + enumPackage_.toString());
      
    }
    
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ************* ACCESSING SPECIAL SCHEMA NODES ***************

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
    String xPathExpr = "//xs:schema/xs:complexType[@name='" + name + "']";
    return xPath_.selectSingleNode(xPathExpr);
  }

  public String getPropertyBinding(Node node)
  {
    String xPathExpr = "./xs:annotation/xs:appinfo/jaxb:property/@name";
    return xPath_.getNodeValue(node, xPathExpr);
  }

  private String getGnastPackageXPathExpr()
  {
    return "//xs:schema/xs:annotation/xs:appinfo/"
      + "gnast:schemaBindings/gnast:package";
  }

  public String getTargetNamespace()
  {
    return targetNamespace_;
  }

  public String getJaxbGenPackage()
  {
    return xPath_.getNodeValue("//jaxb:package/@name");
  }

  public String getName()
  {
    return xPath_.getNodeValue("//gnast:schemaBindings/@name");
  }

  private String getPackageOffset(String packageName)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "/gnast:package[@id='"
                               + packageName
                               + "']/@name");
  }
  
  public JProject getProject()
  {
  	return jproject_;
  }
  
  public String getPackageDocumentation(String packageName)
  {
    String result =
      xPath_.getNodeValue(getGnastPackageXPathExpr()
                          + "/gnast:package[@id='"
                          + packageName
                          + "']/gnast:javadoc/text()");
    if (result != null) result = result.trim();
    return result;
  }

  public String getBasePackage()
  {
    return xPath_.getNodeValue(
          getGnastPackageXPathExpr() + "/@name");
  }

  public String getAstPackageOffset()
  {
    return getPackageOffset("ast");
  }

  public String getAstPackage()
  {
    return getBasePackage() + "." + getAstPackageOffset();
  }

  public String getImplPackageOffset()
  {
    return getPackageOffset("impl");
  }

  public String getImplPackage()
  {
    return getBasePackage() + "." + getImplPackageOffset();
  }

  public String getVisitorPackageOffset()
  {
    return getPackageOffset("visitor");
  }

  public String getVisitorPackage()
  {
    return getBasePackage() + "." + getVisitorPackageOffset();
  }

  public String getJaxbPackageOffset()
  {
    return getPackageOffset("jaxb");
  }

  public String getJaxbPackage()
  {
    return getBasePackage() + "." + getJaxbPackageOffset();
  }

  public String getDomPackageOffset()
  {
    return getPackageOffset("dom");
  }

  public String getDomPackage()
  {
    return getBasePackage() + "." + getDomPackageOffset();
  }

  public JObject getGenObject(String id)
  {
    String xPathExpr = "//*[@id='" + id + "']";
    Node node = xPath_.selectSingleNode(xPathExpr);
    if (node == null) {
      LOGGER.warning("Cannot find node with id " + id);
      return null;
    }
    String objectName = xPath_.getNodeValue(node, "@class");
    if (objectName == null) {
      LOGGER.warning("Node with id " + id + " doesn't have a class name");
      return null;
    }
    String packageName = getBasePackage() + "."
      + xPath_.getNodeValue(node, "../@name");
    
    return new JObjectImpl(objectName, packageName);
  }

  public String getClassName(String id)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='"
                               + id
                               + "']/@class");
  }

  public String getTemplate(String id)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='"
                               + id
                               + "']/@template");
  }

  public String getPackage(String id)
  {
    String xPathExpr = getGnastPackageXPathExpr()
      + "/gnast:package[gnast:generate[@id='" + id + "']]/@name";
    return xPath_.getNodeValue(xPathExpr);
  }

  // *********************** OTHERS ************************

  /**
   * Returns the namespace that corresponds to the given prefix.
   */
  protected String getNamespace(String prefix)
  {
    return nsPrefixProps_.getProperty(prefix);
  }

  /**
   * Returns the GnastClass with the given name.
   *
   * @param className the name of the GnastClass to be retrieved.
   *                  (it may contain the package name).
   * @return the GnastClass with that name, or <code>null</code>
   *         if a GnastClass with that name could not be found.
   * @czt.todo What about Term?
   * @czt.todo Should it really be possible to support names
   *           containing package info?
   */
  public JAstObject getAstClass(String className)
  {
    String methodName = "getAstClass";
    LOGGER.entering(CLASS_NAME, methodName, className);

    String[] blubb = className.split("\\.");
    String name = blubb[blubb.length - 1];
    JAstObject result = getAstClasses().get(name);
    if (result == null) {
      Project project = objectProjectProps_.get(name);
      if (project != null) {
        result = project.getAstObject(name);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  /**
   * <p>Returns a mapping from class names to SchemaClass objects.</p>
   */
  public Map<String, ? extends JAstObject> getAstClasses()
  {
    ensureInit();
    return map_;
  }

  /**
   * Returns a Map of all enumerations found in the given
   * XML schema file.
   */
  public Map<String,List<String>> getEnumerations()
  {
    ensureInit();
    return Collections.unmodifiableMap(enum_);
  }
  
  public Map<String, List<String>> getEnumerationsByPackage()
  {
	ensureInit();
	return Collections.unmodifiableMap(enumPackage_);
  }
  
  public boolean isKnownEnumeration(String type)
  {
	String pack = "";
	boolean result = getEnumerations().containsKey(type);
	if (!result)
	{
		Iterator<String> it = getEnumerationsByPackage().keySet().iterator();
		while (!result && it.hasNext())
		{	
			pack = it.next();
			result = getEnumerationsByPackage().get(pack).contains(type);
		}
	}
	if (!result && importProject_ != null)
	{
		result = importProject_.isKnownEnumeration(type);
		//if (result)System.out.println("Couldn't find Enum, looked into parent and found " 
		//							  + type + " " + importProject_.getName());
	}
	//if (result)
	//	System.out.println("Is enumeration " + type + " = " + pack);
	//else
	//	System.out.println("Couldn't find if " + type + " is enum in " + pack +
	//			" \n\twith importProj = " + importProject_.getClass().getName() +
	//			" \n\tnamed as   	  = "  + importProject_.getName());
	return result;
  }
  
  /**
   * For a given Enum type name given, returns its full name by looking up
   * the actual package of interest to add to the name. The package of interest
   * is either the JAXB or the AST package, as controlled by the given flag.
   * 
   * @param type Enum type name
   * @param asJaxb prepend JAXB or AST prefix 
   * @return
   */
  public String getFullEnumName(String type, boolean asJaxb)
  {
	boolean found = false;
	String result = type;
    if (isKnownEnumeration(type))
    {
    	// not very efficient because redoes the search, but that's okay for now.
    	Iterator<String> it = getEnumerationsByPackage().keySet().iterator();
		while (it.hasNext())
		{	
			String pack = it.next();
			if (getEnumerationsByPackage().get(pack).contains(type))
			{
				assert pack.equals(getBasePackage());
				result = (asJaxb ? getJaxbGenPackage() : getAstPackage()) + "." + type;
				found = true;
				System.out.println("Found full enum name = " + result + " for JProject AST = " + getProject().getAstPackage());
				break;
			}
		}
		
		if (!found && importProject_ != null)
		{
			result = importProject_.getFullEnumName(type, asJaxb);
		}
    }
    return result;
  }

  /**
   * Return the name of the imported project.
   */
  public Project getImportProject()
  {
    ensureInit();
    return importProject_;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  private String serialize(Node node)
  {
    if (node == null) return null;
    try {
      Transformer transformer = TRANSFORMER_FACTORY.newTransformer();
      transformer.setOutputProperty("omit-xml-declaration", "yes");
      StringWriter writer = new StringWriter();
      StreamResult result = new StreamResult(writer);
      NodeIterator iter = xPath_.selectNodeIterator(node, "* | text()");
      Node nextNode = iter.nextNode();
      while(nextNode != null) {
        DOMSource source = new DOMSource(nextNode);
        transformer.transform(source, result);
        nextNode = iter.nextNode();
      }
      writer.close();
      return writer.toString();
    }
    catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * <p>Collects all used namespace prefixes (defined via xmlns)
   * of an XML file into a map. The namespace prefix is used as
   * the key, its associated namespace is the value of the map.</p>
   *
   * <p>If the same prefix is used several times, only the last
   * occurrence is contained in the map.</p>
   *
   * @param url the location of the (XML) file to be searched.
   * @return a map from string representing a namespace prefix
   *         to string representing its associated namespace.
   */
  public static Properties collectNamespacePrefixes(URL url)
    throws IOException
  {
    final Properties result = new Properties();
    Pattern p =
      Pattern.compile("xmlns:[a-zA-Z]+[\\s]*\\=\\s*\\\"[^\\\"]*\\\"");
    BufferedReader reader = new BufferedReader(new InputStreamReader(url.openStream()));
    try {
      String seq = reader.readLine();
      while (seq != null) {
        Matcher m = p.matcher(seq);
        while (m.find()) {
          String s = m.group();
          String[] blubb = s.split("\"");
          Pattern p2 = Pattern.compile("xmlns:[a-zA-Z]+[^a-zA-Z]");
          Matcher m2 = p2.matcher(blubb[0]);
          if (m2.find()) {
            String string = m2.group();
            final int l = "xmlns:".length();
            result.setProperty(string.substring(l, string.length() - 1), blubb[1]);
          }
        }
        seq = reader.readLine();
      }
    } finally {
      reader.close();
    }
    LOGGER.info("Collecting properties for " + url.toString());
    LOGGER.info(result.toString());
    System.out.println("Collecting properties for " + url.toString());
    System.out.println(result.toString());	
    return result;
  }
  
  /**
   * This is the xmlns:??? property mathing the current targetNameSpace. 
   * That is, Z for Z, P for ZPattern, CT for CircusTime, CIRCUS for Circus, etc.
   * This is useful when generating GnAST code that requires different names to 
   * avoid FindBugs issue about confusing class names. 
   * @return
   */
  private static final String getNameSpaceAcronymn(Properties props, String ns)
  	throws XSDException
  {
	 assert props.containsValue(ns);
	 for(Object p : props.keySet())
	 {
		 if (p instanceof String && ns.equals(props.getProperty((String)p)))
		 {
			 return p.toString();
		 }
	 }
	 throw new XSDException("Couldn't find name space acronymn for " + ns + "\n\t" + props.toString());	 
  }

  /**
   * <p>This method asserts that there is at most one colon
   * in the given string.</p>
   *
   * <p>Note: This method updates private member variable
   * <code>objectProjectProps_</code>.
   *
   * @return ...
   *   and <code>null</code> if <code>string</code> is <code>null</code>.
   */
  public String removeNamespace(String string)
  {
    final String methodName = "removeNamespace";
    LOGGER.entering(CLASS_NAME, methodName, string);
    if (string == null) return null;
    try {
      String[] blubb = string.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
        LOGGER.exiting(CLASS_NAME, methodName, string);
        return string;
      }
      else {
        String prefix = blubb[0];
        String obj = blubb[1];
        String namespace = getNamespace(prefix);
        if (!namespace.equals("http://www.w3.org/2001/XMLSchema") &&
            !namespace.equals(targetNamespace_)) {
          Project project = global_.getProjectName(namespace);
          if (project == null) {
            String message =
              "Cannot find project that corresponds to prefix " + prefix;
            LOGGER.warning(message);
          }
          else {
            objectProjectProps_.put(obj, project);
            objectProjectProps_.put(obj + "Impl", project);
          }
        }
        LOGGER.exiting(CLASS_NAME, methodName, obj);
        return obj;
      }
    }
    catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * Returns the Java Object with that name.
   *
   * @return should never be <code>null</code>.
   */
  public JObject getObject(String type)
  {
    Project project = objectProjectProps_.get(type);
    if (project != null) {
      //System.err.println("getObject with project " + project.getName() + " for " + type);  
      JObject result = project.getObject(type);
	  //System.err.println("\tresult.getPackage()   = " + result.getPackage());
      //System.err.println("\tresult.getFullName()  = " + result.getFullName());
	  //System.err.println("\tresult.getName()      = " + result.getName());
	  //System.err.println("\tresult.getProject()   = " + result.getProject().getClass());
	  //System.err.println("\tresult.getProjectAST()= " + result.getProject().getAstPackage());
      return result;
    }
    String typePackage = "";
    //if (type.equals("JokerType"))System.err.println("getObject with no project for " + type);
    if (getAstClass(type) != null)
    {
    	//if (type.equals("JokerType"))System.err.println("\tgetAstClass(" + type + ") = " + getAstClass(type));
    	//if (type.equals("JokerType"))System.err.println("\t\tgetName       = " + getAstClass(type).getName());
    	//if (type.equals("JokerType"))System.err.println("\t\tgetPackage    = " + getAstClass(type).getPackage());
    	//if (type.equals("JokerType"))System.err.println("\t\tgetProperties = " + getAstClass(type).getProperties());
	    typePackage = getAstClass(type).getPackage();
	}    
    //if (type.equals("JokerType"))System.err.println("\tgetAstClasses()     = " + getAstClasses().keySet());
    //if (type.equals("JokerType"))System.err.println("\tobjectProjectProps_ = " + objectProjectProps_);
    //if (type.equals("JokerType"))System.err.println("\tprops_ 			  = " + props_.keySet());
    
    // we might not know whether the given type is within this
    // project ast/impl package, so pass it empty. but pass  the project?
    return new JObjectImpl(type, typePackage, getProject());
  }

  // ############################################################
  // ##################### INNER CLASSES ########################
  // ############################################################

  class SchemaClass extends JAstObjectImpl
  {
    /**
     * The name of this Schema class.
     */
    private String name_ = null;

    /**
     * Is this class abstract?
     */
    private boolean abstract_ = false;

    /**
     * The base class of this Schema class.
     */
    private String extends_ = null;

    /**
     * Properties for this Schema class.
     */
    private List<Object> properties_ = null;

    /**
     *
     */
    private String xsdType_ = null;

    /**
     * Javadoc documentation for this class.
     */
    private String javadoc_ = null;

    /**
     * Creates a new schema class from the node given.
     *
     * @param node  The XML Schema node from which all the neccessary
     *              information is extracted.
     */
    SchemaClass(Node node, GlobalProperties global)
      throws XSDException
    {
      super(global);
      // parsing the name
      name_ = xPath_.getNodeValue(node, "@name");
      if (name_ == null) {
        String message = "The name attribute of a global XML Schema "
          + "element, group, or type is missing: ";
        message += node.toString();
        throw new XSDException(message);
      }

      // parsing whether this class is abstract
      abstract_ = "true".equals(xPath_.getNodeValue(node, "@abstract"));

      // parsing the substitution group attribute
      extends_ =
        removeNamespace(xPath_.getNodeValue(node, "@substitutionGroup"));

      properties_ = new ArrayList<Object>();

      // parsing the type
      xsdType_ = xPath_.getNodeValue(node, "@type");
      if (xsdType_ == null) {
        String message = "The type attribute for " + name_
          + " is either missing or invalid.  "
          + "Are you using unnamed types?  "
          + "Unnamed types are currently not supported.";
        throw new XSDException(message);
      }

      // collecting properties
      properties_ = collectAllProperties(removeNamespace(xsdType_));

      if (extends_ == null) {
        extends_ = "Term";
      }

      // parsing javadoc
      String xPathExpr = "xs:annotation/xs:documentation";
      javadoc_ = serialize(xPath_.selectSingleNode(node, xPathExpr));
      if (javadoc_ != null) javadoc_ = javadoc_.trim();
    }

    public String getName()
    {
      return name_;
    }

    public String getJavadoc()
    {
      return javadoc_;
    }

    public JProject getProject()
    {
      return SchemaProject.this.getProject(); //null;
    }

    public boolean getNameEqualsType()
    {
      return xsdType_.endsWith(name_);
    }

    public String getImplName()
    {
      return getName() + "Impl";
    }

    public String getExtends()
    {
      return extends_;
    }
    
    public String getNSAcronymn()
    {
    	return nsAcronymn_;
    }

    public String getPackage()
    {
      return SchemaProject.this.getAstPackage();
    }
    
    public String getVisitorPackage()
    {
      return SchemaProject.this.getVisitorPackage();
    }

    public String getImplPackage()
    {
      return SchemaProject.this.getImplPackage();
    }
    
    public boolean isKnownEnumeration(String type)
    {	
      return SchemaProject.this.isKnownEnumeration(type);
    }
    
    public String getFullEnumName(String type, boolean asJaxb)
    {
    	return SchemaProject.this.getFullEnumName(type, asJaxb);	
    }

    public Map<String, List<String>> getEnumerationsByPackage()
    {
    	return SchemaProject.this.getEnumerationsByPackage();
    }

    public String getNamespace()
    {
      return SchemaProject.this.getTargetNamespace();
    }
    
    public JObject getObject(String type)
    {
      return SchemaProject.this.getObject(type);
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
        JAstObject c = getAstClasses().get(parent);
        if (c != null) {
          result = c.isInstanceOf(name);
        }
      }
      return result;
    }

    public String getImplExtends()
    {
      String methodName = "getExtendsImpl";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      String result = extends_ + "Impl";
      LOGGER.exiting(CLASS_NAME, methodName, result);
      return result;
    }

    public List<Object> getProperties()
    {
      String methodName = "getProperties";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      List<Object> erg = new Vector<Object>();
      erg.addAll(properties_);
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

    public List<Object> getInheritedProperties()
    {
      String methodName = "getInheritedProperties";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      List<Object> erg = null;
      String ext = getExtends();
      if (ext != null) {
        JAstObject c = getAstClass(ext);
        if (c != null) {
          erg = c.getAllProperties();
        }
        else if (ext.equals("Term")) {
          erg = new ArrayList<Object>();
        }
      }
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

//    /**
//     * Uses extends_ and name_ (in log messages and exceptions),
//     * so make sure these are set prior to calling this method.
//     *
//     * @throws NullPointerException if <code>node</code> is <code>null</code>.
//     */
//    private void parseProperties(Node node)
//      throws XSDException
//    {
//      String methodName = "parseProperties";
//      LOGGER.entering(CLASS_NAME, methodName, node);
//
//      if (node == null) {
//        NullPointerException e = new NullPointerException();
//        LOGGER.exiting(CLASS_NAME, methodName, e);
//        throw e;
//      }
//
//      LOGGER.fine("Properties for " + name_ + " are " + properties_);
//      LOGGER.exiting(CLASS_NAME, methodName);
//    }

    /**
     * Identifies all properties that are children of that node.
     * For instance, given an xs:complexType node, this method
     * returns a list of all properties associated with this type
     * (not included inherited properties).
     *
     * @czt.todo Should this method be static?
     */
    private List<Object> collectProperties(String name, Node node)
      throws XSDException
    {
      final String methodName = "collectProperties";
      LOGGER.entering(CLASS_NAME, methodName, node);

      List<Object> list = props_.get(name);
      if (list != null) {
        return list;
      }
      list = new ArrayList<Object>();
      String xpathexpr = ".//xs:element | .//xs:attribute";
      NodeIterator nl = null;
      try {
        nl = xPath_.selectNodeIterator(node, xpathexpr);
      }
      catch (Exception e) {
        LOGGER.fine("ERROR while getting the properties "
                    + "of a Schema class.");
        e.printStackTrace();
        throw new XSDException();
      }
      Node n;
      while ((n = nl.nextNode()) != null) {
        try {
          SchemaProperty prop = new SchemaProperty(n);
          LOGGER.finer("Found property " + prop);
          list.add(prop);
        }
        catch (XSDException e) {
          XSDException exception =
            new XSDException("Error while processing " + node.toString(), e);
          LOGGER.exiting(CLASS_NAME, methodName, exception);
          throw exception;
        }
      }
      props_.put(name, list);
      LOGGER.exiting(CLASS_NAME, methodName, list);
      return list;
    }

    public boolean getAbstract()
    {
      return abstract_;
    }

    /**
     * The search is stopped at extends_.
     *
     * @param typeName  the name of the complex type
     *                  where the search is started.
     * @throws NullPointerException if <code>typeName</code>
     *                  is <code>null</code>.
     * @czt.todo The collectAllProperties(typeName) method
     *           should get the namespace information as well
     *           since it is not guaranteed that the given type is
     *           defined within this project rather than in an
     *           imported project.
     * @czt.todo Currently, this method changes the member
     *           variable extends_ (when it finds a type whos
     *           name is Term).  This is very dangerous and
     *           unintuitive.  Think of a better way to handle
     *           this.
     */
    private List<Object> collectAllProperties(String typeName)
      throws XSDException
    {
      String methodName = "collectAllProperties";
      LOGGER.entering(CLASS_NAME, methodName, typeName);

      if (typeName == null) {
        NullPointerException e = new NullPointerException();
        LOGGER.exiting(CLASS_NAME, methodName, e);
        throw e;
      }

      List<Object> erg = new Vector<Object>();

      if (typeName.equals("Term")) {
        extends_ = "Term";
      }
      else if (! typeName.equals(extends_)) {
        Node startNode = getComplexTypeNode(typeName);
        if (startNode == null) {
          LOGGER.warning("Cannot find definition of complex type "
                         + typeName
                         + "; proceeding anyway. For SchemaClass " 
                         + name_ + " extends " + extends_);
          LOGGER.exiting(CLASS_NAME, methodName, erg);
          return erg;
        }

        erg.addAll(collectProperties(typeName, startNode));
        Node n = xPath_.selectSingleNode(startNode,
              "./xs:complexContent/xs:extension/@base");
        if (n != null && n.getNodeValue() != null) {
          String base = removeNamespace(n.getNodeValue());
          erg.addAll(collectAllProperties(base));
        }
      }
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

    public boolean isList()
    {
      if (getName().endsWith("List")) {
        List<Object> props = getAllProperties();
        return props.size() == 1 && ((SchemaProperty) props.get(0)).isList();
      }
      return false;
    }
  } // end SchemaClass




  /**
   * xs:element or xs:attribute.
   */
  class SchemaProperty
    extends JPropertyImpl
  {
    /**
     * The name of this property.
     *
     * @see #parseName(Node)
     */
    private String name_ = null;

    /**
     * The type of this property.
     *
     * @see #parseType(Node)
     */
    private String type_ = null;

    private String listType_ = null;

    private boolean attribute_ = false;

    private boolean isReference_ = false;

    SchemaProperty(Node node)
      throws XSDException
    {
      parseName(node);
      parseType(node);
      if (node.getLocalName().equals("attribute")) {
        attribute_ = true;
      }
    }

    public boolean getAttribute()
    {
      return attribute_;
    }

    /**
     * <p>Parses an xs:element or xs:attribute node
     * and sets the name of this property appropriatly.<p>
     *
     * <p>The rules are as follows:  If there is a jaxb property
     * customization,  take the value of the name attribute.  Otherwise,
     * take the value of the name attribute.  If this is not present
     * either, take the value of the ref attribute.  If non of the
     * above suceeds, throw an XSDException.</p>
     */
    /*@
      @ assignable name_;
      @*/
    private void parseName(Node node)
      throws XSDException
    {
      name_ = getPropertyBinding(node);
      if (name_ == null) name_ = xPath_.getNodeValue(node, "@name");
      if (name_ == null)
        name_ = removeNamespace(xPath_.getNodeValue(node, "@ref"));
      if (name_ == null) {
        String message = "Cannot generate a getter method "
          + "since there is neither a property customization, "
          + "a name attribute, nor a ref attribute "
          + "for the following node: ";
        message += node.toString();
        throw new XSDException(message);
      }
    }

    /**
     * <p>Parses an xs:element or xs:attribute node
     * and sets the type of this property appropriatly.<p>
     *
     * @czt.todo Check the value of attribute maxOccurs.  Currently,
     *           it is only checked whether it is present or not.
     * @czt.todo Check the value of attribute minOccurs as well.
     */
    /*@
      @ assignable isReference_;
      @ assignable listType_;
      @ assignable type_;
      @*/
    public void parseType(Node node)
      throws XSDException
    {
      if (parseRefAttribute(node) || parseTypeAttribute(node)) {
        String maxOccurs = xPath_.getNodeValue(node, "@maxOccurs");
        if ("unbounded".equals(maxOccurs) ||
            "2".equals(maxOccurs)) {
          listType_ = type_;
          type_ = "java.util.List<" + listType_ + ">";
        }
        return;
      }
      String message = "There is neither a type nor a ref attribute "
        + "for the following node:\n         " + node.toString();
      throw new XSDException(message);
    }

    /**
     * Returns <code>true</code> iff the given node has a ref attribute.
     */
    /*@
      @ assignable type_;
      @ assignable isReference_;
      @*/
    private boolean parseRefAttribute(Node node)
    {
      String ref = xPath_.getNodeValue(node, "@ref");
      boolean refAttributePresent = ref != null;
      if (refAttributePresent) {
        type_ = removeNamespace(ref);
        isReference_ = true;
      }
      return refAttributePresent;
    }

    /**
     * Returns <code>true</code> iff the given node has a type attribute.
     */
    /*@
      @ assignable type_;
      @*/
    private boolean parseTypeAttribute(Node node)
    {
      String typeAttr = removeNamespace(xPath_.getNodeValue(node, "@type"));
      boolean typeAttributePresent = typeAttr != null;
      if (typeAttributePresent) {
        type_ = (String) bindings_.get(typeAttr);
        if (type_ == null) {
          type_ = typeAttr;
        }
      }
      return typeAttributePresent;
    }
    
    public boolean isKnownEnumeration(String type)
    {	
    	boolean result = SchemaProject.this.isKnownEnumeration(type);
    	//if (result)System.out.println("Is known enumeration " + type + "? =" + result);
      return result;
    }
    
    public String getFullEnumName(boolean asJaxb)
    {
    	assert isEnum();
      return SchemaProject.this.getFullEnumName(name_, asJaxb);	
    }

    public String getName()
    {
    	//if (isEnum())
    	//	return getFullEnumName();
    	//else
    		return name_;
    }

    public JObject getType()
    {
      return SchemaProject.this.getObject(type_);
    }

    public JObject getListType()
    {
      if (listType_ != null) {
        return SchemaProject.this.getObject(listType_);
      }
      return SchemaProject.this.getObject("java.lang.Object");
    }

    public boolean isReference()
    {
      return isReference_;
    }

    public boolean isList()
    {
      return listType_ != null;
    }
    
    public boolean isEnum()
    {
      return isKnownEnumeration(name_);	
    }
  } // end class SchemaAttribute
} // end class SchemaProject

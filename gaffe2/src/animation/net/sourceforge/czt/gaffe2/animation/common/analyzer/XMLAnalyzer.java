
package net.sourceforge.czt.gaffe2.animation.common.analyzer;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.DefaultVariableExtractor;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.SchemaExtractionVisitor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;

/**
 * @author Linan Zhang
 *
 */
public class XMLAnalyzer implements Analyzer
{
  private URL specURL;

  private List<ConstDecl> schemaMap;

  private VariableExtractor ve;

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#initialize(java.io.File)
   */
  public void initialize(File specFile)
  {
    try {
      specURL = specFile.toURL();
      schemaMap = null;
      ve = new DefaultVariableExtractor();
    } catch (MalformedURLException muex) {
      muex.printStackTrace();
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSpecURL()
   */
  public URL getSpecURL()
  {
    return this.specURL;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaNames()
   */
  public Set<String> getSchemaNames()
  {
    try {
      HashSet<String> result = new HashSet<String>();
      JaxbXmlReader reader = new JaxbXmlReader();
      Term term = reader.read(specURL.openStream());
      SchemaExtractionVisitor extracter = new SchemaExtractionVisitor();
      schemaMap = extracter.getSchemas(term);
      for (ConstDecl schema : schemaMap) {
        result.add(schema.getDeclName().toString());
      }
      return result;
    } catch (IOException ioex) {
      ioex.printStackTrace();
      System.out.println("Reading Schema Error!");
      return null;
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaType(java.lang.String)
   */
  public String getSchemaType(String schemaName)
  {
    int stateSize = this.getVariableMap(schemaName, "state").keySet().size();
    int primedSize = this.getVariableMap(schemaName, "primed").keySet().size();
    int inputSize = this.getVariableMap(schemaName, "input").keySet().size();
    int outputSize = this.getVariableMap(schemaName, "output").keySet().size();
    if (stateSize > 0 && primedSize == 0 && inputSize == 0 && outputSize == 0) {
      return "State";
    }
    else if (stateSize == 0 && primedSize > 0 && inputSize == 0
        && outputSize == 0) {
      return "Initial";
    }
    else {
      return "Operation";
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaContent(java.lang.String)
   */
  public String getSchemaContent(String schemaName)
  {
    ConstDecl schema = findSchemaByName(schemaName);
    Expr content = schema.getExpr();
    return content.toString();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getVariableMap(java.lang.String, java.lang.String)
   */
  public HashMap<String, Expr> getVariableMap(String schemaName,
      String variableType)
  {
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    Map<DeclName, VarDecl> zMap = new HashMap<DeclName, VarDecl>();
    ConstDecl schema = findSchemaByName(schemaName);
    if (schema != null) {
      if (variableType.equals("state")) {
        zMap = ve.getStateVariables(schema);
      }
      else if (variableType.equals("input")) {
        zMap = ve.getInputVariables(schema);
      }
      else if (variableType.equals("output")) {
        zMap = ve.getOutputVariables(schema);
      }
      for (DeclName declName : zMap.keySet()) {
        VarDecl varDecl = zMap.get(declName);
        result.put(declName.toString(), varDecl.getExpr());
        System.out.println(declName.toString() + " "
            + varDecl.getExpr().toString());
      }
    }
    else {
      System.out.println("Extract variable from schema Error!");
    }
    return result;
  }

  /**
   * @param name
   * @return
   */
  private ConstDecl findSchemaByName(String name)
  {
    for (ConstDecl schema : schemaMap) {
      DeclName declName = schema.getDeclName();
      if (declName.toString().equals(name)) {
        return schema;
      }
    }
    return null;
  }
}

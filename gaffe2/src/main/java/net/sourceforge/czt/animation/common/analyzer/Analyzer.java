
package net.sourceforge.czt.animation.common.analyzer;

import java.io.File;
import java.net.URL;
import java.util.HashMap;
import java.util.Set;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public interface Analyzer
{
  /** 
   * First initialize the analyzer to let it know which
   * spec it is working on, but it only needs to know
   * how many schemas are there and their names.
   */
  public void initialize(File specFile);

  /** For initialize Evaluator
   * 
   * @return the URL of the specfication
   */
  public URL getSpecURL();

  /** For ui to know how many and what are their names
   * 
   * @return the set of schema Names
   */
  public Set<String> getSchemaNames();

  /** For ui to get default schema type
   * 
   * @param schemaName 
   * @return the type of the schema
   */
  public String getSchemaType(String schemaName);

  /** For toolTip texts
   * 
   * @param schemaName 
   * @return the content of the schema
   */
  public String getSchemaContent(String schemaName);

  /** Return a variable map frome a schema  (schemaName))
   * The map contains information of 
   * variable name -> an new instance of expr
   * 
   * @param schemaName
   * @param variableType one of (state, primed, input, output)
   * @return
   */
  public HashMap<String, Expr> getVariableMap(String schemaName,
      String variableType);

}

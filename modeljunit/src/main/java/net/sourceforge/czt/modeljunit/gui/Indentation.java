/**
 * @author rong
 * This class is for generating code. 
 * Every line has an indentation at the beginning of the line.
 * The wrap method could calculate the indentation and uses the
 * shrink or goFuther to adjust the indentation by checking whether
 * the input string includes '{' or '}'.
 * */
package net.sourceforge.czt.modeljunit.gui;

public class Indentation
{
  private static final String INDENTATION = "  ";
  private static String m_strIndentation = new String();
  public static final String SEP = System.getProperty("line.separator");
  
  protected static void goFurther()
  { m_strIndentation = m_strIndentation.concat(INDENTATION); }
  protected static void shrink()
  {
    m_strIndentation = 
      m_strIndentation.substring(
          0,
          m_strIndentation.length()- INDENTATION.length()
          );
  }
  
  public static String wrap(String str)
  {
    int front = str.indexOf('{');
    int rear = str.indexOf('}');
    if(front>=0)
    {
      str = m_strIndentation + str;
      goFurther();
    }
    if(rear>=0)
    {
      shrink();
      str = m_strIndentation + str;
    }
    if(front < 0 && rear <0)
      str = m_strIndentation + str;
    str += SEP;
    return str;
  }
}

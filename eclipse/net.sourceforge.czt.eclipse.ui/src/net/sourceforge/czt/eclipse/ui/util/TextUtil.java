package net.sourceforge.czt.eclipse.ui.util;

import net.sourceforge.czt.text.Position;

/**
 * @author Andrius Velykis
 */
public class TextUtil
{

  public static Position cztPos(org.eclipse.jface.text.Position jfacePos)
  {
    return new Position(jfacePos.getOffset(), jfacePos.getLength());
  }

  public static org.eclipse.jface.text.Position jfacePos(Position cztPos)
  {
    return new org.eclipse.jface.text.Position(cztPos.getOffset(), cztPos.getLength());
  }

}

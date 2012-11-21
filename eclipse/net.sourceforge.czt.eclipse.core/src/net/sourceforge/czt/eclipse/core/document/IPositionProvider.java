package net.sourceforge.czt.eclipse.core.document;

import net.sourceforge.czt.text.Position;


public interface IPositionProvider<T>
{
  public Position getPosition(T obj);
}

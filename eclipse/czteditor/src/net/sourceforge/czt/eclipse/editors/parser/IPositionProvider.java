package net.sourceforge.czt.eclipse.editors.parser;

import org.eclipse.jface.text.Position;

public interface IPositionProvider<T>
{
  public Position getPosition(T obj);
}

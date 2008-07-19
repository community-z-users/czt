package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Font;

import org.apache.commons.collections15.Transformer;

public class EdgeFontTransformer<V, E> implements Transformer<Object, Font> {
	public Font transform(Object o){
		return new Font("Arial", Font.PLAIN, 12);
	}
}

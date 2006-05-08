package net.sourceforge.czt.eclipse.outline;

import net.sourceforge.czt.eclipse.util.CZTPluginImages;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

/**
 * @author Chengdong Xu
 */
public class OutlineLabelProvider extends LabelProvider {
	
	private static final Image SPECIFICATION_ICON= CZTPluginImages.get(CZTPluginImages.IMG_SPECIFICATION);
	private static final Image DEFAULT_ICON = CZTPluginImages.get("sample.gif");
	
	public OutlineLabelProvider() {
		super();
	}
	
	/**
	 * @see ILabelProvider#getText
	 */
	public String getText(Object element) {
		if (! (element instanceof CztSegment)) 
			return super.getText(element);
		
		CztSegment segment = (CztSegment) element;
		return segment.getName();
	}
	
	
	/**
	 * @see ILabelProvider#getImage
	 */	
	public Image getImage(Object element) {
		return PlatformUI.getWorkbench().
			getSharedImages().getImage(ISharedImages.IMG_OBJ_ELEMENT);
//		if (! (element instanceof CztSegment))
//			return super.getImage(element);
		
//		CztSegment segment = (CztSegment) element;
		
//		if (segment instanceof Spec)
//			return SPECIFICATION_ICON;
		
//		return DEFAULT_ICON;
	}	
}

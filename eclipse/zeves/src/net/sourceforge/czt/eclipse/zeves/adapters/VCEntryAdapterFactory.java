package net.sourceforge.czt.eclipse.zeves.adapters;

import net.sourceforge.czt.eclipse.vcg.views.VCEntry;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.views.IZEvesElement;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IAdapterFactory;

public class VCEntryAdapterFactory implements IAdapterFactory {

	@Override
	public Object getAdapter(Object adaptableObject, 
			@SuppressWarnings("rawtypes") Class adapterType) {
		
		if (adapterType == IZEvesElement.class) {
			return new VCEntryElement((VCEntry) adaptableObject);
		}
		
		return null;
	}

	@Override
	public Class<?>[] getAdapterList() {
		return new Class<?>[] { IZEvesElement.class };
	}
	
	private static class VCEntryElement implements IZEvesElement {
		
		private final VCEntry entry;

		public VCEntryElement(VCEntry entry) {
			this.entry = entry;
		}

		@Override
		public String getDescription() {
			return "VC: " + entry.getVCName();
		}

		@Override
		public Object loadContents(ZEvesApi api, Markup markup) throws ZEvesException {
			
			if (markup == null) {
				markup = entry.getEditor().getMarkup();
			}
			
			return ZEvesResultConverter.printResult(entry.getSectionManager(),
					entry.getSectionName(), entry.getVCPara(), markup, 80);
		}
		
	}

}

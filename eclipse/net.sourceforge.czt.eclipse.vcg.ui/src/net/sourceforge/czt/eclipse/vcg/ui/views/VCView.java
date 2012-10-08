package net.sourceforge.czt.eclipse.vcg.ui.views;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;

import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.IPage;
import org.eclipse.ui.part.MessagePage;
import org.eclipse.ui.part.PageBook;
import org.eclipse.ui.part.PageBookView;


/**
 * @author Andrius Velykis
 */
public class VCView extends PageBookView {

	private final Map<IPage, String> pageMessages = new HashMap<IPage, String>();
	
	@Override
	protected IPage createDefaultPage(PageBook book) {
		MessagePage messagePage = new MessagePage();
		initPage(messagePage);
		messagePage.setMessage("Verification conditions are generated for the active Z editor.");
		messagePage.createControl(book);
		return messagePage;
	}

	@Override
	protected PageRec doCreatePage(IWorkbenchPart part) {
		VCPage vcPage = new VCPage(this, (IZEditor) part);
		initPage(vcPage);
		vcPage.createControl(getPageBook());
		return new PageRec(part, vcPage);
	}

	@Override
	protected void doDestroyPage(IWorkbenchPart part, PageRec pageRecord) {
		pageMessages.remove(pageRecord.page);
		pageRecord.page.dispose();
	}

	@Override
	protected IWorkbenchPart getBootstrapPart() {
		IWorkbenchPage page = getSite().getPage();
		if (page != null) {
			// check whether the active part is important to us
			IWorkbenchPart activePart = page.getActivePart();
			return isImportant(activePart) ? activePart : null;
		}
		return null;
	}

	@Override
	protected boolean isImportant(IWorkbenchPart part) {
		return part instanceof IZEditor;
	}

	void setViewMessage(IPage page, String message) {
		pageMessages.put(page, message);
		if (page == getCurrentPage()) {
			super.setContentDescription(message);
		}
	}

	@Override
	protected void showPageRec(PageRec pageRec) {
		super.showPageRec(pageRec);
		// upon page show, update the message
		String message = pageMessages.get(pageRec.page);
		if (message == null) {
			message = "";
		}
		
		super.setContentDescription(message);
	}
	
}

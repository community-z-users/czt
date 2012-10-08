package net.sourceforge.czt.eclipse.vcg.ui.views;

import net.sourceforge.czt.vcg.util.AbstractVCNameFactory;
import net.sourceforge.czt.vcg.z.feasibility.FSBVCNameFactory;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityPropertyKeys;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;

public class SectionVCNameFactory extends AbstractVCNameFactory implements FSBVCNameFactory {
	
	private final ZSect section;
	private final String vcSectionSuffix;
	
	public SectionVCNameFactory(ZSect section) {
		this(section, "_vc");
	}
	
	public SectionVCNameFactory(ZSect section, String vcSectionSuffix) {
		super();
		this.section = section;
		this.vcSectionSuffix = vcSectionSuffix;
	}

	@Override
	public String getVCSectionName(String originalSectName) {
		return originalSectName + vcSectionSuffix;
	}

	@Override
	public String getSigSchemaName(String schName) {
		return schName + FeasibilityPropertyKeys.VCG_FEASIBILITY_SIGSCHEMA_SUFFIX;
	}

	@Override
	protected String getAxDefName(AxPara para) {
		assert isAxiom(para);
		assert section.getZParaList().contains(para);
		return getSectionName() + "_axiom" + getParaIndex(para, true);
	}

	@Override
	protected String getGenericName(Para para) {
		assert section.getZParaList().contains(para);
		return getSectionName() + "_vc" + getParaIndex(para, false);
	}

	@Override
	protected String getVCName(Para para, String paraName, String vcType) {
		
		if (vcType == null) {
			vcType = "vc";
		}
		
		return paraName + "_" + vcType;
	}

	private String getSectionName() {
		String sectionName = section.getName();
		if (sectionName == null) {
			sectionName = "";
		}
		
		return sectionName;
	}
	
	private boolean isAxiom(Para para) {
		return ZUtils.isAxPara(para) && ((AxPara) para).getBox().equals(Box.AxBox);
	}
	
	private int getParaIndex(Para axPara, boolean axiomsOnly) {
		
		int index = 1;
		
		for (Para para : section.getZParaList()) {
			
			if (para == axPara) {
				return index;
			}
			
			if (!axiomsOnly || isAxiom(para)) {
				index++;
			}
		}
		
		throw new IllegalStateException();
	}

}

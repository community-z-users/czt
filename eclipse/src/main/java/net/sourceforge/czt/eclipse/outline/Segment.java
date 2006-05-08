package net.sourceforge.czt.eclipse.outline;

import javax.swing.Icon;

/**
 * @author Chengdong Xu
 */
public class Segment {
	private String name_ = null;
	private String description_ = null;
	private Icon icon_ = null;
	
	public Segment(String name) {
		name_ = description_ = name;
	}
	
	public Segment(String name, String description) {
		name_ = name;
		description_ = description;
	}
	
	public Segment(String name, String description, Icon icon) {
		name_ = name;
		description_ = description;
		icon_ = icon;
	}
	
	public String getName() {
		return name_;
	}
	
	public void setName(String name) {
		name_ = name;
	}
	
	public String getDescription() {
		return description_;
	}
	
	public void setDescription(String description) {
		description_ = description;
	}
	
	public String toString() {
		return name_;
	}
}

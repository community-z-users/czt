package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;
import java.util.Vector;

import javax.swing.*;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.JTableHeader;
import javax.swing.table.TableColumn;

public class PanelResultViewer extends JPanel{

	class ColumnInformation {
		public String m_title;
		public int m_width;
		public int m_alignment;
		public ColumnInformation(String title, int width, int alignment) {
			m_title = title;
			m_width = width;
			m_alignment = alignment;
		}
	}
	class ResultTableModelInstance extends AbstractTableModel {
		public final  ColumnInformation m_columns[] = {
			new ColumnInformation( "Type", 30, JLabel.LEFT ),
			new ColumnInformation( "Class name", 60, JLabel.LEFT ),
			new ColumnInformation( "Description", 100, JLabel.RIGHT ),
			new ColumnInformation( "Location", 60, JLabel.RIGHT ),
			new ColumnInformation( "Path", 60, JLabel.RIGHT )
		};
		protected Vector<ResultDetails> m_vector; 

		public ResultTableModelInstance(){
			m_vector = new Vector<ResultDetails>();
			clearData();
		}
		public void clearData(){
			m_vector.removeAllElements();
			//m_vector.add(new ResultDetails("A","B","C","D","E"));
		}
		public void addData(ResultDetails rd){
			m_vector.add(rd);
		}
		@Override
		public int getColumnCount() { return m_columns.length; }

		@Override
		public int getRowCount() { return m_vector==null ? 0 : m_vector.size(); }
		
		@Override
		public String getColumnName(int col) { return m_columns[col].m_title; }
		
		@Override
		public Object getValueAt(int rowIndex, int columnIndex) {
			if (rowIndex < 0 || rowIndex >= getRowCount())
				return null;
			ResultDetails row = m_vector.get(rowIndex);
			switch(columnIndex)
			{
			case 0: return row.strType;
			case 1: return row.strName;
			case 2: return row.strDescription;
			case 3: return row.strLocation;
			case 4: return row.strPath;
			}
			return null;
		}
		@Override
		public boolean isCellEditable(int nRow, int nCol) { return false; }
		public String getTitle(){ return "Result table";}
		
	}

	private static PanelResultViewer m_panelRV;
		
	private Vector<ResultDetails> m_resultData;
	private JTable m_table;
	private ResultTableModelInstance m_columeModel;
	
	public ResultTableModelInstance getTableModel(){ return m_columeModel; }
		
	public static PanelResultViewer createResultViewer(){
		if(m_panelRV==null)
			m_panelRV = new PanelResultViewer();
		return m_panelRV;
	}
	private PanelResultViewer(){
		m_resultData = new Vector<ResultDetails>();
		m_table = new JTable();
		m_table.setAutoCreateColumnsFromModel(false);
		m_columeModel = new ResultTableModelInstance();
		m_table.setModel(m_columeModel);
		
		for (int i = 0; i < m_columeModel.getColumnCount(); i++) {
			DefaultTableCellRenderer render = new DefaultTableCellRenderer();
			render.setHorizontalAlignment(
					m_columeModel.m_columns[i].m_alignment);
			render.setText(m_columeModel.m_columns[i].m_title);
			TableColumn column = new TableColumn(i,
					m_columeModel.m_columns[i].m_width, render, null);
			m_table.addColumn(column);
			}
		
		JTableHeader header = m_table.getTableHeader();
		header.setUpdateTableInRealTime(false);
		
		JScrollPane ps = new JScrollPane();
		m_table.setFillsViewportHeight(true);
		ps.getViewport().setBackground(m_table.getBackground());
		ps.getViewport().add(m_table);
		
		setLayout(new BorderLayout());
		add(m_table.getTableHeader(), BorderLayout.PAGE_START);
		add(ps, BorderLayout.CENTER);
		
	}
	public void updateResult()
	{
		
	}
}

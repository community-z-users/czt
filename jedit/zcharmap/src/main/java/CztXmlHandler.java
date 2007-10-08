import java.util.ArrayList;
import java.util.List;

import com.microstar.xml.*;

public class CztXmlHandler extends HandlerBase
{
  private List<List<Object>> table_ = new ArrayList<List<Object>>();
  private List<Object> row_;
  private String name_;
  private String unicode_;
  private String latex_;
  private String description_;

  public List<List<Object>> getList()
  {
    return table_;
  }

  public void attribute(String name, String value, boolean isSpecified)
  {
    if ("HEADING".equalsIgnoreCase(name)) {
      row_ = new ArrayList<Object>();
      row_.add(value);
    }
    else if ("NAME".equalsIgnoreCase(name)) {
      name_ = value;
    }
    else if ("UNICODE".equalsIgnoreCase(name)) {
      unicode_ = value;
    }
    else if ("LATEX".equalsIgnoreCase(name)) {
      latex_ = value;
    }
    else if ("DESCRIPTION".equalsIgnoreCase(name)) {
      description_ = value;
    }
  }

  public void endElement(String name)
  {
    if ("ITEM".equalsIgnoreCase(name)) {
      if (unicode_ == null) unicode_ = name_;
      row_.add(new ZChar(name_, unicode_, latex_, description_));
      name_ = unicode_ = latex_ = description_ = null;
    }
    else if ("ROW".equalsIgnoreCase(name)) {
      table_.add(row_);
    }
  }
}

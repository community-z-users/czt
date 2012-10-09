package net.sourceforge.czt.specreader;

import java.util.List;

/**
 * Records the details of a Z section.
 * 
 * @author ian
 */
public final class ZSection extends Section
{
  /** Section header (name and parents) */
  private HeaderBlock header_;

  /** Mark-up directives, in original order */
  private List<MarkupBlock> markups_;

  /** Paragraphs, in original order */
  private List<ParaBlock> paras_;

  /**
   * Constructs a Z section.
   * 
   * @param pathname path to file from which section was read
   * @param isBufferingWanted whether to buffer whole section's text in memory
   * @param header section header (name and parents)
   * @param markups mark-up directives, in original order
   * @param paras paragraphs, in original order
   */
  public ZSection(Pathname pathname, boolean isBufferingWanted, HeaderBlock header, List<MarkupBlock> markups, List<ParaBlock> paras)
  {
    super(pathname, isBufferingWanted);
    header_ = header;
    markups_ = markups;
    paras_ = paras;
  }

  /**
   * Projects the header field.
   * 
   * @return section header (name and parents)
   */
  public HeaderBlock getHeader()
  {
    return header_;
  }

  /**
   * Returns the text of the section,
   * preceded by a %%Zfile directive to say where the text came from.
   * Mark-up directives are positioned immediately following
   * the section header, and informal paragraphs are optionally elided.
   */
  @Override
  public String toString()
  {
    final StringBuilder stringBuilder = initializeWriter();
    blockAppend(stringBuilder, header_);
    for (MarkupBlock markupBlock : markups_) {
      blockAppend(stringBuilder, markupBlock);
    }
    for (ParaBlock paraBlock : paras_) {
      blockAppend(stringBuilder, paraBlock);
    }
    final String result = stringBuilder.toString();
    finalizeWriter();
    return result;
  }
}

package net.sourceforge.czt.text;

/**
 * Positions describe text ranges of a document. The text range is specified by an offset and a
 * length.
 * <p>
 * This is an immutable value object.
 * 
 * @author Andrius Velykis
 */
public class Position
{

  /** The offset of the position */
  public final int offset;

  /** The length of the position */
  public final int length;

  /**
   * Creates a new position with the given offset and length 0.
   * 
   * @param offset
   *          the position offset, must be >= 0
   */
  public Position(int offset)
  {
    this(offset, 0);
  }

  /**
   * Creates a new position with the given offset and length.
   * 
   * @param offset
   *          the position offset, must be >= 0
   * @param length
   *          the position length, must be >= 0
   */
  public Position(int offset, int length)
  {

    if (offset < 0) {
      throw new IllegalArgumentException("Negative offset");
    }

    if (length < 0) {
      throw new IllegalArgumentException("Negative length");
    }

    this.offset = offset;
    this.length = length;
  }

  @Override
  public int hashCode()
  {
    final int prime = 31;
    int result = 1;
    result = prime * result + length;
    result = prime * result + offset;
    return result;
  }

  @Override
  public boolean equals(Object obj)
  {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    Position other = (Position) obj;
    if (length != other.length)
      return false;
    if (offset != other.offset)
      return false;
    return true;
  }

  /**
   * Returns the length of this position.
   * 
   * @return the length of this position
   */
  public int getLength()
  {
    return length;
  }

  /**
   * Returns the offset of this position.
   * 
   * @return the offset of this position
   */
  public int getOffset()
  {
    return offset;
  }

  /**
   * Calculates the end offset of this position.
   * 
   * @return the end offset of this position (point after the range).
   */
  public int getEndOffset()
  {
    return offset + length;
  }

  /**
   * Checks whether the intersection of the given text range and the text range represented by
   * this position is empty or not.
   * 
   * @param rangeOffset
   *          the offset of the range to check
   * @param rangeLength
   *          the length of the range to check
   * @return {@code true} if intersection is not empty
   */
  public boolean overlapsWith(int rangeOffset, int rangeLength)
  {

    // take inclusive values
    int end = rangeOffset + rangeLength - 1;
    int thisEnd = offset + length - 1;

    return (this.offset <= end) && (thisEnd >= rangeOffset);
  }

  @Override
  public String toString()
  {
    return "Position(" + offset + (length > 0 ? "+" + length : "") + ")";
  }

  /**
   * Static factory method to create a position based on its start and end offsets.
   * 
   * @param start
   *          the start offset of the position
   * @param end
   *          the end offset of the position
   * @return new position with the given start and end offsets
   */
  public static Position createStartEnd(int start, int end)
  {
    return new Position(start, end - start);
  }

}

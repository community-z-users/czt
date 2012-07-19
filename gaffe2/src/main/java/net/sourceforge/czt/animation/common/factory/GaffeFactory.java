
package net.sourceforge.czt.animation.common.factory;

import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.analyzer.ZLiveAnalyzer;
import net.sourceforge.czt.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.animation.common.evaluator.ZLiveEvaluator;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class GaffeFactory
{
  private static ZLive zLive = new ZLive();                    // Hold the ZLive Ref

  private static Analyzer analyzer = new ZLiveAnalyzer();      // Hold the Analyzer Ref

  private static Evaluator evaluator = new ZLiveEvaluator();   // Hold the Evaluator Ref

  /**
   * No instance, solid
   */
  private GaffeFactory()
  {
  }

  /**
   * @return an selected implementation of Analyzer
   */
  public static Analyzer getAnalyzer()
  {
    return analyzer;
  }

  /**
   * @return an selected implementation of Evaluator
   */
  public static Evaluator getEvaluator()
  {
    return evaluator;
  }

  /**
   * @return the factory inside ZLive
   */
  public static Factory getFactory()
  {
    return zLive.getFactory();
  }

  /**
   * @return the zLive ref uniquely
   */
  public static ZLive getZLive()
  {
    return zLive;
  }
}

/**
Copyright (C) 2007 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.modeljunit;

import java.util.Random;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;

public abstract class Tester
{
  public static final long FIXEDSEED = 123456789L;

  /**
   * The model from which tests will be generated.
   */
  protected Model model_;

  /**
   *  A Random number generator for use in test generation.
   */
  protected Random rand_ = new Random(FIXEDSEED);

  /**
   *  Create a test generator for the given model.
   * @param model  Must be non-null.
   */
  public Tester(Model model)
  {
    assert model != null;
    model_ = model;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public Tester(FsmModel fsm)
  {
    this(new Model(fsm));
  }

  /**
   * @return The model that is driving the test generation.
   */
  public Model getModel()
  {
    return model_;
  }

  /** Get the random number generator that is used for test generation. */
  public Random getRandom()
  {
    return rand_;
  }

  /** This allows you to specify a random number generator.
   *  The default is to use new Random(FIXEDSEED), so that test
   *  generation is repeatable (that is, each instance of this class
   *  will generate the same test sequences).
   *
   * @param rand  A non-null instance of Random.
   */
  public void setRandom(Random rand)
  {
    rand_ = rand;
  }

  /**
   *  A convenience method for adding listeners and coverage metrics.
   *  This is equivalent to getModel().addListener(name, listener).
   *
   *  @param name      A name for this listener.  Typically listener.getName()
   *  @param listener  A ModelListener (or CoverageMetric) object.
   */
  public void addListener(String name, ModelListener listener)
  {
    model_.addListener(name, listener);
  }

  /**
   *  A convenience method that adds the metric with the name metric.getName().
   * @param metric  Must be non-null.
   */
  public void addCoverageMetric(CoverageMetric metric)
  {
    model_.addListener(metric.getName(), metric);
  }

  public void reset()
  {
    model_.doReset();  // a user-requested reset
  }

  /** Generate one more test step in the current sequence.
   *  This may reset and start a new test sequence if necessary.
   */
  public abstract void generate();

  /** Generate some test sequences, with the given total length.
   *  The default implementation of this just calls generate()
   *  length times.
   *
   * @param length
   */
  public void generate(int length)
  {
    for (int i=0; i<length; i++)
      generate();
  }
}

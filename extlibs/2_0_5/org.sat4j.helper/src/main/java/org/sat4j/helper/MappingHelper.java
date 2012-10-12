/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 * 
 * Based on the original MiniSat specification from:
 * 
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 * 
 *******************************************************************************/
package org.sat4j.helper;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * Helper class intended to make life easier to people to feed a sat solver
 * programmatically.
 * 
 * @author daniel
 * 
 * @param <T>
 *            The class of the objects to map into boolean variables.
 */
public class MappingHelper<T> {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private final Map<T, Integer> mapToDimacs = new HashMap<T, Integer>();
	private final IVec<T> mapToDomain;
	final ISolver solver;

	public MappingHelper(ISolver solver) {
		this.solver = solver;
		mapToDomain = new Vec<T>();
		mapToDomain.push(null);
	}

	int getIntValue(T thing) {
		Integer intValue = mapToDimacs.get(thing);
		if (intValue == null) {
			intValue = mapToDomain.size();
			mapToDomain.push(thing);
			mapToDimacs.put(thing, intValue);
		}
		return intValue;
	}

	public IVec<T> getSolution() {
		int[] model = solver.model();
		IVec<T> toInstall = new Vec<T>();
		for (int i : model) {
			if (i > 0) {
				toInstall.push(mapToDomain.get(i));
			}
		}
		return toInstall;
	}

	public boolean getBooleanValueFor(T t) {
		return solver.model(getIntValue(t));
	}

	public boolean hasASolution() throws TimeoutException {
		return solver.isSatisfiable();
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            a thing.
	 * @param y
	 *            a thing implied by x.
	 * @throws ContradictionException
	 */
	public void addImplies(T x, T y) throws ContradictionException {
		IVecInt clause = new VecInt();
		clause.push(-getIntValue(x));
		clause.push(getIntValue(y));
		solver.addClause(clause);
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            an array of things such that x[i] -> y for all i.
	 * @param y
	 *            a thing implied by all the x[i].
	 * @throws ContradictionException
	 */
	public void addImplies(T[] x, T y) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T t : x) {
			clause.push(-getIntValue(t));
			clause.push(getIntValue(y));
			solver.addClause(clause);
			clause.clear();
		}
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            a collection of things such that x[i] -> y for all i.
	 * @param y
	 *            a thing implied by all the x[i].
	 * @throws ContradictionException
	 */
	public void addImplies(Collection<T> x, T y) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T t : x) {
			clause.push(-getIntValue(t));
			clause.push(getIntValue(y));
			solver.addClause(clause);
			clause.clear();
		}
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            a thing such that x -> y[i] for all i
	 * @param y
	 *            an array of things implied by x.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addImplies(T x, T[] y) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T t : y) {
			clause.push(-getIntValue(x));
			clause.push(getIntValue(t));
			solver.addClause(clause);
			clause.clear();
		}
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            a thing such that x -> y[i] for all i
	 * @param y
	 *            a collection of things implied by x.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addImplies(T x, Collection<T> y) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T t : y) {
			clause.push(-getIntValue(x));
			clause.push(getIntValue(t));
			solver.addClause(clause);
			clause.clear();
		}
	}

	/**
	 * Easy way to feed the solver with a clause.
	 * 
	 * @param x
	 *            a thing such that x -> y[1] ... y[n]
	 * @param y
	 *            an array of things whose disjunction is implied by x.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addImplication(T x, T[] y) throws ContradictionException {
		IVecInt clause = new VecInt();
		clause.push(-getIntValue(x));
		for (T t : y) {
			clause.push(getIntValue(t));
		}
		solver.addClause(clause);
	}

	/**
	 * Easy way to feed the solver with implications.
	 * 
	 * @param x
	 *            a thing such that x -> y[1] ... y[n]
	 * @param y
	 *            a collection of things whose disjunction is implied by x.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addImplication(T x, Collection<T> y)
			throws ContradictionException {
		IVecInt clause = new VecInt();
		clause.push(-getIntValue(x));
		for (T t : y) {
			clause.push(getIntValue(t));
		}
		solver.addClause(clause);
	}

	/**
	 * Easy way to enter in the solver that at least degree x[i] must be
	 * satisfied.
	 * 
	 * @param x
	 *            an array of things.
	 * @param degree
	 *            the minimal number of elements in x that must be satisfied.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addAtLeast(T[] x, int degree) throws ContradictionException {
		IVecInt literals = new VecInt(x.length);
		for (T t : x) {
			literals.push(getIntValue(t));
		}
		solver.addAtLeast(literals, degree);
	}

	/**
	 * Easy way to enter in the solver that at least degree x[i] must be
	 * satisfied.
	 * 
	 * @param x
	 *            an array of things.
	 * @param degree
	 *            the minimal number of elements in x that must be satisfied.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addAtLeast(Collection<T> x, int degree)
			throws ContradictionException {
		IVecInt literals = new VecInt(x.size());
		for (T t : x) {
			literals.push(getIntValue(t));
		}
		solver.addAtLeast(literals, degree);
	}

	/**
	 * Easy way to enter in the solver that at most degree x[i] must be
	 * satisfied.
	 * 
	 * @param x
	 *            an array of things.
	 * @param degree
	 *            the maximal number of elements in x that must be satisfied.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addAtMost(T[] x, int degree) throws ContradictionException {
		IVecInt literals = new VecInt(x.length);
		for (T t : x) {
			literals.push(getIntValue(t));
		}
		solver.addAtMost(literals, degree);
	}

	/**
	 * Easy way to enter in the solver that at most degree x[i] must be
	 * satisfied.
	 * 
	 * @param x
	 *            an array of things.
	 * @param degree
	 *            the maximal number of elements in x that must be satisfied.
	 * @throws ContradictionException
	 *             if a trivial inconsistency is detected.
	 */
	public void addAtMost(Collection<T> x, int degree)
			throws ContradictionException {
		IVecInt literals = new VecInt(x.size());
		for (T t : x) {
			literals.push(getIntValue(t));
		}
		solver.addAtMost(literals, degree);
	}

	public void addExactlyOneOf(T... ts) throws ContradictionException {
		IVecInt literals = new VecInt(ts.length);
		for (T t : ts) {
			literals.push(getIntValue(t));
		}
		solver.addAtMost(literals, 1);
		solver.addClause(literals);
	}
	
	/**
	 * Add a constraint x -> (y <-> z).
	 * 
	 * @param x
	 * @param y
	 * @param z
	 * @throws ContradictionException 
	 */
	public void addImpliesEquivalence(T x, T y, T z) throws ContradictionException {
		IVecInt literals = new VecInt();
		literals.push(-getIntValue(x)).push(-getIntValue(y)).push(getIntValue(z));		
		solver.addClause(literals);
		literals.clear();
		literals.push(-getIntValue(x)).push(-getIntValue(z)).push(getIntValue(y));		
		solver.addClause(literals);
	}

	/**
	 * Easy way to mean that a set of things are incompatible, i.e. they cannot
	 * altogether be satisfied.
	 * 
	 */
	public void addConflict(Collection<T> things) throws ContradictionException {
		IVecInt literals = new VecInt(things.size());
		for (T t : things) {
			literals.push(-getIntValue(t));
		}
		solver.addClause(literals);
	}

	/**
	 * Easy way to mean that a set of things are incompatible, i.e. they cannot
	 * altogether be satisfied.
	 * 
	 */
	public void addConflict(T... things) throws ContradictionException {
		IVecInt literals = new VecInt(things.length);
		for (T t : things) {
			literals.push(-getIntValue(t));
		}
		solver.addClause(literals);
	}

	public void setTrue(T... things) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T thing : things) {
			clause.push(getIntValue(thing));
			solver.addClause(clause);
			clause.clear();
		}
	}

	public void setFalse(T... things) throws ContradictionException {
		IVecInt clause = new VecInt();
		for (T thing : things) {
			clause.push(-getIntValue(thing));
			solver.addClause(clause);
			clause.clear();
		}
	}
}

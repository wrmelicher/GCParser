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
package org.sat4j.minisat.constraints.card;

import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.UnitPropagationListener;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;

public abstract class Cards {

	public static int niceParameters(UnitPropagationListener s, ILits voc,
	        IVecInt ps, int deg) throws ContradictionException {
	
	    if (ps.size() < deg)
	        throw new ContradictionException();
	    int degree = deg;
	    for (int i = 0; i < ps.size();) {
	        // on verifie si le litteral est affecte
	        if (voc.isUnassigned(ps.get(i))) {
	            // go to next literal
	            i++;
	        } else {
	            // Si le litteral est satisfait,
	            // ?a revient ? baisser le degr?
	            if (voc.isSatisfied(ps.get(i))) {
	                degree--;
	            }
	            // dans tous les cas, s'il est assign?,
	            // on enleve le ieme litteral
	            ps.delete(i);
	        }
	    }
	
	    // on trie le vecteur ps
	    ps.sortUnique();
	    // ?limine les clauses tautologiques
	    // deux litt?raux de signe oppos?s apparaissent dans la m?me
	    // clause
	
	    if (ps.size() == degree) {
	        for (int i = 0; i < ps.size(); i++) {
	            if (!s.enqueue(ps.get(i))) {
	                throw new ContradictionException();
	            }
	        }
	        return 0;
	    }
	
	    if (ps.size() < degree)
	        throw new ContradictionException();
	    return degree;
	
	}


}

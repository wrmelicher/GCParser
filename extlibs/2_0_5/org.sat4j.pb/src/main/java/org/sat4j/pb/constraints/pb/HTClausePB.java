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
* Based on the pseudo boolean algorithms described in:
* A fast pseudo-Boolean constraint solver Chai, D.; Kuehlmann, A.
* Computer-Aided Design of Integrated Circuits and Systems, IEEE Transactions on
* Volume 24, Issue 3, March 2005 Page(s): 305 - 317
* 
* and 
* Heidi E. Dixon, 2004. Automating Pseudo-Boolean Inference within a DPLL 
* Framework. Ph.D. Dissertation, University of Oregon.
*******************************************************************************/
package org.sat4j.pb.constraints.pb;

import static org.sat4j.core.LiteralsUtils.neg;

import java.math.BigInteger;

import org.sat4j.minisat.constraints.cnf.HTClause;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.UnitPropagationListener;
import org.sat4j.specs.IVecInt;

public class HTClausePB extends HTClause implements PBConstr {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

	private boolean learnt;

    public HTClausePB(IVecInt ps, ILits voc) {
        super(ps, voc);
        // TODO Auto-generated constructor stub
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.constraints.pb.PBConstr#getCoefficient(int)
     */
    public BigInteger getCoef(int literal) {
        return BigInteger.ONE;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.sat4j.minisat.constraints.pb.PBConstr#getDegree()
     */
    public BigInteger getDegree() {
        return BigInteger.ONE;
    }

    public BigInteger[] getCoefs() {
        BigInteger[] tmp = new BigInteger[size()];
        for (int i = 0; i < tmp.length; i++)
            tmp[i] = BigInteger.ONE;
        return tmp;
    }

    /**
     * Creates a brand new clause, presumably from external data. Performs all
     * sanity checks.
     * 
     * @param s
     *            the object responsible for unit propagation
     * @param voc
     *            the vocabulary
     * @param literals
     *            the literals to store in the clause
     * @return the created clause or null if the clause should be ignored
     *         (tautology for example)
     */
    public static HTClausePB brandNewClause(UnitPropagationListener s,
            ILits voc, IVecInt literals) {
        HTClausePB c = new HTClausePB(literals, voc);
        c.register();
        return c;
    }

    @Override
    public void assertConstraint(UnitPropagationListener s) {
        for (int i = 0; i < size(); i++)
            if (getVocabulary().isUnassigned(get(i))) {
                boolean ret = s.enqueue(get(i), this);
                assert ret;
                break;
            }
    }

    public IVecInt computeAnImpliedClause() {
        return null;
    }
    
	/**
	 * declares this clause as learnt
	 * 
	 */
	public void setLearnt() {
		learnt = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.sat4j.minisat.datatype.Constr#learnt()
	 */
	public boolean learnt() {
		return learnt;
	}

	/**
	 * Register this clause which means watching the necessary literals If the
	 * clause is learnt, setLearnt() must be called before a call to register()
	 * 
	 * @see #setLearnt()
	 */
	public void register() {
		if (learnt) {
			if (middleLits.length > 0) {
				// looking for the literal to put in tail
				int maxi = 0;
				int maxlevel = voc.getLevel(middleLits[0]);
				for (int i = 1; i < middleLits.length; i++) {
					int level = voc.getLevel(middleLits[i]);
					if (level > maxlevel) {
						maxi = i;
						maxlevel = level;
					}
				}
				if (maxlevel > voc.getLevel(tail)) {
					int l = tail;
					tail = middleLits[maxi];
					middleLits[maxi] = l;
				}
			}
		}

		// watch both head and tail literals.
		voc.attach(neg(head), this);
		voc.attach(neg(tail), this);
	}


}

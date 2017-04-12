r"""
Computation of the asphericity of a convex polytope.

AUTHORS:

- Marcelo Forets (2016-09-10)
"""
#*****************************************************************************
#       Copyright (C) 2016 Marcelo Forets <mforets@nonlinearnotes.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

# SciPy dependencies
import numpy as np
import random

# Sage rings
from sage.rings.rational_field import QQ
from sage.rings.real_double import RDF

# Sage constructors
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.matrix.constructor import matrix, vector
from sage.modules.free_module_element import zero_vector

# Other Sage dependencies
from exceptions import NotImplementedError
from sage.numerical.mip import MixedIntegerLinearProgram

# Polyhedron tools
from polyhedron_tools.misc import *

def asphericity_polytope(P, tol=1e-1, MaxIter=1e2, verbose=0, solver='GLPK'):
    r""" Algorithm for computing asphericity

    INPUT:

    ``x0`` - point in the interior of P

    ``tol`` - stop condition

    OUTPUT:

    ``psi_opt`` -  `\min_{x \in P} psi(x) = R(x)/r(x)`, where `R(x)` and `r(x)` are the circumradius
                and the inradius at `x` respectively

    ``alphakList`` - sequence of `\psi(x)` which converges to `\psi_{\text{opt}}`

    ``xkList`` - sequence of interior points which converge to the minimum
    """
    # check if the polytope is not full-dimensional -- in this case the notion 
    # of asphericity still makes sense but there is yet no "affine function" (or 
    # "relative interior") method from the Polyhedron class that we can use
    # see :trac:16045
    if not P.is_full_dimensional():
        raise NotImplementedError('The polytope is not full-dimensional')

    # initial data
    p = P.ambient_dim()

    [DP, d] = polyhedron_to_Hrep(P) # in the form Dy <= d
    D = -DP    # transform to <Dj,y> + dj >= 0
    l = D.nrows()
    mP = opposite_polyhedron(P)

    # unit ball, infinity norm
    Bn = BoxInfty(center=zero_vector(RDF,p), radius=1)
    [C, c] = polyhedron_to_Hrep(Bn)
    C = -C    # transform to <Cj,y> + cj >= 0
    m = len(c)

    # auxiliary matrices A, a, B, b
    A = matrix(RDF, C.nrows(), C.ncols())
    a = []
    for i in range(m):
        A.set_row(i, -C.row(i)/c[i])
        a.append(support_function(mP, A.row(i),solver=solver))

    B = matrix(RDF, D.nrows(), D.ncols())
    b = []
    for j in range(l):
        [nDj, ymax] = support_function(Bn, D.row(j), return_xopt=True,solver=solver)
        B.set_row(j, D.row(j)/nDj)
        b.append(d[j]/nDj)

    # generate an initial point
    x0 = chebyshev_center(DP, d)

    # compute asphericity at x0
    R = max(A.row(i)*vector(x0)+a[i] for i in range(m))
    r = min(B.row(j)*vector(x0)+b[j] for j in range(l))
    alpha0 = R/r

    xkList = [vector(x0)]
    alphakList = [alpha0]

    xk0 = x0; psi_k0 = alpha0
    alphak0 = alpha0
    convergeFlag = 0
    iterCount = 0
    while (iterCount < MaxIter) and (not convergeFlag):
        [psi_k, xkDict, zkDict] = _asphericity_iteration(xk0, l, m, p, A, a, B, b, verbose=verbose,solver=solver)
        xk = vector(xkDict); xkList.append(xk)
        zk = vector(zkDict); alphakList.append(zk[0])
        xk0 = xk;
        if (abs(psi_k - psi_k0) < tol):
            convergeFlag = 1
        psi_k0 = psi_k
        iterCount += 1

    x_asph = xkList.pop()
    R_asph = max(A.row(i)*vector(x_asph)+a[i] for i in range(m))
    r_asph = min(B.row(j)*vector(x_asph)+b[j] for j in range(l))
    asph = R_asph/r_asph

    return [asph, x_asph]

def _asphericity_iteration(xk, l, m, p, A, a, B, b, verbose=0, solver='GLPK'):
    # find better way to share all those parameters, maybe a class

    #alphak = asphericity(xk)
    R_xk = max(A.row(i)*vector(xk)+a[i] for i in range(m))
    r_xk = min(B.row(j)*vector(xk)+b[j] for j in range(l))
    alphak = R_xk/r_xk

    a_LP = MixedIntegerLinearProgram(maximization=False, solver=solver)
    x = a_LP.new_variable(integer=False, nonnegative=False)
    z = a_LP.new_variable(integer=False, nonnegative=False)

    for i in range(m):
        for j in range(l):
            aux = sum( (A.row(i)[k]-alphak*B.row(j)[k])*x[k] for k in range(p))
            a_LP.add_constraint(aux + a[i] - alphak*b[j] <= z[0]);

    #solve LP
    a_LP.set_objective(z[0])

    if (verbose):
        print '**** Solve LP ****'
        a_LP.show()

    opt_val = a_LP.solve()

    x_opt = a_LP.get_values(x);
    z_opt = a_LP.get_values(z)

    if (verbose):
        print 'Objective Value:', opt_val
        for i, v in x_opt.iteritems():
            print 'x_%s = %f' % (i, v)

        for i, v in z_opt.iteritems():
            print 'z = %f' % (v)
        print '\n'

    return [opt_val, x_opt, z_opt]
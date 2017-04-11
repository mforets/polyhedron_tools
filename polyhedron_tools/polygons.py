r"""
Tools for working with polygons in SageMath, with a focus on computational geometry.

Features:

- Random polygons
- Sorting of vertices
- Order reduction by edge prunning
  
AUTHOR:

- Marcelo Forets (March 2017 at VERIMAG - UGA)

Last modified: 2017-04-09
"""

#************************************************************************
#       Copyright (C) 2016 Marcelo Forets <mforets@nonlinearnotes.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# any later version.
#                  http://www.gnu.org/licenses/
#************************************************************************

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

# Misc methods
from sage.geometry.polyhedron.misc import _make_listlist  
    
def random_polygon_2d(num_vertices, **kwargs):
    r"""Generate a random polygon (2d) obtained by uniform sampling over the unit circle.

    INPUT:

    * ``num_vertices`` - the number of vertices of the generated polyhedron.

    * ``base_ring`` - (default: ``QQ``). The ring passed to the constructor of Polyhedron. 
    alid options are ``QQ`` and ``RDF``.

    * ``scale`` - (default: 1). The scale factor; each vertex is chosen randomly from the unit circle, 
    and then multiplied by scale.

    OUTPUT:

    A random polygon (object of type Polyhedron), whose vertices belong to a circle
    of radius ``scale``.

    NOTES:

    - If ``RDF`` is chosen as ``base_ring``, sometimes there are exceptions related 
    to numerical errors, and show up as ``'FrozenSet'`` exceptions. This occurs 
    particularly frequently for a large number of vertices (more than 30).
    """
    from sage.functions.log import exp
    from sage.symbolic.constants import pi
    from sage.symbolic.all import I
        
    base_ring = kwargs['base_ring'] if 'base_ring' in kwargs else QQ

    scale = kwargs['scale'] if 'scale' in kwargs else 1

    angles = [random.uniform(0, 2*pi.n(digits=5)) for i in range(num_vertices)]
    vert = [[scale*exp(I*angles[i]).real(), scale*exp(I*angles[i]).imag()] for i in range(num_vertices)]

    return Polyhedron(vertices = vert, base_ring=base_ring)
    
def vertex_connections(P):
    r"""Return the vertices that are connected to each edge.
    
    INPUT: 
    
    "P" - a polygon (Polyhedron object in a two-dimensional ambient space). 
    
    OUTPUT: 
    
    A collection of lists ``li`` of integers, where each ``li`` corresponds to a pair of vertices. 
    The vertices are indexed with respect to ``P.vertices_list()``.
    
    NOTES: 
    
    - This has been tested in ``QQ`` and in ``RDF`` base rings. 
    - For ``RDF`` we have a ``tol`` parameter to decide if a vertex 
    satisfies a constraint. 
    """    
    # tolerance for numerical error (for use in RDF only)
    tol = 1e-6
        
    got_QQ = True if P.base_ring() == QQ else False
    
    constraints_matrix = []
    
    # loop in the constraints
    for i, constraint in enumerate(P.inequalities_list()):

        # independent term and coefficient vector
        bi = constraint[0]; ai = vector([constraint[1], constraint[2]])

        constraint_i_vertices = []
    
        for j, vj in enumerate(P.vertices_list()):
            
            if (got_QQ and (ai*vector(vj) + bi == 0)) or (not got_QQ and abs(ai*vector(vj) + bi < tol)): 
                constraint_i_vertices.append(j)
        constraints_matrix.append(constraint_i_vertices)
        
    return constraints_matrix

def edges_adjacent(P, i, cmatrix=None):
    r"""Return the edges that are connected to a given edge in a polygon.
        
    INPUT: 
    
    ``P`` - a polygon (Polyhedron object in two-dimensional ambient space).
    
    ``i`` - integer, index of edge in ``P.inequalities_list()``.
    
    OUTPUT: 
    
    Indices of the edges that are adjacent to the given edge. 
    The edges are indexed according to ``P.inequalities_list()``. 
    
    NOTES: 
    
    - This has been tested for P in QQ and RDF only.
    """
    if cmatrix is None:
        cmatrix = vertex_connections(P)
    
    constraint = P.inequalities_list()[i]
    
    neighbor_constraints = []
    
    # vertices associated to the given edge i
    vert_i = cmatrix[i]
    
    for j, cj in enumerate(cmatrix):
        if (vert_i[0] in cj or vert_i[1] in cj) and (j != i):
            neighbor_constraints.append(j)
            
    return neighbor_constraints

def edges_intersection(P, i, cmatrix=None):
    r"""Return the point in the plane where the edges adjacent to the input edge intersect.
    
    INPUT: 
    
    ``P`` - a polygon (Polyhedron in 2d).
    
    ``i`` - integer, index of edge in ``P.inequalities_list()``.
    
    ``cmatrix`` - (optional) if None, the constraints matrix corresponding to P is computed inside the function.
    
    OUTPUT: 
    
    ``p`` - coordinates of the intersection of the edges that are adjacent to i.
    
    ``neighbor_constraints`` - indices of the edges that are adjacent to it. The edges are indexed according to P.inequalities_list(). 
    
    NOTES: 
    
    - This has been tested for P in QQ and RDF.
    """
    from sage.symbolic.ring import SR
    
    if cmatrix is None:
        cmatrix = vertex_connections(P)
       
    got_QQ = True if P.base_ring() == QQ else False
    
    #constraint_i = P.inequalities_list()[i]

    neighbor_constraints = []
    
    # vertices associated to the given edge i
    vert_i = cmatrix[i]
    
    for j, cj in enumerate(cmatrix):
        if (vert_i[0] in cj or vert_i[1] in cj) and (j != i):
            neighbor_constraints.append(j)
            
    # first one
    constr_1 = P.inequalities_list()[neighbor_constraints[0]]

    # second one
    constr_2 = P.inequalities_list()[neighbor_constraints[1]]

    # write and solve the intersection of the two lines
    x1 = SR.var('x1'); x2 = SR.var('x2')
    
    eq1 = constr_1[1]*x1 + constr_1[2]*x2 == -constr_1[0]
    eq2 = constr_2[1]*x1 + constr_2[2]*x2 == -constr_2[0]

    p = solve([eq1, eq2], x1, x2)
    p = [p[0][0].right_hand_side(), p[0][1].right_hand_side()]            
            
    if not got_QQ: # assuming RDF
        # transform to RDF (because solve produces in general rational answers)
        p = [RDF(pi) for pi in p]
    
    return p, neighbor_constraints

def simplification_edge_prunning(X, E, XE=None, verbose=True):
    r"""Reduce the number of vertices in a polygon. 
    
    Given a polygon `X` and an error set `E`, compute a simplified polygon `X_{new}` 
    based on edge removal, and such that the output is included in `X + E`.
    
    INPUT: 
    
    ``X`` - a polygon (Polyhedron in 2d).
    
    ``E`` - a polygon (Polyhedron in 2d).    
    
    OUTPUT: 
    
    ``Xnew`` - prunned polygon.
    
    NOTES: 
    
    - The input `X + E` is optional; if it is not provided then it is computed. 
    - For several iterations of this algorithm, only the polygon `X + E` 
    should be kept as it was at the first iteration, while X changes.
    """
    if XE is None:
        XE = X + E 
    
    # compute matrix of connections
    cmatrix = vertex_connections(X)

    # number of original inequalities
    NINEQ = len(X.inequalities_list())

    # keep track of those which have been removed
    edges_removed = []

    # loop over constraints (step is the third argument)
    for i in range(0, NINEQ, 1):
    
        # find the point at which the neighbours of edge i intersect
        p, neighbors = edges_intersection(X, i, cmatrix)

        # check whether p lies in XE
        if XE.contains(p):
           
            # check if there is a common vertex between edge i and any of the edges that have been removed
            got_conflict = any(cmatrix[i][0] in cmatrix[e] for e in edges_removed)
            got_conflict = got_conflict or any(cmatrix[i][1] in cmatrix[e] for e in edges_removed)
        
            if not got_conflict:
                # remove i-th inequality provided there are no conflicts
                edges_removed.append(i)
   
    
    # prunned list of inequalities
    Xnew_ieqs = []

    for i, ieq in enumerate(X.inequalities_list()):
        if i not in edges_removed:
            Xnew_ieqs.append(ieq) 

    # instantiate new polyhedron        
    Xnew = Polyhedron(ieqs = Xnew_ieqs)     

    if verbose:
        print '\ninitial number of edges = ', len(X.inequalities_list())
        print 'final number of edges = ', len(Xnew_ieqs)
    
    return Xnew    

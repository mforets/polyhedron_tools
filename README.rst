============================================================================
Tools for polytopes in SageMath
============================================================================

.. image:: https://api.travis-ci.org/mforets/polyhedron_tools.svg
   :target: https://travis-ci.org/mforets/polyhedron_tools

.. image:: https://img.shields.io/badge/docs-latest-blue.svg
   :target: http://mforets.github.io/polyhedron_tools/doc/html

.. image:: https://img.shields.io/github/license/mashape/apistatus.svg?maxAge=2592000
   :target: https://github.com/mforets/polyhedron_tools/blob/master/LICENSE

This project interacts with SageMath's class `Polyhedron <http://doc.sagemath.org/html/en/reference/discrete_geometry/index.html#polyhedral-computations>`_, adding extra features geared towards:

- computational geometry,
- mathematical optimization, and
- high-dimensional set-based calculus. 

It has both an educational and a research purpose.

**WARNING:** *This package is deprecated and is no longer maintained. You may be interested to check out our Julia package* `LazySets.jl <https://github.com/JuliaReach/LazySets.jl>`_.

Installation
~~~~~~~~~~~~

To install the package use the following command::

   sage -pip install --upgrade -v git+https://github.com/mforets/polyhedron_tools.git

Documentation
~~~~~~~~~~~~~

There is an online `HTML documentation <http://mforets.github.io/polyhedron_tools/doc/html/>`_.

For a local build of the HTML documentation, clone this repository and run::

   sage -sh -c "make html"
    
The documentation in PDF format can be built with::

   sage -sh -c "make latexpdf"

These commands shall be executed inside the ``/docs`` directory.

Examples
~~~~~~~~

`Browse the Jupyter notebooks <https://github.com/mforets/polyhedron_tools/tree/master/examples>`_ which are available in the ``/examples`` folder in this repository. 

These can be displayed in a window embedded in github, but it is recommended to use the 
external `nbviewer <http://nbviewer.jupyter.org/github/mforets/polyhedron_tools/tree/master/examples/>`_.

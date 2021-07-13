# CoqRK : Coq formalization of roundoff error analysis of Runge-Kutta methods.

Author: Florian Faissole

# Build 

The following dependencies are needed: 
- Coq 8.13.2.
- mathcomp 1.12.0.
   (opam packages coq-mathcomp-ssreflect, coq-mathcomp-fingroup, coq-mathcomp-algebra).
- Flocq 3.4.2.
- Coquelicot 3.2.0.
- coq-interval 4.3.0. 
 
Ideally, you just have to install the dependencies and run:

$ make

# Organization

The project is organized as follows:

- Rstruct.v : this file is part of the CoqApprox library http://tamadi.gforge.inria.fr/CoqApprox/ ;
- Rstruct_Rpos_compl.v : this file is an adaptation of Rstruct.v for the set R+ of positive real numbers ;
- Compl.v : complements about bigops, matrices, real numbers ;
- RungeKutta.v : generic formalization of Runge-Kutta methods, their implementations and the associated 
expression of local and global rounding errors ;
- Norms.v : definitions and properties of the infinity vector and matrix norms ; 
- FP_prel.v : rounding error bounds for dot products and matrix products, generic results to build the 
local error bounds of RK methods ; 
- Error_loc_to_glob.v : main theorem to bound the global error from bounds on the previous local errors ; 
- Instanciations.v : instanciation of the analysis on Euler and RK2 methods.



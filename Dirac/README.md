# Symbolic Reasoning about Quantum Circuits


## Overview


we propose a symbolic approach to reasoning about quantum circuits. 
It is based on a small set of laws involving some basic manipulations on vectors and matrices. 
This symbolic reasoning scales better than the explicit one and is well suited to be automated in Coq, as demonstrated with some typical examples.


We describe it in detail in [this draft](https://arxiv.org/pdf/2005.11023)(The latest version is still waiting for be announced).


## Directory Contents

### src


Symbolic reasoning strategy design


- src/Complex.v : Complex number library, modified from Coquelicot

- src/sym/M_notWF.v : Matrix library without WF assumptions and redefined matrix equivalence.
- src/sym/MN_notWF.v : Matrix library with BinNat parameters.
- src/sym/Dirac.v : Symbolic reasoning strategy library with Dirac notation.
- src/sym/Equival.v : Equivalences of circuits.

- src/com/Matrix.v : Matrix library, copid form Qwire(https://github.com/inQWIRE/QWIRE), for experimental comparison.
- src/com/Quantum.v : Define unitary matrices and quantum operations library, copid form Qwire(https://github.com/inQWIRE/QWIRE), for experimental comparison.


### example


Examples of verifying correctness properties of quantum circuits using two approaches.


- example/sym_exa/Deutsch.v : Deutsch's algorithm with symbolic approaches.
- example/sym_exa/QFT.v : quantum Fourier transform (QFT) with three qubits with symbolic approaches.
- example/sym_exa/Simon.v : Simon's algorithm with symbolic approaches.
- example/sym_exa/SS.v : quantum secret sharing protocol with symbolic approaches.
- example/sym_exa/Teleportation.v : quantum teleportation with symbolic approaches.
- example/sym_exa/Grover.v : Grover’s search algorithm with two qubits with symbolic approaches.
- example/sym_exa/Simple.v : Equivalences of circuits.
- example/sym_exa/Big_example.v : Preparation of an entangled states.


- example/com_exa/D_solve.v : Deutsch's algorithm with computational approaches.
- example/com_exa/Q_solve.v : quantum Fourier transform (QFT) with three qubits with computational approaches.
- example/com_exa/S_solve.v : Simon's algorithm with computational approaches.
- example/com_exa/SS_solve.v : quantum secret sharing protocol with computational approaches.
- example/com_exa/T_solve.v : quantum teleportation with computational approaches.
- example/com_exa/G_solve.v : Grover’s search algorithm with two qubits with computational approaches.



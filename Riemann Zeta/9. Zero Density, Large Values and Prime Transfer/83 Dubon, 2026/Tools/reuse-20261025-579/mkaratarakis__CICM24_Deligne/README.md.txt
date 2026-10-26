# A formalization of the statement of Deligne’s Theorem

This archive contains the source code for the paper "A formalisation of the statement of
Deligne’s Theorem", submitted to [CICM 2024](https://cicm-conference.org/2024/cicm.php?event=&menu=general). 

The code runs over  Lean's version 4.2.0-nightly-2023-09-18 and mathlib's version [c4bd112a7f09](https://github.com/leanprover-community/mathlib4) (Sep 18, 2023).

We present a partial formalization using the Lean 4 theorem
prover of the statement of Deligne's theorem on attaching
a $p$-adic Galois representation to a weight $k$ eigenform.
The case of this theorem for $k = 2$ is an important part of
the Wiles/Taylor-Wiles proof of Fermat's Last Theorem.
The statement of Deligne's theorem involves diverse
mathematical notions like Galois representations and modular
forms. We have not fully formalized them,
but the only parts missing are proofs of propositions.
This means that all mathematical objects in the statement
have been fully defined. In this paper we also locate this 
work on a lattice of notions of partial formalization, 
with full formalization at the top, and formalization 
in which not even all objects have been defined at the bottom.

# Installation instructions

The formalization depends on Lean 4, VS Code, and Mathlib.

For detailed instructions to install Lean, mathlib, and supporting tools, 
visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

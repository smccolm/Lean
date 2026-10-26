# Toward a formalisation of the statement of Deligne’s Theorem

This repository contains the source code for the short paper "Toward a formalisation of the statement of
Deligne’s Theorem", submitted to [ITP 2023](https://mizar.uwb.edu.pl/ITP2023/). The code runs over Lean 3.49.1 and mathlib's version [bd9851c](https://github.com/leanprover-community/mathlib) (Feb 20, 2023).

Deligne’s theorem attaching a $p$-adic Galois representation to a weight $k$ eigenform 
is an important result in number theory. The case $k=2$ was historically proven earlier 
by Eichler and Shimura, and constitutes a necessary component in the Wiles/Taylor--Wiles 
proof of Fermat's Last Theorem. The formalisation of the statement of Deligne's theorem 
has been suggested as a challenge for modern theorem provers. Moreover, the formalisation 
of this statement involves the formalisation of objects that are currently studied in 
present mathematical research such as the Langlands Program. We discuss a work in progress 
formalisation of the statement of this theorem in the Lean 3 theorem prover.

# Installation instructions

The formalization has been developed over Lean 3 and its matemathical library mathlib. For detailed instructions to install Lean, mathlib, and supporting tools, visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

After installation, run the command `leanproject get mkaratarakis/Deligne` to obtain a copy of the project's source files and dependencies. To open the project in VS Code, either run `path/to/Deligne` on the command line, or use the "Open Folder" menu option to open the project's root directory. To compile the project locally, use the command `lean --make src`.

Copyright (C) 2023, Michail Karatarakis

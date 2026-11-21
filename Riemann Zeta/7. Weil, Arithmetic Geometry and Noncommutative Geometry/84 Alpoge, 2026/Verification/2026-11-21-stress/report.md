# Adversarial checks of the Alpöge export

**Verdict.** Both independent local kernels accepted the published proof of classical RH and Dirichlet GRH. The proof-body mutation, extra axiom and false headline all produced the expected rejections. The full solution also discharged an expanded challenge containing the two analytic-continuation formulations and the universal Robin and Lagarias inequalities.

## Independent kernel replay

Nanoda, the Rust kernel bundled with Lean 4.36.0 for Windows, accepted the full solution with **1,484,733 declarations checked and zero errors**. The run exited 0 after 4 h 4 min 45 s. The configuration allowed only `propext`, `Classical.choice`, and `Quot.sound`, with a hard error for any other axiom even if unused. Nanoda printed all five headline theorems and the definition of `RiemannHypothesis` from the checked input. The underscores in its theorem listing come from the pretty-printer setting that hides proof bodies. The kernel still checked those bodies. [Kernel transcript](nanoda.txt) · [Statements and axioms](nanoda-statements.txt) · [Configuration, binary hash and timings](evidence.json)

The two checkers count the same file differently. We counted its records directly. con-leche's **1,468,418** includes 7,969 grouped inductive records. Those groups contain 7,970 types, 8,342 constructors and 7,972 recursors. Counting the individual constants gives Nanoda's **1,484,733** exactly. The export has three explicit axiom records. [Counts by record type](evidence.json)

## What the theorem says

The classical target is Mathlib's `RiemannHypothesis`. It quantifies over complex zeros, excludes the negative even integers and the point 1, and concludes that the real part is ½. The Dirichlet targets cover every positive modulus, including imprimitive characters. The zero-location theorems quantify over the open critical strip. The nonvanishing theorem covers the open half-plane to the right of ½ and excludes the principal character at 1. [Pinned challenge](https://github.com/leanprover-community/riemann-hypothesis/blob/09e686ad48b95c3d6d6cff1f37b5fd2a6bc99314/src/Challenge.lean)

## Reproducing the target

Using Lean 4.33.1, Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and lean4export at `15f6055e299ad5b89345e533cc2192f4cc00f659`, we built the public challenge in a directory containing no submitted proof modules. Its 350,862,311-byte export matched the published challenge byte for byte. The previous local con-leche run checked the solution against this challenge and justified each of its five named holes. [Pinned challenge and hashes](evidence.json) · [Original comparison](../2026-11-21-con-leche.txt)

The solution export's SHA-256 is `5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e`. We compared the actual exported proof terms of the five public theorems and two intermediate results with their right-hand sides in the author's source. In particular, `riemannHypothesis` invokes `rhOfAll`, which applies `Formalism.VW.rh_of_every` to `allChi`. The latter invokes `UpperTheory.FinalTheorems.everyCharacter`. The import graph read from the archive was acyclic, and all 175,187 submitted modules were reachable from `Main` by imports. A literal search for the eight proof-bypass or assumption tokens listed in the evidence file found zero matches. [Source checks and term matches](evidence.json)

## Identifying the analytic functions

We wrote a second formulation of classical RH using only the series $\sum_{n=1}^{\infty}n^{-s}$, holomorphic continuation to the complex plane punctured at 1, and the locations of zeros. We wrote the corresponding critical-strip statement for $\sum_{n=1}^{\infty}\chi(n)n^{-s}$ for every Dirichlet character of positive modulus. Both statements quantify over every function with the specified continuation property.

Lean 4.33.1 checked that each formulation is equivalent to its Mathlib counterpart, using stock Mathlib alone. The functions agree on a neighborhood of 2 because their series agree there. The identity theorem extends that equality over the connected punctured plane. Conversely, Mathlib's own functions furnish continuations with the required properties. Each equivalence uses only `propext`, `Classical.choice`, and `Quot.sound`. [Exact statements and proofs](Continuation.lean.txt) · [Axiom output](evidence.json)

## Controls

| Change to the input | Local observation |
| --- | --- |
| Keep the first 199 declarations from the real export intact | Nanoda accepted all 199. |
| Change only the first theorem's proof value to the existing expression `Prop`, preserving its name and type | Nanoda rejected the proof when checking definitional equality. |
| Add one unused axiom to the same prefix | The production axiom policy rejected the added axiom by name. Allowing that specific axiom in the control configuration made the same 200-declaration input pass. |

Run the four checks with `python controls.py PATH_TO_SOLUTION.ndjson PATH_TO_NANODA`. The script reads through the first theorem and makes the changes in temporary copies. [Control script](controls.py)

**Trivial-zero counterexample.** Removing only the exclusion for negative even integers gives a false headline, even with the pole exclusion retained. Lean proved this in stock Mathlib by evaluating the zero at $s=-2$ and showing that its real part differs from ½. The proof used only the three standard axioms. We exported the altered challenge with all five theorem names intact and submitted it alongside the authentic full solution to con-leche. The verified comparison exited 1 after 15 min 50 s. It specifically rejected `riemannHypothesis` because the solution's theorem has another type. [Counterexample in Lean](Boundary.lean.txt) · [Rejected comparison](altered-target.txt)

## Four downstream conclusions

The expanded challenge imports the same five RH and Dirichlet GRH statements. It supplies actual proof bodies for the classical and character-weighted series conclusions and for two divisor-sum inequalities. For the arithmetic implications we used the Robin1984 library at commit `acab1a31f31e0499518a4416b63281e0b4838f9c` and its matching Lean 4.33.1 release objects. We compiled its 203 required dependency modules from their pinned sources, then compiled and exported the four new proofs. We found the theorem records for all four in the 659,086,140-byte export. [Exact downstream proofs](ArithmeticProbe.lean.txt) · [Robin1984 source](https://github.com/kimihiro64/Robin1984/tree/acab1a31f31e0499518a4416b63281e0b4838f9c) · [Export hash and theorem records](evidence.json)

con-leche rechecked all 1,468,418 solution records, accepted all 69,217 records in the expanded challenge, and justified its five original open statements by name and type. The four new theorems were among the ordinary declarations whose proof bodies it checked. The verified comparison exited 0 after 29 min 12 s. [Full comparison transcript](arithmetic-comparison.txt)

Robin's conclusion is $\sigma(n)<e^\gamma n\log\log n$ for every integer $n>5040$. Lagarias's conclusion is $\sigma(n)\le H_n+e^{H_n}\log H_n$ for every positive integer $n$, where $H_n$ is the harmonic sum. Both use Mathlib's divisor sum. The independent numerical exercise below checks the boundary behavior of those same formulas.

## Arithmetic at the cutoff

A separate Python program sieved exact integer divisor sums through 1,000,000. It bounded Euler's constant using the 65,536th harmonic number and bounded exponential and logarithmic evaluations using outward-rounded decimal intervals. Robin's strict inequality held for all 994,960 integers from 5,041 through 1,000,000. At 5,040 the divisor sum was 19,344 and a certified upper bound for the right side was below 19,238. This gives a counterexample to lowering the cutoff by one.

The closest case in the tested interval, measured by the divisor sum divided by Robin's right-hand side, was **10,080**. Its divisor sum is 39,312, between 98.581% and 98.583% of the bound. The program compared it with every other candidate using integer cross multiplication and interval bounds.

Lagarias's inequality was an equality at 1 and held strictly at every integer from 2 through 5,040 by direct interval evaluation. Above 5,040 the certified Robin bounds imply the tested Lagarias inequalities because `Hₙ > log(n) + γ`. The finite sweep checks numerical behavior on this interval. [Runnable calculation](finite_checks.py) · [Bounds and counts](evidence.json)

## Source provenance

This machine rebuilt the challenge and checked selected source-to-export proof terms. The full compilation of the author's 175,187 source modules was performed separately at MIT and LUMI. [MIT verification record](https://math.mit.edu/~drew/grh/) · [LUMI build record](https://github.com/aapolipponen/rh-lean-check-lumi)

# Errata, source distinctions and audit questions

4 October 2026. **PLANNING ONLY.** This is a local register, not an author-issued erratum. No mathematical error in the two main theorems has been established by this setup, and no source-contract repair is claimed or authorized here. Absence of an entry is not a complete correctness certification.

## Confirmed source distinctions

| Item | Evidence | Treatment |
|---|---|---|
| Primary edition | arXiv history shows only `2608.31060v1`, 31 August 2026; original source file is `main.tex`. | Freeze bytes, preserve source labels and distinguish preprint status from publication. |
| GS zero-forcing proposition numbering | The 2018 JEMS PDF calls it Proposition 3.4; arXiv `1501.01804v2` calls the corresponding proposition 3.1. Dong–Wang–Wang–Zhang cites the journal's 3.4. | This is **not** an erroneous citation. Both versions are archived and identified. |
| GS mean-value editions | The 1999 arXiv preprint has 30 pages; the 2003 Canadian Journal article has 40. | Use the journal for cited Theorems 2b/4 and Lemma 7.1. Do not assume page or theorem numbering matches the preprint. |
| Two different Yangs | The paper's reference [11] is **Daodao Yang**, not the Andrew Yang of node 63. | Preserve full author identity in the source survey. |

## Formalization hazards, not diagnosed source errors

- Theorem 1.1 chooses `φ` before `L`. The `η` produced by Proposition 4.1 may depend on `L`; absorbing it into the public center is not faithful.
- The Gaussian transform includes a pole residue absent from the nonprincipal-character version. Dropping it because it is later small changes Lemma 3.3.
- The completed function for Hadamard factorization must be entire `xi`, with its genuine zero divisor. The meromorphic completed zeta and Mathlib's modified entire completion are not interchangeable without equations.
- A factorization theorem with a product-equality hypothesis must be supplied an actual factorization, not used to assume it. Infinite sums need genuine summability.
- Lemma 2.1's source conventions for maximization and multiplicative functions need an exact bridge; no general formalization is claimed from name matching.
- Lemma 5.1 is an all-large-x power bound. The upper bound `x≤T^A` is used later to turn it into logarithmic saving, and must remain in T2.
- Remark 1.3 is supplementary. Audit the full density-source range before claiming its displayed exceptional-set exponent. No correction or formal proof of that remark is supplied by this scaffold.

## Future entry format

For a real issue record: stable identifier; frozen source location and exact claim; classification (source error / attribution / formal bridge / tooling); concrete demonstration; affected gates; proposed repair; owner authorization if the contract changes; actual Lean theorem and transitive audit; unchanged final targets; permanent regression; and verification receipt. Preserve the original, do not overwrite it. Do not copy node-63 counterexamples or repairs into this paper as if they concerned its statements.

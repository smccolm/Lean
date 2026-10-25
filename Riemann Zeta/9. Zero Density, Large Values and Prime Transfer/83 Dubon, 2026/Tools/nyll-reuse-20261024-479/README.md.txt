# NYLL

Lean 4 libraries for number theory and arithmetic geometry.

The official NYLL repository publishes completed, verified modules together with
their dependencies. Further development and unfinished mathematical goals are
maintained separately in the private development workspace. The scope of each
published result is given by its precise Lean statement and assumptions.

[Browse the library](https://n-yamaguchi-0729.github.io/NYLL/) · [Source](https://github.com/n-yamaguchi-0729/NYLL)

## Using NYLL

Use the Lean version in [lean-toolchain](lean-toolchain) and the Mathlib revision
pinned in [lake-manifest.json](lake-manifest.json). Add NYLL to your project's
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/NYLL.git"
rev = "main"
```

Run `lake update Nyll`, then commit the generated lake-manifest.json to retain
the resolved revisions. In Lean, use `import Nyll` for the full collection,
or import the specific modules needed by your proof.

The standalone repositories below provide smaller distributions of the same
package. Choose one distribution; use NYLL when you need several libraries together.

To build a checkout of NYLL, run from its root:

```sh
lake exe cache get
lake --wfail build +Nyll
```

## Libraries

These repositories contain their named library and its actual NYLL import
dependencies. Their READMEs describe the included results and assumptions.

| Library | Description |
| --- | --- |
| [Pro-C Groups](https://github.com/n-yamaguchi-0729/ProCGroups) | Profinite and pro-C groups, free pro-C groups, and completed group algebras. |
| [Class Field Theory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) | Local fields, number fields and global function fields; reciprocity, norm subgroups and class fields. |
| [Sawin's Totally Real Towers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers) | Sawin's totally real tower theorem and related results of Martinet and Shafarevich. |
| [Étale Fundamental Groups and Cohomology](https://github.com/n-yamaguchi-0729/EtaleFundamentalGroupsAndCohomology) | Finite étale covers, fundamental groups, Galois categories and proved cohomological comparisons. |
| [Generalized Jacobians](https://github.com/n-yamaguchi-0729/JacobianVarieties) | Generalized Jacobians over arbitrary fields, with ordinary Jacobians at zero modulus; modulus existence and unique Abel factorization. |
| [Research Papers](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization) | Results on ab-faithful Galois actions and solvable coverings. |
| [Anabelian Geometry](https://github.com/n-yamaguchi-0729/AnabelianGeometry) | Genus-zero weak reconstruction over number fields and geometric hyperbolic slimness. Weak reconstruction proves existence of a curve isomorphism; realizing the supplied group isomorphism and uniqueness in that correspondence remain unfinished. |

[All source code](https://n-yamaguchi-0729.github.io/NYLL/browse/) includes these
libraries and the shared foundations in scheme theory, valued fields, Galois
cohomology, algebraic curves and abelian varieties. The library guides specify
the proved results and the mathematical goals that remain open.

## AI-written code and verification

All original code developed for NYLL is written by OpenAI Codex. The project
maintainer sets the mathematical goals and scope and directs the development.

Published source is checked by Lean with errors and warnings treated as failures.
The Lean workflow records verification for its exact commit. Kernel checking
validates formal proofs against their encoded statements, definitions and
assumptions; fidelity to the intended mathematics requires separate review.

Copyright, authorship and license notices for upstream and adapted code are
preserved in the relevant source files.

## License and attribution

NYLL's original code and documentation are Copyright (c) 2026 Naganori Yamaguchi
and released under [Apache-2.0](LICENSE), unless a file states otherwise.

External and adapted material retains its source-specific copyright, authorship,
license and attribution notices. An absent upstream notice does not transfer
ownership to NYLL. The [pi1 attribution record](Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md)
and [pinned source manifest](Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json) distinguish
upstream adaptations from NYLL additions. Anthropic FLT, Mathlib and other external
source notices remain in their corresponding files and directories.

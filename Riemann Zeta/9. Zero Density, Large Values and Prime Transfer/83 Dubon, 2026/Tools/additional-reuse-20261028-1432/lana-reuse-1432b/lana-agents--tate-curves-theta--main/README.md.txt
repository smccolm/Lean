# tate-curves-theta

Tate curves, q-uniformization, and the formal algebraic theta function.

## Status

The classical `q`-uniformization and theta-function package is **complete and
`sorry`-free** at the current tip. All results below live in the namespace
`TateCurvesTheta` (most under `TateCurvesTheta.TateParameter`), for a Tate parameter
`t : TateParameter K` (a unit `q` with `‖q‖ < 1`) over a field `K` with
`[NormedField K] [CompleteSpace K] [IsUltrametricDist K]`. The only extra hypotheses are
the arithmetic ones written into the statements: `(12 : K) ≠ 0`, or
`TameResidueChar K := ‖(2 : K)‖ = 1 ∧ (12 : K) ≠ 0` for the group law and uniformization.

Evidence: `git grep -nwE 'sorry|admit'` finds no occurrence in any `.lean` file except
in docstrings, and there are no `axiom`/`opaque`/`native_decide` declarations. The
validation script below builds with `lake build --wfail`, under which a `sorry` warning
fails the build.

### Theta function (Mochizuki, *The Étale Theta Function*, Prop. 1.4, classical content)

* Convergence: `thetaTerm_summable`; product form `thetaProd`.
* Quasi-periodicity: `theta_q_smul`, `theta_zpow_q_smul`.
* Inversion and oddness: `theta_inv`, `thetaOdd_inv`, `thetaOdd_q_smul`,
  `thetaOdd_eq_zero_iff` (for the odd theta `thetaOdd u = u · θ(-u²)`).
* Jacobi triple product, unconditional: `theta_eq_thetaProd` (via the Durfee-square identity
  `thetaProdNormConst_eq_one` and the Strassmann-type coefficient uniqueness
  `laurentCoeffUnique`).
* Zero divisor: `theta_eq_zero_iff` (`θ(u) = 0 ↔ u ∈ -qᶻ`), `thetaProd_eq_zero_iff`.

### Tate curve and `q`-uniformization (Silverman, *Advanced Topics*, V.3.1)

* Weierstrass identity, unconditional under `12 ≠ 0`: `tateDefect_eq_zero`,
  `tatePoint_mem'` (the Tate point `(X(u), Y(u))` lies on `E_q` for `u ∉ qᶻ`), proved by
  the Eisenstein pair-identity computation.
* Group law: `tatePoint_mul`, `tatePointHom` with `tatePointHom_ker = qᶻ`,
  `mapTatePointHom_injective`.
* Surjectivity and the isomorphism `Kˣ/qᶻ ≃* E_q(K)`: `tatePoint_surjective`,
  `mapTatePointHom_bijective`, `tateUniformization`. These take the Weierstrass identity
  as an argument `hmem`, which `tatePoint_mem'` discharges.

### The Tate `q`-parameter

* `j`-invariant: `tateJ`, `tateJ_eq_j`, `norm_tateJ` (`‖j(E_q)‖ = ‖q‖⁻¹`),
  `one_lt_norm_tateJ`.
* Characterization (`12 ≠ 0`): `tateJ_injective`, `exists_tateParameter_tateJ_eq`,
  `existsUnique_tateParameter_tateJ_eq`, and
  `existsUnique_splitMultiplicative_tateParameter` (each `j` with `‖j‖ > 1` has a unique
  Tate parameter, whose curve has split multiplicative reduction).
* Reduction: `tateCurveInt`, `isSplitMultiplicative_reduction`,
  `tateCurve_multiplicative_reduction`.
* Normalized order (IUT I, Def. 3.1(c)): `IsUniformizer`, `orderZ`, `toOrdered`
  (`OrderedTateParameter`).
* Base change along isometric extensions `L/K`: `baseChange`, `ord_baseChange`,
  `orderZ_baseChange`, `algebraMap_X`, `algebraMap_Y`, `map_tateCurve`, `algebraMap_tateJ`.

### Converse: split multiplicative curves are Tate curves (Silverman V.5.3)

For an elliptic curve `W` over `K` (`(12 : K) ≠ 0`, any residue characteristic) with
`‖j(W)‖ > 1`, and the twist invariant `gammaInvariant W = -c₄/c₆` (`TateCurvesTheta/Converse/`):

* `exists_variableChange_tateCurve_iff`: `W` is `K`-isomorphic (by a Weierstrass change of
  variables) to `E_q` for `q = ofJ j(W)` iff `γ(W)` is a square in `K`;
  `exists_variableChange_tateCurve` is the existence direction.
* `exists_tateParameter_variableChange_iff`: `W ≅ E_q` for *some* `q` iff `‖j(W)‖ > 1` and
  `γ(W)` is a square.
* Uniqueness: `eq_ofJ_of_smul_eq_tateCurve` (the parameter is `ofJ j(W)`) and
  `smul_eq_tateCurve_iff` (the isomorphism is unique up to the automorphism `-1`,
  `negChange E_q = (-1, 0, -1, 0)`, `negChange_tateCurve`); packaged as
  `existsUnique_tateParameter`.
* Inputs: `TateParameter.isSquare_gammaInvariant` (`γ(E_q)` is a square: `-c₄c₆(E_q) = 1 + 8δ`,
  `‖δ‖ < 1`), Hensel's lemma for square roots in every residue characteristic
  `exists_sq_eq_of_norm_sub_one_lt_norm_four` (`‖a - 1‖ < ‖4‖`), and the Weierstrass
  isomorphism criterion `exists_variableChange_iff_isSquare` for equal `j ≠ 0, 1728` together
  with the automorphism computation `eq_one_or_eq_negChange`.
* Tangent criterion (`TangentCriterion.lean`), for a model with `‖c₄‖ = 1`, `‖Δ‖ < 1`:
  `isSquare_gammaInvariant_iff_exists_tangent_root'` (**every residue characteristic**, `2 ≠ 0`
  in `K`): the tangent quadratic at the node (discriminant `-c₄c₆`) has a root mod `𝔪` iff `γ(W)`
  is a square, via the Hensel form `isSquare_sq_add_four_mul` (`‖s‖ = 1`, `‖e‖ < 1` ⇒ `s² + 4e`
  is a square). The `‖2‖ = 1` versions `isSquare_gammaInvariant_iff_exists_tangent_root` and
  `exists_variableChange_tateCurve_of_tangent_root` (library form of iut's
  `Iut.exists_variableChange_tateCurve`, same hypotheses) are kept.
* Reduction type (`ReductionType.lean`, **every residue characteristic**): `IsIntegral`,
  `integralModel`, `reduction` (over `𝒪/𝔪`), and `HasSplitMultiplicativeReduction W` (some
  change of variables gives an integral model whose reduction is `IsSplitMultiplicative`: nodal,
  node at the origin, split tangent cone). `hasSplitMultiplicativeReduction_iff` (`12 ≠ 0`):
  split multiplicative ⟺ `‖j‖ > 1 ∧ IsSquare γ(W)`; `hasSplitMultiplicativeReduction_iff_exists_tateCurve`:
  ⟺ `W ≅ E_q` for some `q`; `hasSplitMultiplicativeReduction_iff_exists_tangent_root`: for an
  integral model with `‖c₄‖ = 1`, `‖Δ‖ < 1`, split ⟺ the tangent quadratic has an integral root
  mod `𝔪`. Key step `isSquare_gammaInvariant_of_isSplitMultiplicative`: a split node gives
  `b₂ = s² + 4e` (a square `σ²`) and `-c₄c₆ = (σ⁵)² + 4m`, `‖m‖ < 1`; Hensel at precision `‖4‖`
  covers residue characteristic `2`. `TateParameter.hasSplitMultiplicativeReduction`.
* Non-split case (`QuadraticTwist.lean`, `NonSplit.lean`): `quadraticTwist W d`
  (`y² = x³ + d b₂ x² + 8d² b₄ x + 16 d³ b₆`, `c₄ ↦ 2⁴d²c₄`, `c₆ ↦ 2⁶d³c₆`, same `j`,
  `γ ↦ γ/(4d)`); `exists_variableChange_quadraticTwist_iff` (`W ≅ W^d` iff `d` square,
  `j ≠ 0, 1728`). `nonsplit_tateCurve`: for `‖j(W)‖ > 1` and `γ = γ(W)` not a square, `W ≇ E_q`,
  `W ≅ E_q^γ` over `K` (`exists_variableChange_quadraticTwist_tateCurve`, valid for any `γ`),
  `E_q^γ ≇ E_q` over `K`, `[K(√γ) : K] = 2` for `SqrtGammaField W = K[X]/(X² - γ)`, and
  `W ≅ E_q` over `K(√γ)` (base changes along `algebraMap`). General extensions:
  `exists_variableChange_map_tateCurve_iff` (any field `L / K`: `W_L ≅ (E_q)_L` iff `γ` is a
  square in `L`) and, for a valued extension `[NormedField L] [NormedAlgebra K L]`,
  `exists_variableChange_baseChange_tateCurve_iff` (`W_L ≅ E_{q,L}`, via `map_tateCurve`).

### Theta values and continuous Kummer classes (`TateCurvesTheta/Kummer/`)

Uses [`continuous-kummer-theory`](https://github.com/lana-agents/continuous-kummer-theory):
`kummer n K Ω : Kˣ →* H¹_cont(Gal(Ω/K), μ_n)`, `kummerZHat K Ω` into `H¹_cont(G_K, Ẑ(1))`,
`restriction_kummer`, `Decomposition.decomposition_kummerValue`.

* **(i) Kummer classes of theta values** (`ThetaValues.lean`). Off the divisor `-qᶻ`, `θ(u)` is a
  unit `thetaUnit u hu : Kˣ`. Relations from the functional equations, first in `Kˣ` and then
  for every homomorphism `Kˣ →* G` into a commutative group (`map_thetaUnit_*`), stated for
  `kummer n K Ω` and `kummerZHat K Ω`:
  * `qᶻ`-translates: `thetaUnit_zpow_q_smul`, `kummer_thetaUnit_zpow_q_smul`,
    `kummer_thetaUnit_q_smul`, `kummerZHat_thetaUnit_zpow_q_smul`:
    `κ(θ(qᵐu)) = κ(q)^{-e(m)} κ(u)^{-m} κ(θ(u))`, `e(m) = m(m+1)/2`;
  * inversion: `thetaUnit_inv`, `kummer_thetaUnit_inv`, `kummerZHat_thetaUnit_inv`:
    `κ(θ(u⁻¹)) = κ(u) κ(θ(u))`;
  * the IUT-type values at `√q^{2j-1}` ([EtTh] §1): for `s² = q` in `K`, `theta_sqrt_ne_zero`
    (these points are never zeros), `theta_sqrt_zpow` (`θ(s^{2j-1}) = s^{-j²} θ(s⁻¹)`),
    `kummer_thetaUnit_sqrt`, `kummerZHat_thetaUnit_sqrt`:
    `κ(θ(s^{2j-1})) = κ(s)^{-j²} κ(θ(s⁻¹))`, so up to one common class these theta values have
    the Kummer classes of `q^{-j²/2}`;
  * compatibility with the `μ_n`-components: `h1Proj_kummerZHat_thetaUnit`;
  * base change and restriction: `algebraMap_theta` (`θ` commutes with every extension of
    valued fields `L/K`), `map_thetaUnit`, `restriction_kummer_thetaUnit`
    (`res_{L/K} κ_K(θ(u)) = κ_L(θ_{q_L}(u))`).
* **(ii) The Kummer class of `θ` as a function vs. its value** (`ThetaGerm.lean`). The function
  side is the germ of `θ` in the completed local ring `K⟦X⟧` at `u` (coordinate `u(1 + X)`):
  `thetaGerm u = ∑ₙ q^{e(n)} uⁿ (1 + X)ⁿ`, with integer binomial coefficients `binomCoeff n k`
  of `(1 + X)ⁿ`, `n ∈ ℤ`. It is the germ of `θ`: `hasSum_thetaGerm` (for `‖w‖ < 1`,
  `∑ₖ coeff_k(Θ_u) wᵏ = θ(u(1 + w))`, via `hasSum_binom` and Fubini); `constantCoeff_thetaGerm`
  (`Θ_u(0) = θ(u)`); `thetaGermUnit` (a unit off the divisor). For a field `F ⊇ K⟦X⟧` (`hCF`;
  e.g. `K((X))`, `laurentSeries_algebraMap_C`), `Ω/F` algebraic and a valuation subring
  `A ⊆ Ω` dominating `K⟦X⟧` (existence: `exists_valuationSubring_dominating`,
  `exists_valuationSubring_dominating_laurentSeries`), `decomposition_kummer_thetaGerm`: the
  restriction of `κ_F(Θ_u)` to the decomposition group `D_A` (coefficients reduced mod `𝔪_A`)
  is the inflation along `D_A → Gal(κ(A)/K)` of `κ_K(θ(u))`. Inputs: `residue_eq_pointEval`
  (reduction mod `A` is evaluation at `X = 0`), `kummerValue_thetaGermUnit`.
* **(iii) Over an algebraically closed field** (`ThetaGermClosed.lean`). The instance
  hypotheses of `decomposition_kummer_thetaGerm` on `κ(A)` and `Ω` are derived:
  `isAlgClosed_residueField` (the residue field of a valuation subring of an algebraically
  closed field is algebraically closed: lift a monic polynomial, take a root in `Ω`; it is
  integral over `A`, hence in `A`), `hasKummerRoots_of_isAlgClosed` (`n ≠ 0`, any
  characteristic), and `isIntegral_residueField`: if `Ω` is algebraic over `F = Frac K⟦X⟧`
  (`IsFractionRing K⟦X⟧ F`, e.g. `K((X))`) and `A` dominates `K⟦X⟧`, then `κ(A)` is algebraic
  over `K` (clear denominators of a polynomial over `F`, divide by the common power of `X`, reduce
  at `X = 0`); hence `isAlgClosure_residueField(_laurentSeries)`: `κ(A)` is an algebraic closure
  of `K`. Corollaries `decomposition_kummer_thetaGerm_of_isAlgClosed` (any `F = Frac K⟦X⟧`) and
  `decomposition_kummer_thetaGerm_laurentSeries` (`F = K((X))`, `Ω` e.g.
  `AlgebraicClosure K((X))`, canonical `K`-algebra structure on `κ(A)`): the only hypotheses left
  are `n ≠ 0`, that `A` dominates `K⟦X⟧` (such `A` exist), and `θ(u) ≠ 0`. The hypothesis
  `F = Frac K⟦X⟧` is genuinely needed for "κ(A) algebraic over K": for e.g. `F = K((X))(Y)`
  there are `A` dominating `K⟦X⟧` with the residue of `Y` transcendental over `K`, and then
  `Gal(κ(A)/K)` (with the Krull topology used by `kummer`) is not the profinite Galois group of
  an algebraic extension. `n ≠ 0` is needed since `HasKummerRoots 0` fails.

### Open / out of scope

* Theta and Kummer classes: there is no étale or tempered fundamental group of the Tate curve
  (or its `ℤ`-cover) in Mathlib, so the Kummer class of the *étale theta function* on
  `Π^{temp}` ([EtTh] Prop. 1.4 / Thm. 1.6) is not formalised; the function-vs-value comparison
  is local, in the completed local ring at the point and its decomposition groups. The
  hypotheses that `κ(A)` is algebraic over `K` with `n`-th roots are derived for `Ω`
  algebraically closed and algebraic over `Frac K⟦X⟧` (see (iii)). The theta values are over
  `K` itself (`u ∈ Kˣ`, `s ∈ K` with `s² = q`); points over extensions are handled by base change
  (`restriction_kummer_thetaUnit`).
* The reduction type is the repository's concrete notion (`HasSplitMultiplicativeReduction`: an
  integral model, reached by a change of variables, reducing to a split node at the origin), not
  a scheme-theoretic Néron/minimal-model notion. No norm is put on `K(√γ)` itself
  (`SqrtGammaField` is a bare `AdjoinRoot`; Mathlib's spectral norm needs a
  `NontriviallyNormedField` base): the `K(√γ)` statement is about the base change of `E_q`, and
  the valued form holds for any `[NormedField L] [NormedAlgebra K L]` in which `γ` is a square.
* Anabelian rigidity claims of *The Étale Theta Function* are out of scope by design.
  This repository is also distinct from `elliptic-reduction` (reduction theory; an empty
  scaffold at present).

## Dependencies

Mathlib (`v4.32.0`),
[`continuous-kummer-theory`](https://github.com/lana-agents/continuous-kummer-theory) (pinned at
`98b67df`, same Mathlib commit; used by `TateCurvesTheta/Kummer/`) and, as a Lake dependency only,
[`formal-schemes`](https://github.com/lana-agents/formal-schemes) (pinned in
`lakefile.toml`). No file currently imports `FormalSchemes`; the integral model and the
special fibre are done concretely over the unit ball (`integerRing`, `integerIdeal`).

Intended link, not a dependency: log-volumes
[`padic-log-volume`](https://github.com/lana-agents/padic-log-volume) (an empty scaffold
repository, not required in `lakefile.toml`).

## Use in `iut`

The converse V.5.3 (`TateCurvesTheta/Converse/`) generalises iut's
`Iut/Cor312/ThetaData/{UltrametricSqrt,TateIsomorphism}.lean` and the automorphism part of
`TateStructureUnique.lean`; iut does not use it yet (it pins an older commit).

[`lana-agents/iut`](https://github.com/lana-agents/iut) pins this repository at
`ca6c227` and uses it to build the local Θ-data at the bad places (`Iut/Cor312/ThetaData/`,
`Iut/Concrete/`): existence and uniqueness of the Tate parameter from the `j`-invariant
(`exists_tateParameter_tateJ_eq`, `tateJ_injective`,
`existsUnique_splitMultiplicative_tateParameter`), the uniformization `tateUniformization`
with `tatePoint_mem'`, `TameResidueChar`, `IsUniformizer`/`toOrdered` for the normalized
order, and the base-change naturality `baseChange`, `algebraMap_X`, `algebraMap_Y`.

## Established sources

* Tate's `q`-uniformization; J. Tate, *A review of non-Archimedean elliptic functions*.
* Mumford, *An analytic construction of degenerating abelian varieties over complete rings*
  (appendix to Faltings–Chai).
* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, Prop. 1.4.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `TateCurvesTheta/`, and every file must be imported from
the root module `TateCurvesTheta.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib TateCurvesTheta --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#13](https://taxis.lana.merten.dev/issues/13), [#36](https://taxis.lana.merten.dev/issues/36), [#37](https://taxis.lana.merten.dev/issues/37)

License: Apache 2.0 (see LICENSE)

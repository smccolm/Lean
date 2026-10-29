/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.TateCurve.WeierstrassIdentity
import TateCurvesTheta.Theta.Uniqueness

/-!
# The Tate parametrization Weierstrass identity `tatePoint_mem` (reduction via the engine)

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`) and a point
`u : Kˣ` off the `q`-orbit, Tate's analytic parametrization sends `u` to the affine point
`(X(u), Y(u))` on the Tate curve `E_q`; membership `(X(u), Y(u)) ∈ E_q` is the **Weierstrass
identity** (Silverman, *Advanced Topics*, Ch. V, Thm 3.1). By `Theta/WeierstrassIdentity.lean`
(#120) this reduces to the vanishing of the `q`-periodic **Weierstrass defect**
`tateDefect u = Y(u)² + X(u)·Y(u) - (X(u)³ + a₄·X(u) + a₆)` (`tatePoint_equation_iff`).

This file closes `tatePoint_mem` **modulo two precisely-stated inputs**, using the `q`-difference
uniqueness engine `TateParameter.const_of_qinvariant_laurent` of `Theta/Uniqueness.lean` (#119),
exactly as `Theta/TripleProduct.lean` (#124) closed `theta = thetaProd`:

1. `LaurentCoeffUnique K` — the nonarchimedean coefficient-uniqueness principle, discharged for
   densely-normed `K` in `Theta/StrictDominant.lean` (#121) and, unconditionally, via the
   Strassmann route (#122/#127/#130/#131/#136).
2. `DefectLaurentRepr t` — the **residual analytic seam**: the `q`-periodic defect `tateDefect`
   is represented, off the `q`-orbit, by a convergent, `q`-invariant two-sided Laurent series in
   `u`. See the definition below for the precise statement.

Given these, the engine forces the representing series to be the constant `d := c 0`, so
`tateDefect u = d` for every off-orbit `u` (`tateDefect_eq_const`). A single normalization value
`tateDefect u₀ = 0` at one off-orbit point pins `d = 0` and delivers the identity `tateDefect ≡ 0`,
hence `tatePoint_mem`.

## Why a Laurent representation, and why the `q`-invariance clause is bundled

The individual coordinate functions `X`, `Y` are genuinely `q`-periodic *elliptic* functions with
poles on the `q`-orbit `qᶻ` (a `q`-invariant global Laurent series would have to be constant by the
engine, which `X`, `Y` are not). Only the specific algebraic combination `tateDefect` is
pole-free: its poles at `qᶻ` cancel, so it extends to a `q`-periodic function with no poles, i.e.
a global convergent Laurent series — the analytic content still to be supplied. As in
`RatioLaurentRepr` (`Theta/TripleProduct.lean`), the series-level `q`-invariance clause is carried
*inside* the seam rather than derived from `tateDefect_q_smul`: the latter controls the defect only
**off** the discrete orbit, and propagating the shift relation across `qᶻ` to all coefficients needs
the continuity of the Laurent series plus density of `Kˣ ∖ qᶻ`, a topological input not yet in the
tree. It holds once the pole-cancellation Laurent development of the defect is carried out (the
deferred analytic work); this file delivers the reusable reduction that consumes it.

## Main definitions

* `TateCurvesTheta.TateParameter.DefectLaurentRepr` : the residual analytic seam above.

## Main results

* `TateParameter.tateDefect_eq_const` : given `LaurentCoeffUnique K` and `DefectLaurentRepr t`,
  the defect is a single constant `d` on the whole off-orbit locus.
* `TateParameter.tatePoint_mem` : with, in addition, one off-orbit normalization point `u₀` where
  `tateDefect u₀ = 0`, the Tate point `(X(u), Y(u))` lies on `E_q` for every off-orbit `u`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- **The residual analytic seam for the Weierstrass identity.** Off the `q`-orbit, the
`q`-periodic Weierstrass defect `tateDefect` is represented by a convergent, `q`-invariant
two-sided Laurent series: there is a coefficient family `c : ℤ → K` that is summable on all of
`Kˣ`, agrees with the defect at every off-orbit point
(`tateDefect u = ∑' n, cₙ uⁿ` whenever `qⁿ u ≠ 1` for all `n`), and whose series is `q`-invariant
(`∑' n, cₙ (q·u)ⁿ = ∑' n, cₙ uⁿ`).

This is the pole-cancellation "the defect is a pole-free `q`-periodic function" step flagged in
`WeierstrassIdentity.lean`; see the module docstring for why the `q`-invariance clause is bundled
here. It is exactly the shape consumed by `const_of_qinvariant_laurent`. -/
def DefectLaurentRepr : Prop :=
  ∃ c : ℤ → K,
    (∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) ∧
    (∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
      t.tateDefect u = ∑' n : ℤ, c n * (u : K) ^ n) ∧
    (∀ u : Kˣ,
      (∑' n : ℤ, c n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, c n * (u : K) ^ n)

/-- **The Weierstrass defect is constant off the `q`-orbit.** Given the coefficient-uniqueness
principle `LaurentCoeffUnique K` and the Laurent representation of the defect
(`DefectLaurentRepr t`), the `q`-difference engine `const_of_qinvariant_laurent` collapses the
representing series to its constant term `c₀ := c 0`, so `tateDefect u = c₀` for every off-orbit
`u : Kˣ`. -/
theorem tateDefect_eq_const (huniq : LaurentCoeffUnique K) (hrepr : t.DefectLaurentRepr) :
    ∃ d : K, ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) → t.tateDefect u = d := by
  obtain ⟨c, hsum, hid, hqinv⟩ := hrepr
  -- The engine forces the representing series to equal its constant term `c 0` everywhere.
  have hconst : ∀ u : Kˣ, (∑' n : ℤ, c n * (u : K) ^ n) = c 0 :=
    t.const_of_qinvariant_laurent huniq c hsum hqinv
  exact ⟨c 0, fun u hu => by rw [hid u hu, hconst u]⟩

/-- **The Tate parametrization Weierstrass identity.** Beyond the coefficient-uniqueness principle
and the defect's Laurent representation, all that is needed is one normalization value: a single
off-orbit point `u₀` where the defect already vanishes, `tateDefect u₀ = 0`. This pins the constant
`d` of `tateDefect_eq_const` to `0`, so the defect vanishes at every off-orbit `u`, and the Tate
point `(X(u), Y(u))` lies on the Tate curve `E_q`:
`Y(u)² + X(u)·Y(u) = X(u)³ + a₄·X(u) + a₆`. -/
theorem tatePoint_mem (huniq : LaurentCoeffUnique K) (hrepr : t.DefectLaurentRepr)
    {u₀ : Kˣ} (hu₀ : ∀ n : ℤ, (t.q : K) ^ n * (u₀ : K) ≠ 1) (hnorm : t.tateDefect u₀ = 0)
    {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u) := by
  obtain ⟨d, hd⟩ := t.tateDefect_eq_const huniq hrepr
  -- The shared constant `d` equals `tateDefect u₀ = 0`, so the defect vanishes off the orbit.
  have hdef : t.tateDefect u = 0 := by rw [hd u hu, ← hd u₀ hu₀, hnorm]
  exact (t.tatePoint_equation_iff u).mpr hdef

end TateParameter

end TateCurvesTheta

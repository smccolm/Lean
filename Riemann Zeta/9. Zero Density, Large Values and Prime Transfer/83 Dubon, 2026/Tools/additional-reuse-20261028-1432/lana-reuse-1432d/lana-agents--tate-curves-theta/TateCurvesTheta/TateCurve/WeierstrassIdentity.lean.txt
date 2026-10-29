/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import TateCurvesTheta.TateCurve.Parametrization

/-!
# The Tate parametrization Weierstrass identity: reduction to a `q`-periodic defect

For a Tate parameter `q` over a complete nonarchimedean field `K` and a point `u : Kˣ`
avoiding the `q`-orbit, Tate's analytic parametrization sends `u` to the affine point
`(X(u), Y(u))` on the Tate curve `E_q` (Silverman, *Advanced Topics*, Ch. V, Thm 3.1). The
statement that this point lies on `E_q` is the **Weierstrass identity**
```
Y(u)² + X(u)·Y(u) = X(u)³ + a₄(q)·X(u) + a₆(q).
```

This file develops the purely algebraic reduction of that membership statement. The full
identity itself is *not* proved here: its standard proofs either transport the `℘`-function
`q`-expansion identity from `ℂ` (a formal-power-series identity over `ℤ` verified analytically,
requiring the complex Weierstrass `℘`-theory that is not yet in the tree), or invoke a
nonarchimedean uniqueness principle for `q`-periodic functions with a prescribed divisor
(also not yet in the tree). What *is* established here is a clean, unconditional reduction that
isolates exactly the analytic content still to be supplied.

## Main definitions

* `TateCurvesTheta.TateParameter.tateDefect`: the **Weierstrass defect**
  `Y(u)² + X(u)·Y(u) - (X(u)³ + a₄·X(u) + a₆)`, whose vanishing is the Weierstrass identity.

## Main results

* `TateParameter.tateCurve_equation_iff`: the abstract predicate `E_q.Equation x y` unfolds to
  the concrete Weierstrass equation `y² + x·y = x³ + a₄·x + a₆` of the Tate curve.
* `TateParameter.tatePoint_equation_iff`: the Tate point `(X(u), Y(u))` lies on `E_q` **iff**
  the Weierstrass defect `tateDefect u` vanishes.
* `TateParameter.tateDefect_q_smul`: the Weierstrass defect is `q`-periodic,
  `tateDefect (q·u) = tateDefect u`, a direct consequence of the `q`-periodicity `X_q_smul`,
  `Y_q_smul` of the coordinate functions. This is the invariance underlying the
  elliptic-function-uniqueness route to the full identity: the defect descends to a function on
  the analytic quotient `Kˣ/qᶻ`, and the outstanding task is to show that function is
  identically zero.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- **Concrete Weierstrass equation of the Tate curve.** The abstract predicate
`E_q.Equation x y` (vanishing of the Weierstrass polynomial) unfolds, using the Tate
`a`-invariants `a₁ = 1`, `a₂ = a₃ = 0`, `a₄`, `a₆`, to the classical equation
`y² + x·y = x³ + a₄·x + a₆`. Purely algebraic; needs no analytic hypotheses. -/
lemma tateCurve_equation_iff (x y : K) :
    t.tateCurve.toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄, tateCurve_a₆]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- The **Weierstrass defect** of the Tate point `(X(u), Y(u))`:
`Y(u)² + X(u)·Y(u) - (X(u)³ + a₄·X(u) + a₆)`. The Weierstrass identity of Silverman's
Thm 3.1 is exactly the statement that this defect vanishes for every `u` off the `q`-orbit. -/
def tateDefect (u : Kˣ) : K :=
  t.Y u ^ 2 + t.X u * t.Y u - (t.X u ^ 3 + t.a₄ * t.X u + t.a₆)

lemma tateDefect_apply (u : Kˣ) :
    t.tateDefect u = t.Y u ^ 2 + t.X u * t.Y u - (t.X u ^ 3 + t.a₄ * t.X u + t.a₆) := rfl

/-- **Reduction of the Weierstrass identity to the vanishing of the defect.** The Tate point
`(X(u), Y(u))` lies on the Tate curve `E_q` if and only if `tateDefect u = 0`. This converts the
membership goal `tatePoint_mem` into the analytic identity `tateDefect u = 0`. -/
lemma tatePoint_equation_iff (u : Kˣ) :
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u) ↔ t.tateDefect u = 0 := by
  rw [tateCurve_equation_iff, tateDefect_apply, sub_eq_zero]

/-- **`q`-periodicity of the Weierstrass defect.** Because both coordinate functions are
`q`-periodic (`X_q_smul`, `Y_q_smul`) and the coefficients `a₄`, `a₆` are constants, the defect
satisfies `tateDefect (q·u) = tateDefect u`. Hence it descends to a well-defined function on the
analytic quotient `Kˣ/qᶻ`; proving that this descended function is identically zero (via
nonarchimedean elliptic-function uniqueness, or the `℘`-expansion transport) is exactly the
outstanding analytic input to the full identity. Unconditional. -/
lemma tateDefect_q_smul (u : Kˣ) : t.tateDefect (t.q * u) = t.tateDefect u := by
  simp only [tateDefect_apply, t.X_q_smul, t.Y_q_smul]

end TateParameter

end TateCurvesTheta

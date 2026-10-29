/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.TateCurve.SurjectivityAnnulus
import TateCurvesTheta.TateCurve.SurjectivitySphere

/-!
# The Tate uniformization isomorphism `Kˣ/qᶻ ≃* E_q(K)`

The capstone of the `q`-uniformization (issue #36): over a complete nonarchimedean field
with `TameResidueChar K` (`‖2‖ = 1 ∧ 12 ≠ 0`, i.e. residue characteristic `≠ 2` and
`12 ≠ 0`; residue characteristic `3` is allowed), the Tate point map is **surjective** — every
point of the Mordell–Weil group `E_q(K)` is `tatePoint u` for some unit `u` — and therefore the
injective homomorphism `Kˣ/qᶻ →* E_q(K)` of `GroupLaw.lean` is an **isomorphism**
(`tateUniformization`), completing the exact sequence

  `1 → qᶻ → Kˣ → E_q(K) → 0`.

Surjectivity is assembled from the three regions established in
`LargePointParametrization.lean` (`1 < ‖x‖`, fixed-point iteration),
`SurjectivitySphere.lean` (`‖x‖ = 1`, exact nodal lift and translation) and
`SurjectivityAnnulus.lean` (`‖x‖ < 1`, translation by explicit annulus points); the
degenerate configuration `‖x‖ < 1 = ‖y‖` is impossible on the curve.

## Main results

* `TateCurvesTheta.TateParameter.tatePoint_surjective`: the point map is surjective.
* `TateCurvesTheta.TateParameter.mapTatePointHom_bijective`.
* `TateCurvesTheta.TateParameter.tateUniformization`: the Tate uniformization
  isomorphism `Kˣ/qᶻ ≃* E_q(K)` (multiplicativized Mordell–Weil group).

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V,
  Theorem 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)
variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : TameResidueChar K)

/-- **Surjectivity of the Tate point map**: every point of the Mordell–Weil group of the
Tate curve is `tatePoint u` for some unit `u`. -/
theorem tatePoint_surjective : Function.Surjective (t.tatePoint hmem h12) := by
  classical
  intro P
  cases P with
  | zero => exact ⟨1, t.tatePoint_one hmem h12⟩
  | some x y hns =>
    have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
      (t.tateCurve_equation_iff x y).mp hns.1
    rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
    · have hy1 : ‖y‖ ≤ 1 := t.norm_y_le_one_of_norm_x_le_one h12 hxy hlt.le
      rcases lt_or_eq_of_le hy1 with hylt | hyeq
      · exact t.mem_range_tatePoint_of_annulus hmem h12 hns hlt hylt
      · -- `‖x‖ < 1 = ‖y‖` is impossible on the curve
        exfalso
        have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
        have hL : ‖y ^ 2 + x * y‖ = 1 := by
          have h1 : ‖x * y‖ < ‖y ^ 2‖ := by
            rw [norm_mul, norm_pow, hyeq, mul_one, one_pow]
            exact hlt
          rw [norm_add_eq_left_of_norm_lt h1, norm_pow, hyeq, one_pow]
        have hR : ‖x ^ 3 + t.a₄ * x + t.a₆‖ < 1 := by
          refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
            · rw [norm_pow]
              exact pow_lt_one₀ (norm_nonneg x) hlt (by omega)
            · rw [norm_mul]
              calc ‖t.a₄‖ * ‖x‖ ≤ ‖(t.q : K)‖ * 1 :=
                    mul_le_mul t.norm_a₄_le hlt.le (norm_nonneg x) (norm_nonneg _)
                _ < 1 := by rwa [mul_one]
          · exact (t.norm_a₆_le h12.2).trans_lt hq1
        rw [hxy] at hL
        linarith
    · exact t.mem_range_tatePoint_of_unit_sphere hmem h12 hns heq
        (t.norm_y_le_one_of_norm_x_le_one h12 hxy heq.le)
    · exact t.exists_tatePoint_eq_some hmem h12 hns hgt

/-- The descended homomorphism `Kˣ/qᶻ →* E_q(K)` is bijective. -/
theorem mapTatePointHom_bijective [DecidableEq K] :
    Function.Bijective (t.mapTatePointHom hmem h12) := by
  refine ⟨t.mapTatePointHom_injective hmem h12, ?_⟩
  intro P
  obtain ⟨u, hu⟩ := t.tatePoint_surjective hmem h12 (Multiplicative.toAdd P)
  refine ⟨t.toAnalyticQuotient u, ?_⟩
  rw [t.mapTatePointHom_mk hmem h12 u, hu]
  rfl

/-- **The Tate uniformization isomorphism** `Kˣ/qᶻ ≃* E_q(K)`: the analytic quotient is
isomorphic, as a group, to the Mordell–Weil group of the Tate curve (written
multiplicatively). This completes the exact sequence `1 → qᶻ → Kˣ → E_q(K) → 0` of the
`q`-uniformization. -/
noncomputable def tateUniformization [DecidableEq K] :
    t.AnalyticQuotient ≃* Multiplicative t.tateCurve.toAffine.Point :=
  MulEquiv.ofBijective (t.mapTatePointHom hmem h12)
    (t.mapTatePointHom_bijective hmem h12)

@[simp] lemma tateUniformization_apply_mk [DecidableEq K] (u : Kˣ) :
    t.tateUniformization hmem h12 (t.toAnalyticQuotient u)
      = Multiplicative.ofAdd (t.tatePoint hmem h12 u) :=
  t.mapTatePointHom_mk hmem h12 u

end TateParameter

end TateCurvesTheta

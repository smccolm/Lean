import Dubon2026.SourceEllipticLegendreGenerators

/-! The finite Galois Legendre good-model stage and its faithful inertia.
The generators are the actual two-torsion abscissae and square roots of
their nonzero differences. This realizes the model and action required by
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite Legendre model proof.
Native valuation-ring inertia and the existing explicit good model are reused.
No characteristic-zero Hahn-series route is introduced. -/
namespace Dubon2026.SourceEllipticLegendreStage
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open Dubon2026.SourceEllipticLegendre
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [DecidableEq Ω] {E : WeierstrassCurve F}
  (h2 : (2 : F) ≠ 0) {e₁ e₂ e₃ : Ω}
  (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
  (M : IntermediateField F Ω) (hM : IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) ≤ M)

include hM in
lemma mem_M_of_mem_gens {x : Ω} (hx : x ∈ gens e₁ e₂ e₃) : x ∈ M :=
  hM (IntermediateField.subset_adjoin F _ (Finset.mem_coe.mpr hx))

lemma e₁_mem_gens : e₁ ∈ gens e₁ e₂ e₃ := by simp [gens]
lemma e₂_mem_gens : e₂ ∈ gens e₁ e₂ e₃ := by simp [gens]
lemma e₃_mem_gens : e₃ ∈ gens e₁ e₂ e₃ := by simp [gens]

include h2 h3 hM in

lemma roots_M :
    (E.baseChange M).twoTorsionPolynomial.roots =
      {⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩, ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩,
        ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩} := by
  set f₁ : M := ⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩
  set f₂ : M := ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩
  set f₃ : M := ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩
  have ha := four_ne_zero E h2
  have h4M : (4 : M) ≠ 0 := by
    have : (E.baseChange M).twoTorsionPolynomial.a ≠ 0 := by
      rw [WeierstrassCurve.baseChange, ← map_twoTorsionPolynomial]
      show algebraMap F M E.twoTorsionPolynomial.a ≠ 0
      exact (_root_.map_ne_zero _).mpr ha
    exact this

  have hfac : (E.baseChange M).twoTorsionPolynomial.toPoly =
      Polynomial.C 4 * (X - Polynomial.C f₁) * (X - Polynomial.C f₂) * (X - Polynomial.C f₃) := by
    apply Polynomial.map_injective (algebraMap M Ω) (algebraMap M Ω).injective
    have h1 : ((E.baseChange M).twoTorsionPolynomial.toPoly).map (algebraMap M Ω) =
        (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).toPoly := by
      rw [WeierstrassCurve.baseChange, ← map_twoTorsionPolynomial, Cubic.map_toPoly, Cubic.map_toPoly,
        Polynomial.map_map]
      congr 1
    rw [h1, Cubic.eq_prod_three_roots ha h3]
    have hPa : E.twoTorsionPolynomial.a = 4 := rfl
    rw [hPa, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_C, map_ofNat, map_ofNat]
    rfl
  show (E.baseChange M).twoTorsionPolynomial.toPoly.roots = _
  rw [hfac, mul_assoc, mul_assoc, Polynomial.roots_C_mul _ h4M,
    Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero f₁)
      (mul_ne_zero (X_sub_C_ne_zero f₂) (X_sub_C_ne_zero f₃))),
    Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero f₂) (X_sub_C_ne_zero f₃)),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl


end
end Dubon2026.SourceEllipticLegendreStage

import Dubon2026.SourceEllipticLegendreValuation
import Dubon2026.SourceEllipticLegendreCoordinates

/-! The explicit Legendre good model for an elliptic curve with integral j.
The specified coordinate change is needed to prove faithfulness of the
realized inertia action, not just potential good reduction. This serves
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Legendre local model proof.
No Hasse-invariant development or characteristic-zero Hahn series is needed. -/
namespace Dubon2026.SourceEllipticLegendre
open WeierstrassCurve
noncomputable section
variable {M : Type*} [Field M]
theorem exists_legendre_good_model (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by
  have h2M : (2 : M) ≠ 0 := by
    have : ((2 : A) : M) ≠ 0 := fun h => h2.ne_zero (Subtype.ext h)
    exact this
  have h2v : A.valuation (2 : M) = 1 := by
    have := (A.valuation_eq_one_iff (2 : A)).mp h2
    exact this

  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2M h2M
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2M) E.isUnit_Δ
  obtain ⟨h12, h13, h23⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha he').mp hdisc
  have hw2 : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; exact hw2 (by rw [← hw]; ring)

  set l₀ : M := (e₃ - e₁) / (e₂ - e₁) with hl₀
  have hjl := j_mul_of_legendre E h2M he hw hw0
  obtain ⟨hvl, hvl1⟩ := val_lambda A ((A.valuation_le_one_iff _).mpr hj) h2v hjl
  have hlA : l₀ ∈ A := (A.valuation_le_one_iff _).mp hvl.le
  set l : A := ⟨l₀, hlA⟩ with hl
  have hlu : IsUnit l := (A.valuation_eq_one_iff l).mpr hvl
  have hl1u : IsUnit (1 - l) := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 : M) - l₀) = 1
    rw [← neg_sub, Valuation.map_neg]; exact hvl1
  refine ⟨l, ⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩, hlu, hl1u, ?_, rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  ·
    rw [legendre_Δ]
    have h16 : IsUnit (16 : A) := by
      rw [show (16 : A) = 2 ^ 4 by norm_num]; exact h2.pow 4
    have hlm1 : IsUnit (l - 1) := by
      rw [show l - 1 = -(1 - l) by ring]; exact hl1u.neg
    exact ((h16.mul (hlu.pow 2)).mul (hlm1.pow 2))
  · rw [legendre_map, variableChange_eq_legendre E h2M he hw hw0]
    rfl


end
end Dubon2026.SourceEllipticLegendre

import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic

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

/-- The actual Legendre equation y^2 = x(x-1)(x-l). -/
def legendreCurve {R : Type*} [CommRing R] (l : R) : WeierstrassCurve R :=
  ⟨0, -(1 + l), 0, l, 0⟩

section Model

variable (E : WeierstrassCurve M) [E.IsElliptic]

lemma legendre_Δ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma legendre_c₄ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [legendreCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma legendre_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : R) :
    (legendreCurve l).map φ = legendreCurve (φ l) := by
  simp only [legendreCurve, WeierstrassCurve.map]
  ext <;> simp

omit [E.IsElliptic] in
theorem variableChange_eq_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M) • E =
      legendreCurve ((e₃ - e₁) / (e₂ - e₁)) := by

  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hV1 := Cubic.b_eq_three_roots ha he'
  have hV2 := Cubic.c_eq_three_roots ha he'
  have hV3 := Cubic.d_eq_three_roots ha he'
  simp only [RingHom.id_apply, twoTorsionPolynomial] at hV1 hV2 hV3

  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hV1 hV2 hV3
  have hw2 : e₂ - e₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
  ext
  ·
    simp only [legendreCurve, variableChange_a₁, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    field_simp
    linear_combination hV1 + 4 * hw
  ·
    simp only [legendreCurve, variableChange_a₃, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    have hV2' : 2 * E.a₄ + E.a₁ * E.a₃ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
      apply mul_left_cancel₀ h2
      linear_combination hV2
    field_simp
    linear_combination hV2' + e₁ * hV1 + 2 * (e₁ - e₃) * hw
  ·
    simp only [legendreCurve, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0]

    have hroot : 4 * e₁ ^ 3 + E.b₂ * e₁ ^ 2 + 2 * E.b₄ * e₁ + E.b₆ = 0 := by
      have hmem : e₁ ∈ E.twoTorsionPolynomial.roots := by rw [he]; simp
      have hne : E.twoTorsionPolynomial.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
      have := (Cubic.mem_roots_iff hne e₁).mp hmem
      simpa [twoTorsionPolynomial] using this
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hroot
    field_simp
    linear_combination hroot

lemma j_legendre_mul (l : M) [(legendreCurve l).IsElliptic] :
    (legendreCurve l).j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3 := by
  have hjΔ : (legendreCurve l).j * (legendreCurve l).Δ = (legendreCurve l).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← coe_Δ', Units.mul_inv, one_mul]
  rw [legendre_Δ, legendre_c₄] at hjΔ
  have h16 : (16 : M) ≠ 0 := by
    intro h
    apply (legendreCurve l).isUnit_Δ.ne_zero
    rw [legendre_Δ, h]; ring
  apply mul_left_cancel₀ h16
  linear_combination hjΔ

lemma j_mul_of_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    E.j * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 * ((e₃ - e₁) / (e₂ - e₁) - 1) ^ 2) =
      256 * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 - (e₃ - e₁) / (e₂ - e₁) + 1) ^ 3 := by
  have hκ := variableChange_eq_legendre E h2 he hw hw0
  haveI : (legendreCurve ((e₃ - e₁) / (e₂ - e₁))).IsElliptic := by rw [← hκ]; infer_instance
  have hj : E.j = (legendreCurve ((e₃ - e₁) / (e₂ - e₁))).j := by
    have h1 := variableChange_j E
      (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M)
    have h2' : ∀ (V₁ V₂ : WeierstrassCurve M) [V₁.IsElliptic] [V₂.IsElliptic], V₁ = V₂ → V₁.j = V₂.j := by
      rintro V₁ V₂ _ _ rfl; rfl
    rw [← h1]
    exact h2' _ _ hκ
  rw [hj]
  exact j_legendre_mul _

end Model


end
end Dubon2026.SourceEllipticLegendre

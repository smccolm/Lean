import Dubon2026.SourceOriginalWeilPrincipalInvariance
import Dubon2026.SourceOriginalWeilRepresentatives

/-! DUB-17/18 -> original Weil pairing descent. One moved first divisor
avoiding both second supports joins any two representatives of the same
pair of actual Picard torsion classes. Principal-shift invariance then
removes both representative choices. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
open scoped Classical
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable {n : ℕ} [NeZero n]

theorem pairing_eq_of_classLeft_eq (d d' : OriginalWeilDatum N L n)
    (hD₂ : d'.D₂ = d.D₂) (hx : d'.classLeft = d.classLeft) : d'.pairing = d.pairing := by
  apply pairing_eq_of_isPrincipal_sub_left d d' hD₂
  have he : Pic0.mk (⟨d'.D₁, d'.degree_first⟩ - ⟨d.D₁, d.degree_first⟩) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hx)
  exact (Pic0.mk_eq_zero_iff _).mp he

theorem pairing_eq_of_classRight_eq (d d' : OriginalWeilDatum N L n)
    (hD₁ : d'.D₁ = d.D₁) (hy : d'.classRight = d.classRight) : d'.pairing = d.pairing := by
  apply pairing_eq_of_isPrincipal_sub_right d d' hD₁
  have he : Pic0.mk (⟨d'.D₂, d'.degree_second⟩ - ⟨d.D₂, d.degree_second⟩) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hy)
  exact (Pic0.mk_eq_zero_iff _).mp he

theorem pairing_eq_of_classes_eq (d d' : OriginalWeilDatum N L n)
    (hx : d'.classLeft = d.classLeft) (hy : d'.classRight = d.classRight) :
    d'.pairing = d.pairing := by
  obtain ⟨A, hA, havoid⟩ := originalPic0_representative_avoiding N L d.classLeft.val
    (d.D₂.support ∪ d'.D₂.support)
  have ht : Pic0.mk A ∈ Pic0.torsion n := hA.symm ▸ d.classLeft.property
  obtain ⟨a, ha, horda⟩ := (Pic0.mk_mem_torsion_iff A n).mp ht
  have ho (v : Place L (modularFunctionFieldOver N L)) : v.ord a = n * A.val v := by
    simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (horda v).symm
  let dA : OriginalWeilDatum N L n := {
    D₁ := A.val
    D₂ := d.D₂
    f₁ := a
    f₂ := d.f₂
    f₁_ne_zero := ha
    f₂_ne_zero := d.f₂_ne_zero
    ord_f₁ := ho
    ord_f₂ := d.ord_f₂
    disjoint := fun v => by
      by_cases hv : d.D₂ v = 0
      · exact Or.inr hv
      · exact Or.inl (havoid v (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))) }
  let dB : OriginalWeilDatum N L n := {
    D₁ := A.val
    D₂ := d'.D₂
    f₁ := a
    f₂ := d'.f₂
    f₁_ne_zero := ha
    f₂_ne_zero := d'.f₂_ne_zero
    ord_f₁ := ho
    ord_f₂ := d'.ord_f₂
    disjoint := fun v => by
      by_cases hv : d'.D₂ v = 0
      · exact Or.inr hv
      · exact Or.inl (havoid v (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))) }
  have hAx : dA.classLeft = d.classLeft := Subtype.ext hA
  have hBx : dB.classLeft = d'.classLeft := (Subtype.ext hA).trans hx.symm
  calc
    d'.pairing = dB.pairing := pairing_eq_of_classLeft_eq dB d' rfl hBx.symm
    _ = dA.pairing := pairing_eq_of_classRight_eq dA dB rfl hy
    _ = d.pairing := pairing_eq_of_classLeft_eq d dA rfl hAx

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum

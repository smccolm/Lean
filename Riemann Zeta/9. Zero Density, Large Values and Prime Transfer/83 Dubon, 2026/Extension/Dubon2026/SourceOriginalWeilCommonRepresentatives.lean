import Dubon2026.SourceOriginalWeilPairingDescent

/-! DUB-17/18 -> original Tate pairing -> bilinearity of the descended
Weil pairing. Move each first divisor away from a single second divisor,
so addition uses the same second principal function. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]

theorem exists_original_weil_common_right
    (x x' y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    ∃ d d' : OriginalWeilDatum N L n, d.D₂ = d'.D₂ ∧ d.f₂ = d'.f₂ ∧
      d.classLeft = x ∧ d'.classLeft = x' ∧ d.classRight = y ∧ d'.classRight = y := by
  obtain ⟨d, hx, hy⟩ := exists_original_weil_representative N L n x y
  obtain ⟨A, hA, havoid⟩ := originalPic0_representative_avoiding N L x'.val d.D₂.support
  have ht : Pic0.mk A ∈ Pic0.torsion n := hA.symm ▸ x'.property
  obtain ⟨a, ha, horda⟩ := (Pic0.mk_mem_torsion_iff A n).mp ht
  let d' : OriginalWeilDatum N L n := {
    D₁ := A.val
    D₂ := d.D₂
    f₁ := a
    f₂ := d.f₂
    f₁_ne_zero := ha
    f₂_ne_zero := d.f₂_ne_zero
    ord_f₁ := fun v => by simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (horda v).symm
    ord_f₂ := d.ord_f₂
    disjoint := fun v => by
      by_cases hv : d.D₂ v = 0
      · exact Or.inr hv
      · exact Or.inl (havoid v (Finsupp.mem_support_iff.mpr hv)) }
  exact ⟨d, d', rfl, rfl, hx, Subtype.ext hA, hy, hy⟩

namespace OriginalWeilDatum
variable {N L n}

omit [IsAlgClosed L] in
theorem classLeft_addLeft (d d' : OriginalWeilDatum N L n) (hD : d.D₂ = d'.D₂) :
    (d.addLeft d' hD).classLeft = d.classLeft + d'.classLeft := by
  apply Subtype.ext
  exact Pic0.mk.map_add ⟨d.D₁, d.degree_first⟩ ⟨d'.D₁, d'.degree_first⟩

omit [IsAlgClosed L] in
theorem classRight_addLeft (d d' : OriginalWeilDatum N L n) (hD : d.D₂ = d'.D₂) :
    (d.addLeft d' hD).classRight = d.classRight := rfl

end OriginalWeilDatum
end
end Dubon2026.SourceFunctionField

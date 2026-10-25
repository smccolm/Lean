import Dubon2026.SourceOriginalClosedPicardMoving
import Dubon2026.SourceOriginalWeilClasses

/-! DUB-17/18 -> original Weil pairing descent. Every pair of actual
Picard n-torsion classes has disjoint divisor/function representatives.
The existing quotient torsion criterion supplies the principal multiples;
the proved moving theorem supplies disjoint support over arithmetic constants. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem exists_original_weil_representative (n : ℕ) [NeZero n]
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    ∃ d : OriginalWeilDatum N L n, d.classLeft = x ∧ d.classRight = y := by
  obtain ⟨D₁, hD₁, _⟩ := originalPic0_representative_avoiding N L x.val ∅
  obtain ⟨D₂, hD₂, havoid⟩ := originalPic0_representative_avoiding N L y.val D₁.val.support
  have ht₁ : Pic0.mk D₁ ∈ Pic0.torsion n := hD₁.symm ▸ x.property
  have ht₂ : Pic0.mk D₂ ∈ Pic0.torsion n := hD₂.symm ▸ y.property
  obtain ⟨f₁, hf₁, hord₁⟩ := (Pic0.mk_mem_torsion_iff D₁ n).mp ht₁
  obtain ⟨f₂, hf₂, hord₂⟩ := (Pic0.mk_mem_torsion_iff D₂ n).mp ht₂
  let d : OriginalWeilDatum N L n := {
    D₁ := D₁.val
    D₂ := D₂.val
    f₁ := f₁
    f₂ := f₂
    f₁_ne_zero := hf₁
    f₂_ne_zero := hf₂
    ord_f₁ := fun v => by simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (hord₁ v).symm
    ord_f₂ := fun v => by simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (hord₂ v).symm
    disjoint := fun v => by
      by_cases hv : D₁.val v = 0
      · exact Or.inl hv
      · exact Or.inr (havoid v (Finsupp.mem_support_iff.mpr hv)) }
  exact ⟨d, Subtype.ext hD₁, Subtype.ext hD₂⟩

end
end Dubon2026.SourceFunctionField

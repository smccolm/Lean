import Dubon2026.SourceModularGaussConstants

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction -> actual
Gauss residue image. The normalized numerator and denominator belong to the
same modular field and have nonzero reductions. Their quotient is a Gauss unit,
so integrality of the original element forces its scalar factor into the
valuation ring of constants. The proved coefficient-specialization theorem then
puts its residue in the actual residue modular field. This avoids the external
second residue-basis and extension-degree argument. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open IntermediateField
variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

theorem resHom_mem_coefficient_field (hNL : (N : L) ≠ 0)
    (hNk : (N : IsLocalRing.ResidueField A) ≠ 0) (f : gaussRing A N) :
    resHom A N f ∈ modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) := by
  by_cases hf : (f : modularFunctionFieldCoeff N L) = 0
  · have he : f = 0 := Subtype.ext hf
    rw [he, map_zero]
    exact zero_mem _
  obtain ⟨c, _, x, y, hx, hy, hxF, hyF, h⟩ := exists_frac_form A N f hf
  let X : modularFunctionFieldCoeff N L := ⟨ι A x, hxF⟩
  let Y : modularFunctionFieldCoeff N L := ⟨ι A y, hyF⟩
  have hx0 : ι A x ≠ 0 := fun he => hx (by rw [(ι_eq_zero_iff A x).mp he, map_zero])
  have hX : X⁻¹ ∈ gaussRing A N := by
    refine ⟨1, x, hx, ?_⟩
    change (ι A x)⁻¹ * ι A x = ι A 1
    rw [inv_mul_cancel₀ hx0, map_one]
  have he : algebraMap L (modularFunctionFieldCoeff N L) c =
      (f : modularFunctionFieldCoeff N L) * Y * X⁻¹ := by
    apply Subtype.ext
    change algebraMap L (LaurentSeries L) c =
      ((f : modularFunctionFieldCoeff N L) : LaurentSeries L) * ι A y * (ι A x)⁻¹
    rw [h, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
  have hc : c ∈ A := (algebraMap_mem_gaussRing_iff A N c).mp (by
    rw [he]
    exact (gaussRing A N).mul_mem _ _
      ((gaussRing A N).mul_mem _ _ f.2 (ι_mem_gaussRing A N hyF)) hX)
  have hw : ((f : modularFunctionFieldCoeff N L) : LaurentSeries L) * ι A y =
      ι A (HahnSeries.C (⟨c, hc⟩ : A) * x) := by
    rw [map_mul, ι_C]
    exact h
  rw [resHom_eq A N hy hw, map_mul, ϖ_C]
  exact div_mem (mul_mem ((modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).algebraMap_mem _)
    (integral_modular_coefficient_specializes A N hNL hNk x hxF))
    (integral_modular_coefficient_specializes A N hNL hNk y hyF)

end
end Dubon2026.SourceFunctionField.GaussReduction

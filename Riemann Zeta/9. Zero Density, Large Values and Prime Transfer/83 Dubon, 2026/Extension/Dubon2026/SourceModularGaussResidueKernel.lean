import Dubon2026.SourceModularGaussResidueHom

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
actual modular Gauss residue map. Choose literal integral Laurent fraction
witnesses, prove independence of that choice by cross multiplication, and
construct the coefficient-reduction ring homomorphism. Its kernel is exactly
the maximal ideal, and its restriction to constants is the original valuation.
Actual residue-image identification and good reduction are subsequent consumers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, constant-reduction construction. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IntermediateField

variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ)
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A

theorem resHom_eq_zero_iff (f : gaussRing A N) :
    resHom A N f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A N) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨hy, h⟩ := wit_spec A N f
  constructor
  · rintro h0 ⟨u, rfl⟩
    have := congrArg (resHom A N) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hu
    by_contra h0
    apply hu
    rw [resHom_eq A N hy h, div_eq_zero_iff, or_iff_left hy] at h0
    have hf0 : ((f : FF) : LaurentSeries L) ≠ 0 := by
      intro hf
      rw [hf, zero_mul, eq_comm, ι_eq_zero_iff] at h
      exact h0 (by rw [h, map_zero])
    have hf0' : (f : FF) ≠ 0 := fun h' => hf0 (by rw [h']; rfl)
    have hinv : (f : FF)⁻¹ ∈ gaussRing A N := by
      refine ⟨(wit A N f).2, (wit A N f).1, h0, ?_⟩
      rw [IntermediateField.coe_inv]
      exact IsInt.inv_of (A := A) h0 h
    exact ⟨⟨f, ⟨(f : FF)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'),
      Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩


end
end Dubon2026.SourceFunctionField.GaussReduction

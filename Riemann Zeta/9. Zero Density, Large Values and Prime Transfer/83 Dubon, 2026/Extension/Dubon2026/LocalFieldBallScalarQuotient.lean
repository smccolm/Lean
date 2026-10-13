import Dubon2026.LocalFieldBallIntegerCoordinates

/-! # Exact scalar quotient of original local balls

This identifies the additive ball quotient in DUB-17's local power-index
calculation with the original integer ring modulo the actual scalar ideal.
It uses the existing valuation divisibility criterion, without a p-adic
principal-unit classification.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- The original local-field NontriviallyNormedField structure used for this calculation. -/
local instance localFieldBallScalarQuotientNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- The original local-field IsUltrametricDist structure used for this calculation. -/
local instance localFieldBallScalarQuotientUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- Scaling the original integer ring by a nonzero field element preserves
the exact quotient by an original nonzero integral scalar. -/
def localFieldIntegerBallQuotientEquiv (a : K) (ha : a ≠ 0)
    (r : 𝒪[K]) (hr : r ≠ 0) :
    (𝒪[K] ⧸ (Ideal.span {r} : Ideal 𝒪[K]).restrictScalars ℤ) ≃ₗ[ℤ]
      normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha) ⧸
        (normedFieldBallModule K ‖(r : K) * a‖
          (norm_pos_iff.mpr (mul_ne_zero (by exact_mod_cast hr) ha))).comap
            (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha)).subtype := by
  let A := normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha)
  let B := normedFieldBallModule K ‖(r : K) * a‖
    (norm_pos_iff.mpr (mul_ne_zero (by exact_mod_cast hr) ha))
  let I : Submodule ℤ 𝒪[K] := (Ideal.span {r} : Ideal 𝒪[K]).restrictScalars ℤ
  let e := localFieldIntegerBallEquiv K a ha
  have hm (x : 𝒪[K]) : e x ∈ B.comap A.subtype ↔ x ∈ I := by
    change (e x : K) ∈ B ↔ x ∈ (Ideal.span {r} : Ideal 𝒪[K])
    rw [normedFieldBallModule_mem, localFieldIntegerBallEquiv_apply, norm_mul, norm_mul,
      mul_comm ‖(r : K)‖ ‖a‖, mul_le_mul_iff_right₀ (norm_pos_iff.mpr ha),
      localFieldOriginalNorm_le_iff, Ideal.mem_span_singleton]
    exact (Valuation.integer.integers (ValuativeRel.valuation K)).le_iff_dvd
  apply Submodule.Quotient.equiv I (B.comap A.subtype) e
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hm x).mpr hx
  · intro hy
    refine ⟨e.symm y, (hm (e.symm y)).mp ?_, e.apply_symm_apply y⟩
    simpa only [e.apply_symm_apply] using hy

/-- The original additive ball quotient has precisely the scalar ideal
quotient cardinality in the original integer ring. -/
theorem localFieldBallScalarQuotient_card (a : K) (ha : a ≠ 0)
    (r : 𝒪[K]) (hr : r ≠ 0) :
    Nat.card (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha) ⧸
      (normedFieldBallModule K ‖(r : K) * a‖
        (norm_pos_iff.mpr (mul_ne_zero (by exact_mod_cast hr) ha))).comap
          (normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha)).subtype) =
      Nat.card (𝒪[K] ⧸ (Ideal.span {r} : Ideal 𝒪[K])) := by
  exact Nat.card_congr (localFieldIntegerBallQuotientEquiv K a ha r hr).symm.toEquiv

end
end Dubon2026

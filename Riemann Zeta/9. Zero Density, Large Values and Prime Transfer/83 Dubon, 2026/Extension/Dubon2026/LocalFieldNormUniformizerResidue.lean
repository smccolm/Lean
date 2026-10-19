import Dubon2026.LocalFieldGaloisNormOrder

/-! The existing cyclotomic identity N(zeta - 1) = p will discharge the
order-one norm input below. Its consequence is actual residue degree one,
the total-ramification input for the fixed tame quotient in the local
deformation rings serving Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [ValuativeRel K] [ValuativeRel L]
  [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- An actual field norm of normalized order one forces the original
residue extension to have degree one. -/
theorem localField_residue_degree_one_of_norm_order_one
    (v : Lˣ)
    (hv : localFieldUnitOrder K
      (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) = 1) :
    Module.finrank 𝓀[K] 𝓀[L] = 1 := by
  rw [localField_galois_norm_order K L] at hv
  apply Nat.eq_one_of_dvd_one
  apply Int.natCast_dvd_natCast.mp
  exact ⟨localFieldUnitOrder L (Additive.ofMul v), hv.symm⟩

/-- The same norm witness proves that every original extension residue
comes from the original base residue field. -/
theorem localField_residue_surjective_of_norm_order_one
    (v : Lˣ)
    (hv : localFieldUnitOrder K
      (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) = 1) :
    Function.Surjective (algebraMap 𝓀[K] 𝓀[L]) := by
  have hd := localField_residue_degree_one_of_norm_order_one K L v hv
  intro x
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero).mp hd x
  exact ⟨a, by simpa only [Algebra.smul_def, mul_one] using ha⟩

end
end Dubon2026

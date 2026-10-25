import Dubon2026.SourceCurveFiberPlaces
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-! DUB-17/18 -> original Frobenius determinant -> divisorial Weil
reciprocity and Hecke adjointness -> evaluation of a norm on a place fiber.
The first required step identifies reduction of the actual integral norm
with the norm in the actual residue-fiber algebra. Reuse native integral
closures and determinant base change. Decomposition into ramified local
factors and the evaluation formula remain subsequent obligations.
Selected from S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra F E]

variable (E) in
/-- Extension of the actual base-place maximal ideal to its integral closure. -/
abbrev residueFiberIdeal (v : Place K F) : Ideal (integralClosureAt E v) :=
  (maximalIdeal v.toValuationSubring).map (algebraMap v.toValuationSubring (integralClosureAt E v))

theorem residueFiberIdeal_ne_bot (v : Place K F) : residueFiberIdeal E v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hm : algebraMap v.toValuationSubring (integralClosureAt E v) π ∈ residueFiberIdeal E v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hm
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hm, map_zero]))

variable (E) in
/-- The canonical residue-field algebra on the actual residue-fiber quotient. -/
instance residueFiberQuotientAlgebra (v : Place K F) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt E v ⧸ residueFiberIdeal E v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem residue_norm_eq_norm_residueFiber (v : Place K F) (c : integralClosureAt E v) :
    IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c) =
      Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (residueFiberIdeal E v) c) := by
  letI : Module.Free v.toValuationSubring (integralClosureAt E v) :=
    Module.free_of_finite_type_torsion_free'
  have hequiv := Algebra.norm_eq_of_algEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := v.toValuationSubring)
      (integralClosureAt E v) (maximalIdeal v.toValuationSubring))
    (Ideal.Quotient.mk (residueFiberIdeal E v) c)
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk] at hequiv
  have hbase : algebraMap v.toValuationSubring
      (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
        (Algebra.norm v.toValuationSubring c) =
      Algebra.norm (v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
        ((1 : v.toValuationSubring ⧸ maximalIdeal v.toValuationSubring)
          ⊗ₜ[v.toValuationSubring] c) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]
  exact hbase.trans hequiv

end
end Dubon2026.SourceCurve.Place

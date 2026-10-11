import Dubon2026.UnramifiedLocalFieldNormImage
import Dubon2026.ContinuousCyclicGaloisNormQuotient
import Mathlib.Data.ZMod.Basic

/-! # Normalized order realizes the actual unramified field-norm quotient -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Original normalized integer order reduced modulo the displayed integer. -/
def localFieldUnitOrderMod (n : ℕ) : Additive Kˣ →ₗ[ℤ] ZMod n :=
  ((Int.castAddHom (ZMod n)).comp (localFieldUnitOrder K)).toIntLinearMap

/-- Surjectivity of the actual normalized order survives its original reduction. -/
theorem localFieldUnitOrderMod_surjective (n : ℕ) :
    Function.Surjective (localFieldUnitOrderMod K n) :=
  ZMod.intCast_surjective.comp (localFieldUnitOrder_surjective K)

variable {K} {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The kernel of original normalized order modulo the extension degree
is exactly the range of the original field-unit norm. -/
theorem unramifiedLocalField_orderMod_ker :
    LinearMap.ker (localFieldUnitOrderMod K (Module.finrank K L)) =
      LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)) := by
  ext u
  change (localFieldUnitOrder K u : ZMod (Module.finrank K L)) = 0 ↔ _
  rw [CharP.intCast_eq_zero_iff]
  have h : (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u.toMul) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K u :=
    unramifiedLocalField_mem_normRange_iff_order_dvd (L := L) u.toMul
  rw [← h]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.toMul, congrArg Additive.toMul hv⟩

/-- Actual normalized order identifies the original unramified field-norm
quotient with the actual residue class group of the extension degree. -/
def unramifiedLocalNormQuotientEquiv :
    (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L))) ≃ₗ[ℤ]
      ZMod (Module.finrank K L) :=
  (Submodule.quotEquivOfEq _ _ (unramifiedLocalField_orderMod_ker (K := K) (L := L)).symm).trans
    ((localFieldUnitOrderMod K (Module.finrank K L)).quotKerEquivOfSurjective
      (localFieldUnitOrderMod_surjective K (Module.finrank K L)))

/-- The actual norm quotient map has exactly the original normalized order formula. -/
theorem unramifiedLocalNormQuotientEquiv_mk (u : Additive Kˣ) :
    unramifiedLocalNormQuotientEquiv (L := L) (Submodule.Quotient.mk u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) := by
  rfl

end
end Dubon2026

import Dubon2026.LocalFieldUnitValuationSequence

/-! # An actual fixed uniformizer splits the original valuation sequence

Integral powers of the specified original invariant unit of order one
give an equivariant section of the existing field-unit valuation map.
This is the narrower input needed to prove outside-support integer-unit
acyclicity in DUB-17 without another completion model or norm-lifting proof.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped ValuativeRel
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)

/-- Integral powers of the actual invariant uniformizer define an original representation morphism. -/
def localFieldFixedUniformizerSection :
    Rep.trivial ℤ Gal(L/K) ℤ ⟶ Rep.ofAlgebraAutOnUnits K L := by
  refine Rep.ofHom ⟨LinearMap.toSpanSingleton ℤ (Rep.ofAlgebraAutOnUnits K L)
    (Rep.toAdditive.symm (Additive.ofMul π)), ?_⟩
  intro σ
  apply LinearMap.ext
  intro n
  change π ^ n = σ • (π ^ n)
  rw [smul_zpow', hfixed]

/-- The actual unit of order one gives a right inverse to the original valuation map. -/
theorem localFieldFixedUniformizerSection_comp
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    localFieldFixedUniformizerSection K L π hfixed ≫
        (localFieldUnitValuationShortComplex K L).g = 𝟙 (Rep.trivial ℤ Gal(L/K) ℤ) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  change localFieldUnitOrder L (n • Additive.ofMul π) = n
  simp only [map_zsmul, hπ, zsmul_eq_mul, Int.cast_id, mul_one]

end
end Dubon2026

import Dubon2026.AdelicDirichletCharacter
import Dubon2026.AdelicScalarCoordinates

/-! # The actual full rational idele group and its real/finite coordinates -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- The original full idele group is isomorphic to its genuine real and finite unit groups. -/
def rationalIdeleCoordinateEquiv : (AdeleRing ℤ ℚ)ˣ ≃* (ℝˣ × (FiniteAdeleRing ℤ ℚ)ˣ) :=
  (Units.mapEquiv rationalAdeleRealFiniteRingEquiv.toMulEquiv).trans MulEquiv.prodUnits

/-- The actual group equivalence uses exactly the original real and finite idele homomorphisms. -/
theorem rationalIdeleCoordinateEquiv_apply (a : (AdeleRing ℤ ℚ)ˣ) :
    rationalIdeleCoordinateEquiv a = (rationalIdeleRealHom a, rationalIdeleFiniteHom a) := rfl

/-- The inverse original idele coordinate map is precisely the original prescribed unit pair. -/
theorem rationalIdeleCoordinateEquiv_symm (r : ℝˣ) (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    rationalIdeleCoordinateEquiv.symm (r, a) = rationalAdeleUnitPair r a := rfl

/-- Equality of both original unit coordinates determines the original full idele. -/
theorem rationalIdele_ext (a b : (AdeleRing ℤ ℚ)ˣ)
    (hr : rationalIdeleRealHom a = rationalIdeleRealHom b)
    (hf : rationalIdeleFiniteHom a = rationalIdeleFiniteHom b) : a = b :=
  rationalIdeleCoordinateEquiv.injective (Prod.ext hr hf)

/-- The actual real unit embedding in the original full rational ideles. -/
def rationalIdeleRealEmbedding : ℝˣ →* (AdeleRing ℤ ℚ)ˣ where
  toFun r := rationalIdeleCoordinateEquiv.symm (r, 1)
  map_one' := map_one rationalIdeleCoordinateEquiv.symm
  map_mul' r s := by
    simpa only [Prod.mk_mul_mk, one_mul] using
      map_mul rationalIdeleCoordinateEquiv.symm (r, 1) (s, 1)

/-- The actual finite unit embedding in the original full rational ideles. -/
def rationalIdeleFiniteEmbedding : (FiniteAdeleRing ℤ ℚ)ˣ →* (AdeleRing ℤ ℚ)ˣ where
  toFun a := rationalIdeleCoordinateEquiv.symm (1, a)
  map_one' := map_one rationalIdeleCoordinateEquiv.symm
  map_mul' a b := by
    simpa only [Prod.mk_mul_mk, one_mul] using
      map_mul rationalIdeleCoordinateEquiv.symm (1, a) (1, b)

/-- Each original idele is the product of its actual real and finite coordinate embeddings. -/
theorem rationalIdele_real_mul_finite (a : (AdeleRing ℤ ℚ)ˣ) :
    rationalIdeleRealEmbedding (rationalIdeleRealHom a) *
      rationalIdeleFiniteEmbedding (rationalIdeleFiniteHom a) = a := by
  apply rationalIdeleCoordinateEquiv.injective
  rw [map_mul]
  change rationalIdeleCoordinateEquiv (rationalIdeleCoordinateEquiv.symm _) *
    rationalIdeleCoordinateEquiv (rationalIdeleCoordinateEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, rationalIdeleCoordinateEquiv_apply]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

/-- The actual real embedding is continuous in the original full unit topology. -/
theorem rationalIdeleRealEmbedding_continuous : Continuous rationalIdeleRealEmbedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact rationalAdeleRealFiniteRingEquiv_symm_continuous.comp
      (Units.continuous_val.prodMk continuous_const)
  · exact rationalAdeleRealFiniteRingEquiv_symm_continuous.comp
      (Units.continuous_coe_inv.prodMk continuous_const)

/-- The actual finite embedding is continuous in the original full unit topology. -/
theorem rationalIdeleFiniteEmbedding_continuous : Continuous rationalIdeleFiniteEmbedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact rationalAdeleRealFiniteRingEquiv_symm_continuous.comp
      (continuous_const.prodMk Units.continuous_val)
  · exact rationalAdeleRealFiniteRingEquiv_symm_continuous.comp
      (continuous_const.prodMk Units.continuous_coe_inv)

/-- A principal rational idele factors into its actual embedded real and finite rational units. -/
theorem rationalIdele_principal_factor (q : ℚˣ) :
    Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q =
      rationalIdeleRealEmbedding (Units.map (Rat.castHom ℝ).toMonoidHom q) *
        rationalIdeleFiniteEmbedding (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q) := by
  have h := rationalIdele_real_mul_finite
    (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q)
  rw [rationalIdeleRealHom_rational, rationalIdeleFiniteHom_rational] at h
  exact h.symm

end
end Dubon2026

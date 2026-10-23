import Dubon2026.SourceOriginalHeckeAllPrimeAbel
import Dubon2026.SourceOriginalPathIntegralLinearCombination
import Dubon2026.HeckePrimeLinear

/-! DUB-17/18 -> original Jacobian Tate Hecke realization -> actual
period Hecke operator at every prime, including primes dividing the level. Use the proved regular-differential/cusp-form
equivalence and the native basis-dual equivalence. This is the transpose
of the genuine analytic Hecke operator, with no chosen matrix or
compatibility premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]

private local instance (ell : Nat.Primes) : NeZero ell.val :=
  ⟨ell.property.ne_zero⟩

/-- The genuine analytic Hecke operator on the original regular differentials. -/
def originalPrimeRegularHecke (ell : Nat.Primes) :
    Module.End ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :=
  (originalRegularCuspEquiv N).symm.toLinearMap.comp
    ((cuspHeckePrimeLinear 2 ell.property).comp (originalRegularCuspEquiv N).toLinearMap)

theorem originalPrimeRegularHecke_cusp (ell : Nat.Primes)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalRegularCuspEquiv N (originalPrimeRegularHecke N ell ω) =
      cuspHeckePrime ell.property (originalRegularCuspEquiv N ω) :=
  (originalRegularCuspEquiv N).apply_symm_apply _

/-- Dual Hecke action in the coordinates of an actual original regular basis. -/
def originalPrimePeriodHecke (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    Module.End ℂ (Fin n → ℂ) where
  toFun v i := b.constr ℂ v (originalPrimeRegularHecke N ell (b i))
  map_add' v w := by
    funext i
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c v := by
    funext i
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

attribute [local instance] placeTopology

theorem originalPrimePeriodHecke_pathIntegral (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P Q) :
    originalPrimePeriodHecke N ell b (fun i => pathIntegral N (b i).val γ) =
      fun i => pathIntegral N (originalPrimeRegularHecke N ell (b i)).val γ := by
  funext i
  change b.constr ℂ (fun j => pathIntegral N (b j).val γ)
    (originalPrimeRegularHecke N ell (b i)) = _
  rw [Module.Basis.constr_apply_fintype]
  have he := congrArg Subtype.val (b.sum_repr (originalPrimeRegularHecke N ell (b i)))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  rw [← he, pathIntegral_sum_smul N _ _ (fun j => (b j).property)]
  rfl

theorem originalPrimePeriodHecke_primitive_difference (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (τ₀ τ₁ : ℍ) :
    originalPrimePeriodHecke N ell b
        (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₁ -
          sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₀) =
      fun i => sourceWeightTwoPrimitive 1
          (cuspHeckePrime ell.property (originalRegularCuspEquiv N (b i))) τ₁ -
        sourceWeightTwoPrimitive 1
          (cuspHeckePrime ell.property (originalRegularCuspEquiv N (b i))) τ₀ := by
  let γ : Path τ₀ τ₁ := PathConnectedSpace.somePath τ₀ τ₁
  have he := originalPrimePeriodHecke_pathIntegral N ell b
    (γ.map (originalAnalyticPlace_continuous N))
  simpa only [original_pathIntegral_eq_cusp_primitive, originalPrimeRegularHecke_cusp] using he

end
end Dubon2026.SourceFunctionField.OriginalChart

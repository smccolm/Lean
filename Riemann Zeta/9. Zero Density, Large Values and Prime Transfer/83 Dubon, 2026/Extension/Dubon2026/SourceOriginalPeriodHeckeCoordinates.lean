import Dubon2026.SourceOriginalCuspPeriodLattice
import Dubon2026.SourceWeightTwoScalarHecke
import Dubon2026.HeckePrimeLinear

/-! DUB-17/18 -> original Jacobian Tate Hecke realization -> actual
period Hecke operator. Use the proved regular-differential/cusp-form
equivalence and the native basis-dual equivalence. This is the transpose
of the genuine analytic Hecke operator, with no chosen matrix or
compatibility premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]

private local instance {N : ℕ} (ell : sourceBinaryHeckePrime N) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The genuine analytic Hecke operator on the original regular differentials. -/
def originalRegularHecke (ell : sourceBinaryHeckePrime N) :
    Module.End ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :=
  (originalRegularCuspEquiv N).symm.toLinearMap.comp
    ((cuspHeckePrimeLinear 2 ell.property.1).comp (originalRegularCuspEquiv N).toLinearMap)

theorem originalRegularHecke_cusp (ell : sourceBinaryHeckePrime N)
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalRegularCuspEquiv N (originalRegularHecke N ell ω) =
      cuspHeckePrime ell.property.1 (originalRegularCuspEquiv N ω) :=
  (originalRegularCuspEquiv N).apply_symm_apply _

/-- Dual Hecke action in the coordinates of an actual original regular basis. -/
def originalPeriodHecke (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    Module.End ℂ (Fin n → ℂ) where
  toFun v i := b.constr ℂ v (originalRegularHecke N ell (b i))
  map_add' v w := by
    funext i
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c v := by
    funext i
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

theorem originalPeriodHecke_dual (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (L : Module.Dual ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    originalPeriodHecke N ell b (fun i => L (b i)) =
      fun i => L (originalRegularHecke N ell (b i)) := by
  funext i
  change b.constr ℂ (fun j => L (b j)) (originalRegularHecke N ell (b i)) = _
  rw [b.constr_self]

theorem originalPeriodHecke_cusp_period (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (γ : Gamma0 N) :
    originalPeriodHecke N ell b
        (fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ) =
      fun i => sourceWeightTwoPeriodValue (Gamma0 N)
        (cuspHeckePrime ell.property.1 (originalRegularCuspEquiv N (b i))) γ := by
  let L : Module.Dual ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :=
    (LinearMap.proj γ).comp
      ((sourceWeightTwoPeriodValue (Gamma0 N)).comp (originalRegularCuspEquiv N).toLinearMap)
  change originalPeriodHecke N ell b (fun i => L (b i)) = _
  rw [originalPeriodHecke_dual]
  funext i
  change sourceWeightTwoPeriodValue (Gamma0 N)
    (originalRegularCuspEquiv N (originalRegularHecke N ell (b i))) γ = _
  rw [originalRegularHecke_cusp]

end
end Dubon2026.SourceFunctionField.OriginalChart

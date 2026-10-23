import Dubon2026.SourceOriginalFullHeckeMatrixRange
import Dubon2026.SourceCuspDualHeckeWords

/-! DUB-17/18 -> original rank-two matrix descent -> the actual
cusp-period dual equivalence. The already proved regular-cusp and
basis-dual equivalences identify the same original period coordinates
with the cusp dual. Genuine prime compatibility extends to all integral
words, retaining their actual actions on both sides.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "S" => CuspForm (Gamma0 N) 2

/-- Original period coordinates identified with the dual of the actual weight-two cusp space. -/
def originalCuspPeriodDualEquiv {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ S :=
  (b.constr ℂ).trans (originalRegularCuspEquiv N).symm.dualMap

theorem originalCuspPeriodDualEquiv_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (v : Fin n → ℂ) (f : S) :
    originalCuspPeriodDualEquiv N b v f =
      b.constr ℂ v ((originalRegularCuspEquiv N).symm f) := rfl

theorem originalCuspPeriodDualEquiv_prime {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (ell : Nat.Primes) (v : Fin n → ℂ) :
    originalCuspPeriodDualEquiv N b (originalPrimePeriodHecke N ell b v) =
      (cuspHeckeLinear N 2 ell.val).dualMap (originalCuspPeriodDualEquiv N b v) := by
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  let e := originalRegularCuspEquiv N
  apply LinearMap.ext
  intro f
  have h := LinearMap.congr_fun (originalPrimePeriodHecke_constr N ell b v) (e.symm f)
  have hr : originalPrimeRegularHecke N ell (e.symm f) =
      e.symm (cuspHeckeLinear N 2 ell.val f) := by
    apply e.injective
    rw [originalPrimeRegularHecke_cusp]
    simp only [e, LinearEquiv.apply_symm_apply]
    rw [cuspHeckeLinear_prime N 2 ell.property]
    rfl
  change b.constr ℂ (originalPrimePeriodHecke N ell b v) (e.symm f) =
    b.constr ℂ v (e.symm (cuspHeckeLinear N 2 ell.val f))
  exact h.trans (congrArg (b.constr ℂ v) hr)

theorem originalCuspPeriodDualEquiv_heckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (a : FreeAlgebra ℤ Nat.Primes) (v : Fin n → ℂ) :
    originalCuspPeriodDualEquiv N b (originalPeriodHeckeWord N b a v) =
      sourceWeightTwoDualHeckeWord N a (originalCuspPeriodDualEquiv N b v) :=
  sourceHeckeWord_intertwine_addHom
    (fun ell => originalPrimePeriodHecke N ell b)
    (fun ell : Nat.Primes => (cuspHeckeLinear N 2 ell.val).dualMap)
    (originalCuspPeriodDualEquiv N b).toLinearMap.toAddMonoidHom
    (fun ell x => originalCuspPeriodDualEquiv_prime N b ell x) a v

theorem originalCuspPeriodDualEquiv_heckeWord_apply {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (a : FreeAlgebra ℤ Nat.Primes) (v : Fin n → ℂ) (f : S) :
    originalCuspPeriodDualEquiv N b (originalPeriodHeckeWord N b a v) f =
      originalCuspPeriodDualEquiv N b v (sourceWeightTwoCuspHeckeWord N a f) :=
  (LinearMap.congr_fun (originalCuspPeriodDualEquiv_heckeWord N b a v) f).trans
    (sourceWeightTwoDualHeckeWord_apply N a (originalCuspPeriodDualEquiv N b v) f)

end
end Dubon2026.SourceFunctionField.OriginalChart

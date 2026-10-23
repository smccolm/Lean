import Dubon2026.SourceOriginalCuspPeriodDual
import Dubon2026.SourceDualCoordinateTranspose

/-! DUB-17/18 -> actual rank-two matrix descent -> faithful transport
of cusp operators to the original period coordinates. Conjugate their
dual action through the proved original cusp-period equivalence. The
construction sends each actual integral Hecke word to its already
constructed original period word and is injective.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "S" => CuspForm (Gamma0 N) 2

/-- The genuine cusp transpose expressed in the actual original period coordinates. -/
def originalCuspPeriodTranspose {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Module.End ℂ S →ₗ[ℂ] Module.End ℂ (Fin n → ℂ) :=
  dualCoordinateTranspose (originalCuspPeriodDualEquiv N b)

theorem originalCuspPeriodTranspose_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (T : Module.End ℂ S) (v : Fin n → ℂ) :
    originalCuspPeriodDualEquiv N b (originalCuspPeriodTranspose N b T v) =
      T.dualMap (originalCuspPeriodDualEquiv N b v) :=
  dualCoordinateTranspose_apply (originalCuspPeriodDualEquiv N b) T v

theorem originalCuspPeriodTranspose_heckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalCuspPeriodTranspose N b (sourceWeightTwoCuspHeckeWord N a) =
      originalPeriodHeckeWord N b a := by
  apply LinearMap.ext
  intro v
  apply (originalCuspPeriodDualEquiv N b).injective
  rw [originalCuspPeriodTranspose_apply, originalCuspPeriodDualEquiv_heckeWord]
  apply LinearMap.ext
  intro f
  exact (sourceWeightTwoDualHeckeWord_apply N a (originalCuspPeriodDualEquiv N b v) f).symm

theorem originalCuspPeriodTranspose_injective {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Function.Injective (originalCuspPeriodTranspose N b) :=
  dualCoordinateTranspose_injective (originalCuspPeriodDualEquiv N b)

end
end Dubon2026.SourceFunctionField.OriginalChart

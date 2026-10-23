import Dubon2026.SourceIntegralHeckeBasisCoordinates
import Mathlib.RingTheory.AlgebraTower

/-! DUB-17/18 -> original rank-two Tate descent -> two real Hecke
generators of the actual cusp dual. The perfect coefficient pairing
turns the complex integral-algebra basis into a cusp-dual basis. Native
scalar-tower basis multiplication by 1 and I supplies its real span.
No real two-generator or orbit-spanning premise is assumed.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2
local notation "S" => CuspForm (Gamma0 N) 2

theorem sourceWeightTwoDual_real_two_generators :
    ∃ w : Fin 2 → Module.Dual ℂ S,
      Submodule.span ℝ (Set.range fun t : TZ × Fin 2 => t.1.val.dualMap (w t.2)) = ⊤ := by
  classical
  let b := sourceIntegralHeckeBasis N
  let d := (sourceIntegralHeckeComplexBasis N b).map (sourceWeightTwoHeckeDualEquiv N)
  let B := Complex.basisOneI.smulTower d
  refine ⟨fun k => Complex.basisOneI k • cuspCoefficientLinear N 2 1, ?_⟩
  apply top_unique
  rw [← B.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨⟨k, i⟩, rfl⟩
  refine ⟨(b i, k), ?_⟩
  apply LinearMap.ext
  intro f
  simp only [B, d, Module.Basis.smulTower_apply, Module.Basis.map_apply,
    LinearMap.dualMap_apply', LinearMap.smul_apply, sourceWeightTwoHeckeDualEquiv_apply,
    sourceIntegralHeckeComplexBasis_apply]
  rfl

end
end Dubon2026

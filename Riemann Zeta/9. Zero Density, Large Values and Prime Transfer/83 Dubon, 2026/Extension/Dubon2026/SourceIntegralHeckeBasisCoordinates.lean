import Dubon2026.SourceIntegralHeckeComplexBasis
import Dubon2026.SourceIntegralAlgebraBasisCoordinates

/-! DUB-17/18 -> rank-two descent -> integral coordinates on the actual
full Hecke algebra. Its finite free integer basis extends to a complex
basis with exactly the same coordinates on every integral operator.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2
local notation "A" => sourceWeightTwoFullHeckeAlgebra N

theorem sourceOriginalIntegralHecke_free : Module.Free ℤ TZ := by
  letI := sourceOriginalIntegralHeckeAlgebra_finite N 2 (by norm_num)
  exact finiteIntegerOperatorAlgebra_free _ TZ

/-- A finite integer basis of the literal integral operator algebra. -/
def sourceIntegralHeckeBasis : Module.Basis (Fin (Module.finrank ℤ TZ)) ℤ TZ := by
  letI := sourceOriginalIntegralHeckeAlgebra_finite N 2 (by norm_num)
  letI := sourceOriginalIntegralHecke_free N
  exact Module.finBasis ℤ TZ

/-- Inclusion of actual integral operators into the full complex Hecke algebra. -/
def sourceIntegralHeckeToComplex : TZ →ₐ[ℤ] A :=
  integralComplexAlgebraInclusion TZ A (sourceOriginalIntegralHecke_le_full N)

theorem sourceIntegralHeckeToComplex_apply (t : TZ) :
    (sourceIntegralHeckeToComplex N t).val = t.val :=
  integralComplexAlgebraInclusion_apply TZ A (sourceOriginalIntegralHecke_le_full N) t

theorem sourceIntegralHeckeToComplex_basis {ι : Type*} (b : Module.Basis ι ℤ TZ)
    (i : ι) : sourceIntegralHeckeToComplex N (b i) = sourceIntegralHeckeComplexBasis N b i :=
  integralComplexAlgebraInclusion_basis TZ A (sourceOriginalIntegralHecke_le_full N)
    b (sourceIntegralHeckeComplexBasis N b) (sourceIntegralHeckeComplexBasis_apply N b) i

theorem sourceIntegralHeckeComplexBasis_repr {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ TZ) (t : TZ) (i : ι) :
    (sourceIntegralHeckeComplexBasis N b).repr (sourceIntegralHeckeToComplex N t) i =
      (b.repr t i : ℂ) :=
  integralComplexAlgebraInclusion_repr TZ A (sourceOriginalIntegralHecke_le_full N)
    b (sourceIntegralHeckeComplexBasis N b) (sourceIntegralHeckeComplexBasis_apply N b) t i

end
end Dubon2026

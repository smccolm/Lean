import Dubon2026.SourceIntegralHeckeComplexIndependence
import Dubon2026.SourceWeightTwoHeckePerfectPairing
import Mathlib.LinearAlgebra.FreeModule.PID

/-! DUB-17/18 -> rank-two Hecke descent -> rational cusp matrices.
The already finite integral Hecke algebra has a basis which remains
independent over the complex numbers. Its complex span is the full
actual Hecke algebra. This supplies the algebra basis used to dualize
the perfect first-coefficient pairing, without constructing a broader
integral Fourier structure.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2
local notation "A" => sourceWeightTwoFullHeckeAlgebra N

theorem sourceOriginalIntegralHecke_le_full : TZ ≤ (A).restrictScalars ℤ := by
  apply Algebra.adjoin_le
  intro x hx
  change x ∈ A
  exact Algebra.subset_adjoin hx

theorem sourceWeightTwoFullHecke_adjoin_integral :
    Algebra.adjoin ℂ (TZ : Set (Module.End ℂ (CuspForm (Gamma0 N) 2))) = A := by
  apply le_antisymm
  · exact Algebra.adjoin_le (sourceOriginalIntegralHecke_le_full N)
  · apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin (Algebra.subset_adjoin hx : x ∈ TZ)

theorem sourceWeightTwoFullHecke_span_integralBasis {ι : Type*}
    (b : Module.Basis ι ℤ TZ) :
    Submodule.span ℂ (Set.range fun i => (b i).val) = (A).toSubmodule := by
  have hz : (TZ).toSubmodule = Submodule.span ℤ (Set.range fun i => (b i).val) := by
    rw [← (TZ).toSubmodule.range_subtype, ← Submodule.map_top, ← b.span_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← sourceWeightTwoFullHecke_adjoin_integral N]
  exact ((TZ).adjoin_eq_span_of_eq_span ℂ hz).symm

/-- The same literal integral basis, now a complex basis of the actual full algebra. -/
def sourceIntegralHeckeComplexBasis {ι : Type*} (b : Module.Basis ι ℤ TZ) :
    Module.Basis ι ℂ A :=
  (Module.Basis.span (sourceOriginalIntegralHecke_linearIndependent_complex N b
    b.linearIndependent)).map
      (LinearEquiv.ofEq _ _ (sourceWeightTwoFullHecke_span_integralBasis N b))

theorem sourceIntegralHeckeComplexBasis_apply {ι : Type*} (b : Module.Basis ι ℤ TZ)
    (i : ι) : (sourceIntegralHeckeComplexBasis N b i).val = (b i).val := by
  simp only [sourceIntegralHeckeComplexBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

end
end Dubon2026

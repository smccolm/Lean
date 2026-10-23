import Dubon2026.SourceIntegralHeckeBasisCoordinates

/-! DUB-17/18 -> rank-two original Tate descent -> dimension of the
real operator span. The constructed integer basis remains independent
over the complex numbers, hence over the reals. Its real span is the
span of every genuine integral Hecke operator. Perfect coefficient
duality identifies its dimension with the actual cusp-space dimension.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2
local notation "S" => CuspForm (Gamma0 N) 2

theorem sourceIntegralHeckeBasis_real_span {ι : Type*} (b : Module.Basis ι ℤ TZ) :
    Submodule.span ℝ (Set.range fun i => (b i).val) =
      Submodule.span ℝ (TZ : Set (Module.End ℂ S)) := by
  have hz : (TZ).toSubmodule = Submodule.span ℤ (Set.range fun i => (b i).val) := by
    rw [← (TZ).toSubmodule.range_subtype, ← Submodule.map_top, ← b.span_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  change _ = Submodule.span ℝ ((TZ).toSubmodule : Set (Module.End ℂ S))
  rw [hz, Submodule.span_span_of_tower]

theorem sourceWeightTwoRealHecke_finrank :
    Module.finrank ℝ (Submodule.span ℝ (TZ : Set (Module.End ℂ S))) =
      Module.finrank ℂ S := by
  let b := sourceIntegralHeckeBasis N
  have hli := (sourceOriginalIntegralHecke_linearIndependent_complex N b
    b.linearIndependent).restrict_scalars' ℝ
  rw [← sourceIntegralHeckeBasis_real_span N b, finrank_span_eq_card hli,
    ← Module.finrank_eq_card_basis (sourceIntegralHeckeComplexBasis N b),
    sourceWeightTwoFullHeckeAlgebra_finrank N]

end
end Dubon2026

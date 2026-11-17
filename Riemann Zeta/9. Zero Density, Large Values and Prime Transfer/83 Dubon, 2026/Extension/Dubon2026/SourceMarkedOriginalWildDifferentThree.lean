import Dubon2026.SourceMarkedOriginalNormalFieldThree
import Dubon2026.SourceMarkedOriginalWildDifferent

/-! DUB-17/18 -> reverse original genus -> characteristic-three different.
The actual original Gamma1 field has different order at least seven
at every place where j has order six. The native inertia quotient and
marked chart construct the normal auxiliary field, so no normal-field or
local differential certificate remains in this endpoint. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
    [CharP (IsLocalRing.ResidueField A) 3]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem original_seven_le_different_of_j_order_six
    (h3N : ¬ 3 ∣ N) (hN : 2 ≤ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (v : Place kk F) (hv : v.ord x = 6) :
    7 ≤ v.ordDifferential (D kk F x) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ω := AlgebraicClosure (RatFunc kk)
  letI : Algebra kk Ω := inferInstanceAs (Algebra kk (AlgebraicClosure (RatFunc kk)))
  letI : IsScalarTower kk (RatFunc kk) Ω :=
    inferInstanceAs (IsScalarTower kk (RatFunc kk) (AlgebraicClosure (RatFunc kk)))
  obtain ⟨M, L, hfd, hgal, ι, hι, hdvd⟩ :=
    exists_original_normal_field_j_order_dvd_six A N h3N hN x hx
  letI : Algebra kk M := IntermediateField.algebra' M
  letI : IsScalarTower kk (RatFunc kk) M := IntermediateField.isScalarTower M
  letI : Algebra kk L := IntermediateField.algebra' L
  letI : IsScalarTower kk (RatFunc kk) L := IntermediateField.isScalarTower L
  letI := hfd
  letI := hgal
  exact original_wild_different_of_normal_order_bound A N 3 h3N x hx L ι hι
    6 (by norm_num) 1 (by norm_num) hdvd v hv

end
end Dubon2026.SourceFunctionField.MarkedChart

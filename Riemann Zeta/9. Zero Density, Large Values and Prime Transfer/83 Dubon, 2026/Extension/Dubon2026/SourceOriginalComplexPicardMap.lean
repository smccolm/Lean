import Dubon2026.SourceOriginalDivisorConorm
import Dubon2026.SourceOriginalPicardGroup

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison.
The actual conorm descends through the original degree-zero divisor quotients
to an additive map from originalJZero to the original complex Picard group.
It preserves actual n-torsion. Injectivity and surjectivity on torsion still
require principal-divisor and torsion descent; neither is assumed here.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

/-- The actual conorm restricted to original degree-zero divisors. -/
def conormDegZero :
    Divisor.degZero (K := Qbar) (F := FQ) →+ Divisor.degZero (K := ℂ) (F := FC) where
  toFun D := ⟨conorm N D.val, by
    change Divisor.degree (conorm N D.val) = 0
    rw [degree_conorm]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero (conorm N))
  map_add' D E := Subtype.ext (map_add (conorm N) D.val E.val)

/-- The actual original arithmetic-to-complex degree-zero divisor-class map. -/
def complexPicardMap : originalJZero N →+ Pic0 ℂ FC :=
  QuotientAddGroup.map _ _ (conormDegZero N) (by
    intro D hD
    change Divisor.IsPrincipal (conorm N D.val)
    exact isPrincipal_conorm N hD)

theorem complexPicardMap_mk (D : Divisor.degZero (K := Qbar) (F := FQ)) :
    complexPicardMap N (Pic0.mk D) = Pic0.mk (conormDegZero N D) := rfl

theorem complexPicardMap_mem_torsion {n : ℕ} {x : originalJZero N}
    (hx : x ∈ Pic0.torsion n) : complexPicardMap N x ∈ Pic0.torsion n := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceFunctionField.OriginalConstantField

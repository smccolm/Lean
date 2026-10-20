import Dubon2026.SourceSquareZeroGroupStability
import Dubon2026.SourceInducedLieComplements

/-! Elementary group-stability of the actual source Lie complements.
The original induced Lie submodules are mapped into the same original
regular-function ring. The proved finite exponential then recovers their
stability under the actual square-zero special-linear directions.
Full group-stability and irreducibility remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℤ)

/-- Every actual source Lie submodule is stable under the original square-zero special-linear one-parameter directions. -/
theorem sourceInducedLieSubmodule_squareZero_stable
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam))
    (X : LieAlgebra.SpecialLinear.sl (Fin n) K) (hX : X.val * X.val = 0)
    (t : K) (p : generalLinearIntegralInducedSubmodule K n lam) (hp : p ∈ W) :
    generalLinearIntegralInducedRepresentation K n lam
      (sourceSquareZeroLine X.val hX t) p ∈ W := by
  let F := (generalLinearIntegralInducedSubmodule K n lam).subtype
  let V := W.toSubmodule.map F
  have hV : ∀ q ∈ V, sourceRegularDifferential X.val q ∈ V := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hq
    apply Submodule.mem_map.mpr
    exact ⟨⁅X, r⁆, W.lie_mem hr, rfl⟩
  have hmem : p.val ∈ V := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  have hact := sourceSquareZero_action_mem_of_differential X.val hX V hV t hmem
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp hact
  have hqeq : q = generalLinearIntegralInducedRepresentation K n lam
      (sourceSquareZeroLine X.val hX t) p := Subtype.ext he
  rwa [hqeq] at hq

/-- The actual source-induced module has Lie complements that are also stable under every original square-zero special-linear direction, with all action and complete-reducibility inputs discharged. -/
theorem sourceInduced_exists_squareZero_stable_complement {m : ℕ}
    (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) :
    ∃ U : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
        (generalLinearIntegralInducedSubmodule K (m + 1) weight),
      IsCompl W U ∧
      ∀ (X : LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
        (hX : X.val * X.val = 0) (t : K)
        (p : generalLinearIntegralInducedSubmodule K (m + 1) weight), p ∈ U →
          generalLinearIntegralInducedRepresentation K (m + 1) weight
            (sourceSquareZeroLine X.val hX t) p ∈ U := by
  obtain ⟨U, hU⟩ := sourceInducedSpecialLinear_exists_complement K weight W
  exact ⟨U, hU, sourceInducedLieSubmodule_squareZero_stable K (m + 1) weight U⟩

end
end Dubon2026

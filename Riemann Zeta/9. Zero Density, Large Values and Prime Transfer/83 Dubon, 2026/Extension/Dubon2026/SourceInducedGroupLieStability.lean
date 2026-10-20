import Dubon2026.SourceRegularSpecialLinearStability
import Dubon2026.SourceInducedLieIrreducible

/-! Recovering the actual source Lie invariance from the original group action.
The original invariant subspace is mapped into the same regular-function ring.
Its actual elementary group orbits and coefficient extraction give stability
under the differentiated action, without a supplied Lie-invariance premise.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℤ)

/-- Every subspace stable under the original source general-linear action is stable under the actual differentiated special-linear action. -/
theorem sourceInduced_group_stable_lie_mem
    (W : Submodule K (generalLinearIntegralInducedSubmodule K n lam))
    (hW : ∀ g : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ p ∈ W, generalLinearIntegralInducedRepresentation K n lam g p ∈ W)
    (X : LieAlgebra.SpecialLinear.sl (Fin n) K)
    (p : generalLinearIntegralInducedSubmodule K n lam) (hp : p ∈ W) :
    ⁅X, p⁆ ∈ W := by
  let F := (generalLinearIntegralInducedSubmodule K n lam).subtype
  let V := W.map F
  have hV (Y : Matrix (Fin n) (Fin n) K) (hY : Y * Y = 0) :
      ∀ t : K, ∀ q ∈ V,
        generalLinearRegularRightTranslate (sourceSquareZeroLine Y hY t) q ∈ V := by
    intro t q hq
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨generalLinearIntegralInducedRepresentation K n lam (sourceSquareZeroLine Y hY t) r,
        hW _ r hr, rfl⟩
  have hoff (i j : Fin n) (hij : i ≠ j) (q : GeneralLinearRegularFunctions K n)
      (hq : q ∈ V) :
      sourceRegularDifferential (Matrix.single i j (1 : K)) q ∈ V := by
    have hs : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
      rw [Matrix.single_mul_single_of_ne (h := fun h => hij h.symm)]
    exact sourceSquareZero_differential_mem_of_group _ hs V (hV _ hs) q hq
  have hmem : p.val ∈ V := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  have hd := sourceRegular_traceZero_stable_of_offDiagonal V hoff X.val X.property
    p.val hmem
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp hd
  have hqeq : q = ⁅X, p⁆ := Subtype.ext he
  rwa [hqeq] at hq

/-- An original group-invariant source subspace, with its derived actual Lie-submodule structure. -/
def sourceInducedGroupLieSubmodule
    (W : Submodule K (generalLinearIntegralInducedSubmodule K n lam))
    (hW : ∀ g : Matrix.GeneralLinearGroup (Fin n) K,
      ∀ p ∈ W, generalLinearIntegralInducedRepresentation K n lam g p ∈ W) :
    LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam) where
  toSubmodule := W
  lie_mem := fun {X p} hp => sourceInduced_group_stable_lie_mem K n lam W hW X p hp

end
end Dubon2026

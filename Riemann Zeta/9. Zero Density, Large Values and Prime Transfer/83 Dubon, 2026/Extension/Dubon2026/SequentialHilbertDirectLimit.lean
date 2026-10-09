import Dubon2026.SequentialHilbertIsometries

/-! # The genuine algebraic direct limit with its finite-stage inner product -/

namespace Dubon2026

noncomputable section

variable (V : ℕ → ComplexInnerCarrier) (J : ∀ n, V n →ₗᵢ[ℂ] V (n + 1))

/-- The actual algebraic directed quotient of the consecutive finite Hilbert spaces. -/
abbrev SequentialHilbertLimit :=
  DirectLimit (fun n => V n) (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)

/-- The genuine canonical map of a finite stage into the algebraic directed quotient. -/
def sequentialHilbertOf (n : ℕ) : V n →ₗ[ℂ] SequentialHilbertLimit V J :=
  DirectLimit.Module.of ℂ ℕ (fun n => V n) (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap) n

/-- The direct-limit inner product is obtained from the actual original finite-stage inner products. -/
def sequentialHilbertInner : SequentialHilbertLimit V J → SequentialHilbertLimit V J → ℂ :=
  DirectLimit.lift₂ (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)
    (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)
    (fun n => @inner ℂ (V n) _) (fun n m h x y => (LinearIsometry.inner_map_map (sequentialHilbertMap V J n m h) x y).symm)

/-- The directed quotient retains the exact original inner product at every finite stage. -/
theorem sequentialHilbertInner_of (n : ℕ) (x y : V n) :
    sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n y) = inner ℂ x y :=
  DirectLimit.lift₂_def (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)
    (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)
    (fun n => @inner ℂ (V n) _) (fun n m h x y =>
      (LinearIsometry.inner_map_map (sequentialHilbertMap V J n m h) x y).symm) n x y

/-- The actual finite-stage inner products descend to a positive definite inner-product core. -/
@[implicit_reducible]
def sequentialHilbertCore : InnerProductSpace.Core ℂ (SequentialHilbertLimit V J) where
  inner := sequentialHilbertInner V J
  conj_inner_symm := by
    apply DirectLimit.induction₂
    intro n x y
    change starRingEnd ℂ (sequentialHilbertInner V J (sequentialHilbertOf V J n y) (sequentialHilbertOf V J n x)) =
      sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n y)
    rw [sequentialHilbertInner_of, sequentialHilbertInner_of]
    exact inner_conj_symm _ _
  re_inner_nonneg := by
    apply DirectLimit.induction
    intro n x
    change 0 ≤ (sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n x)).re
    rw [sequentialHilbertInner_of]
    exact inner_self_nonneg (𝕜 := ℂ) (x := x)
  add_left := by
    apply DirectLimit.induction₃
    intro n x y z
    change sequentialHilbertInner V J (sequentialHilbertOf V J n x + sequentialHilbertOf V J n y)
        (sequentialHilbertOf V J n z) =
      sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n z) +
        sequentialHilbertInner V J (sequentialHilbertOf V J n y) (sequentialHilbertOf V J n z)
    rw [← map_add, sequentialHilbertInner_of, sequentialHilbertInner_of, sequentialHilbertInner_of]
    exact inner_add_left _ _ _
  smul_left := by
    intro x y c
    induction x, y using DirectLimit.induction₂ with
    | _ n x y =>
      change sequentialHilbertInner V J (c • sequentialHilbertOf V J n x) (sequentialHilbertOf V J n y) =
        starRingEnd ℂ c * sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n y)
      rw [← map_smul, sequentialHilbertInner_of, sequentialHilbertInner_of]
      exact inner_smul_left _ _ _
  definite := by
    intro x
    induction x using DirectLimit.induction with
    | _ n x =>
      change sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n x) = 0 → _
      rw [sequentialHilbertInner_of]
      intro hx
      have hz : x = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hx
      change sequentialHilbertOf V J n x = 0
      rw [hz, map_zero]

/-- The directed quotient norm is the norm derived from its actual finite-stage inner product. -/
instance sequentialHilbertLimitNormed : NormedAddCommGroup (SequentialHilbertLimit V J) :=
  letI := sequentialHilbertCore V J
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The actual directed quotient has its positive definite finite-stage inner product. -/
instance sequentialHilbertLimitInner : InnerProductSpace ℂ (SequentialHilbertLimit V J) :=
  letI := sequentialHilbertCore V J
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (SequentialHilbertLimit V J))

/-- The canonical finite-stage inclusion is a genuine isometry for the independently descended inner product. -/
def sequentialHilbertOfIsometry (n : ℕ) : V n →ₗᵢ[ℂ] SequentialHilbertLimit V J :=
  @LinearMap.isometryOfInner ℂ (V n) inferInstance inferInstance inferInstance
    (SequentialHilbertLimit V J) inferInstance inferInstance
    (sequentialHilbertOf V J n) (sequentialHilbertInner_of V J n)

/-- Every directed-quotient vector is represented at an actual finite stage. -/
theorem sequentialHilbertLimit_exists_stage (x : SequentialHilbertLimit V J) :
    ∃ n y, sequentialHilbertOf V J n y = x := by
  obtain ⟨n, y, hy⟩ := DirectLimit.exists_eq_mk _ x
  exact ⟨n, y, hy.symm⟩

end
end Dubon2026

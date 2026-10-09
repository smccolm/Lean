import Dubon2026.SequentialHilbertDirectLimit

/-! # Isometric realizations of the genuine finite-stage Hilbert direct limit -/

namespace Dubon2026

noncomputable section

variable (V : ℕ → ComplexInnerCarrier) (J : ∀ n, V n →ₗᵢ[ℂ] V (n + 1))
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : ∀ n, V n →ₗᵢ[ℂ] H) (hT : ∀ n x, T (n + 1) (J n x) = T n x)

/-- The actual compatible finite-stage maps induce a linear map from the genuine directed quotient. -/
def sequentialHilbertLimitLinearMap : SequentialHilbertLimit V J →ₗ[ℂ] H :=
  DirectLimit.Module.lift ℂ ℕ (fun n => V n) (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap)
    (fun n => (T n).toLinearMap) (sequentialHilbertMap_realization V J T hT)

/-- The actual direct-limit realization recovers each original finite-stage map exactly. -/
theorem sequentialHilbertLimitLinearMap_of (n : ℕ) (x : V n) :
    sequentialHilbertLimitLinearMap V J T hT (sequentialHilbertOf V J n x) = T n x := rfl

/-- The genuine directed-quotient realization preserves the independently descended finite-stage inner product. -/
theorem sequentialHilbertLimitLinearMap_inner (x y : SequentialHilbertLimit V J) :
    inner ℂ (sequentialHilbertLimitLinearMap V J T hT x) (sequentialHilbertLimitLinearMap V J T hT y) =
      inner ℂ x y := by
  induction x, y using DirectLimit.induction₂ with
  | _ n x y =>
    change inner ℂ (sequentialHilbertLimitLinearMap V J T hT (sequentialHilbertOf V J n x))
        (sequentialHilbertLimitLinearMap V J T hT (sequentialHilbertOf V J n y)) =
      sequentialHilbertInner V J (sequentialHilbertOf V J n x) (sequentialHilbertOf V J n y)
    rw [sequentialHilbertLimitLinearMap_of, sequentialHilbertLimitLinearMap_of, sequentialHilbertInner_of]
    exact (T n).inner_map_map x y

/-- The direct-limit map is genuinely isometric for the original finite-stage tensor norm. -/
def sequentialHilbertLimitIsometry : SequentialHilbertLimit V J →ₗᵢ[ℂ] H :=
  (sequentialHilbertLimitLinearMap V J T hT).isometryOfInner (sequentialHilbertLimitLinearMap_inner V J T hT)

/-- The genuine direct-limit isometry recovers every original finite-stage vector. -/
theorem sequentialHilbertLimitIsometry_of (n : ℕ) (x : V n) :
    sequentialHilbertLimitIsometry V J T hT (sequentialHilbertOf V J n x) = T n x := rfl

/-- The original range of the directed-quotient realization is exactly the union of the finite-stage ranges. -/
theorem sequentialHilbertLimitIsometry_mem_range_iff (y : H) :
    y ∈ (sequentialHilbertLimitIsometry V J T hT).toLinearMap.range ↔ ∃ n x, T n x = y := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n, x, rfl⟩ := sequentialHilbertLimit_exists_stage V J x
    exact ⟨n, x, rfl⟩
  · rintro ⟨n, x, rfl⟩
    exact ⟨sequentialHilbertOf V J n x, rfl⟩

end
end Dubon2026

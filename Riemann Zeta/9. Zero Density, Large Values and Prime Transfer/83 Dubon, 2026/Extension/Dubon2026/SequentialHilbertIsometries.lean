import Dubon2026.FiniteHilbertTensor
import Mathlib.Algebra.Colimit.DirectLimit

/-! # Genuine directed systems obtained by iterating consecutive Hilbert isometries -/

namespace Dubon2026

noncomputable section

variable (V : ℕ → ComplexInnerCarrier) (J : ∀ n, V n →ₗᵢ[ℂ] V (n + 1))

/-- The actual isometric composite of consecutive reference insertions. -/
def sequentialHilbertMap (n m : ℕ) (h : n ≤ m) : V n →ₗᵢ[ℂ] V m :=
  Nat.leRec (motive := fun m _ => V n →ₗᵢ[ℂ] V m) LinearIsometry.id
    (fun {m} _ T => (J m).comp T) h

/-- No transition changes a vector at its original stage. -/
theorem sequentialHilbertMap_self (n : ℕ) : sequentialHilbertMap V J n n le_rfl = LinearIsometry.id := by
  exact Nat.leRec_self _ _

/-- Advancing one more stage composes with exactly the given next isometry. -/
theorem sequentialHilbertMap_succ (n m : ℕ) (h : n ≤ m) :
    sequentialHilbertMap V J n (m + 1) (Nat.le_succ_of_le h) =
      (J m).comp (sequentialHilbertMap V J n m h) := by
  exact Nat.leRec_succ _ _ h

/-- The genuine iterated transitions satisfy composition on all vectors. -/
theorem sequentialHilbertMap_trans (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (x : V n) :
    sequentialHilbertMap V J m l hml (sequentialHilbertMap V J n m hnm x) =
      sequentialHilbertMap V J n l (hnm.trans hml) x := by
  induction hml with
  | refl => rw [sequentialHilbertMap_self]; rfl
  | @step l hml ih =>
      rw [sequentialHilbertMap_succ V J m l hml,
        sequentialHilbertMap_succ V J n l (hnm.trans hml)]
      exact congrArg (J l) ih

/-- Consecutive genuine Hilbert isometries therefore give a true directed linear system. -/
instance sequentialHilbertDirectedSystem :
    DirectedSystem (fun n => V n) (fun n m h => (sequentialHilbertMap V J n m h).toLinearMap) where
  map_self := by intro n x; rw [LinearIsometry.coe_toLinearMap, sequentialHilbertMap_self]; rfl
  map_map := by
    intro l m n hnm hml x
    exact sequentialHilbertMap_trans V J n m l hnm hml x

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (T : ∀ n, V n →ₗᵢ[ℂ] H)

/-- Compatibility with actual consecutive isometries implies compatibility with every genuine iterated transition. -/
theorem sequentialHilbertMap_realization (hT : ∀ n x, T (n + 1) (J n x) = T n x) (n m : ℕ) (h : n ≤ m) (x : V n) :
    T m (sequentialHilbertMap V J n m h x) = T n x := by
  induction h with
  | refl => rw [sequentialHilbertMap_self]; rfl
  | @step m h ih =>
      rw [sequentialHilbertMap_succ V J n m h]
      exact (hT m (sequentialHilbertMap V J n m h x)).trans ih

end
end Dubon2026

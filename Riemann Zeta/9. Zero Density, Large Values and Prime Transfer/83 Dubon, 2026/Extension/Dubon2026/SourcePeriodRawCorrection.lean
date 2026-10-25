import Dubon2026.SourcePeriodIntegerCorrection

/-! DUB-17/18 -> actual cover Abel converse -> regular period correction.
The exact double-sum raw reciprocity clauses convert to the native finite
matrix correction theorem. This isolates the required algebra from actual
splitting-field expressions without changing any mathematical assumption. -/
namespace Dubon2026.SourceFunctionField.PeriodCorrection
noncomputable section
open Matrix

private theorem raw_pairing_eq {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (y : Fin n ⊕ Fin n → ℂ) (i : Fin n) :
    (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec y i =
      ∑ k, ∑ l, (Q k l : ℂ) * A k i * y l := by
  simp only [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A k i * (Q k l : ℂ) * y l = _
  ring


theorem exists_integer_correction_of_raw_reciprocity {d : ℕ}
    (A : Matrix (Fin d ⊕ Fin d) (Fin d) ℂ)
    (Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℤ)
    (hA : Function.Injective A.mulVecLin) (hQ : IsUnit Q.det)
    (hRR : ∀ i j, ∑ k, ∑ l, (Q k l : ℂ) * A k i * A l j = 0)
    (y : Fin d ⊕ Fin d → ℂ) (t : ℂ) (μ κ : Fin d ⊕ Fin d → ℤ)
    (hrec : ∀ i, ∑ k, ∑ l, (Q k l : ℂ) * A k i * y l =
      t * ((∑ k, (μ k : ℂ) * A k i) + ∑ k, (κ k : ℂ) * A k i)) :
    ∃ c : Fin d → ℂ, ∃ m : Fin d ⊕ Fin d → ℤ,
      ∀ k, y k - ∑ i, c i * A k i = t * (m k : ℂ) := by
  have hRm : (A.transpose * Q.map (Int.castRingHom ℂ)) * A = 0 := by
    ext i j
    change (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec (fun l => A l j) i = 0
    rw [raw_pairing_eq]
    exact hRR i j
  have hrecM : (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec y =
      t • A.transpose.mulVec (fun k => ((μ k + κ k : ℤ) : ℂ)) := by
    ext i
    rw [raw_pairing_eq, hrec i]
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.smul_apply,
      smul_eq_mul, Int.cast_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  obtain ⟨c, m, hm⟩ := exists_integer_period_correction A Q hA hQ hRm y t (fun k => μ k + κ k) hrecM
  refine ⟨c, m, fun k => ?_⟩
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using hm k

end
end Dubon2026.SourceFunctionField.PeriodCorrection

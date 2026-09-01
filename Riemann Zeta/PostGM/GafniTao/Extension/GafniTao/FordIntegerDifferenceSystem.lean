import GafniTao.FordPrimeSet

/-!
# Ford Lemma 3.3: integral type-raising system

Ford's complete counts use integer polynomials.  This is the literal
`Φ_j(X+y)-Φ_j(X)` construction from Lemma 3.3, with its type `(d+1,yT)`
certificate proved through the injective scalar extension to `ℚ`.
-/

open Polynomial

namespace GafniTao

noncomputable section

def fordIntegerFiniteDifference (y : ℤ) (p : ℤ[X]) : ℤ[X] :=
  p.taylor y - p

@[simp] theorem fordIntegerFiniteDifference_eval (y x : ℤ) (p : ℤ[X]) :
    (fordIntegerFiniteDifference y p).eval x = p.eval (x + y) - p.eval x := by
  simp [fordIntegerFiniteDifference, taylor_eval]

theorem fordIntegerFiniteDifference_map (y : ℤ) (p : ℤ[X]) :
    (fordIntegerFiniteDifference y p).map (Int.castRingHom ℚ) =
      fordFiniteDifference (y : ℚ) (p.map (Int.castRingHom ℚ)) := by
  simp [fordIntegerFiniteDifference, fordFiniteDifference]

def fordIntegerDifferenceSystem
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (y : ℕ) (hy : 0 < y) :
    FordIntegerPolynomialSystem k (d + 1) (y * T) where
  poly j := if (j : ℕ) + 1 ≤ d + 1 then 0
    else fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)
  twoMultiplicity := Ψ.twoMultiplicity
  zero_below j hj := by simp [hj]
  degree_above j hj := by
    rw [if_neg (not_le_of_gt hj)]
    have hjd : d < (j : ℕ) + 1 := by omega
    have hold : (Ψ.poly j).natDegree =
        ((j : ℕ) + 1 - (d + 1)) + 1 := by
      rw [Ψ.degree_above j hjd]
      omega
    rw [← natDegree_map_eq_of_injective
        (f := Int.castRingHom ℚ) Int.cast_injective
        (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)),
      fordIntegerFiniteDifference_map]
    apply fordFiniteDifference_natDegree
      (p := (Ψ.poly j).map (Int.castRingHom ℚ))
    · rwa [natDegree_map_eq_of_injective Int.cast_injective]
    · rw [leadingCoeff_map_of_injective Int.cast_injective,
        show (Int.castRingHom ℚ) (Ψ.poly j).leadingCoeff =
            ((Ψ.poly j).leadingCoeff : ℚ) by rfl,
        Ψ.leadingCoeff_above j hjd]
      positivity
    · exact_mod_cast (ne_of_gt hy)
  leadingCoeff_above j hj := by
    rw [if_neg (not_le_of_gt hj)]
    change (Int.castRingHom ℚ)
        (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)).leadingCoeff = _
    rw [
      ← leadingCoeff_map_of_injective
        (f := Int.castRingHom ℚ) Int.cast_injective
        (fordIntegerFiniteDifference (y : ℤ) (Ψ.poly j)),
      fordIntegerFiniteDifference_map]
    have hjd : d < (j : ℕ) + 1 := by omega
    have hlead : (Int.castRingHom ℚ) (Ψ.poly j).leadingCoeff =
        (((j : ℕ) + 1).factorial : ℚ) /
          (((j : ℕ) + 1 - d).factorial : ℚ) *
            ((2 ^ Ψ.twoMultiplicity * T : ℕ) : ℚ) := by
      change ((Ψ.poly j).leadingCoeff : ℚ) = _
      exact Ψ.leadingCoeff_above j hjd
    have hold : ((Ψ.poly j).map (Int.castRingHom ℚ)).natDegree =
        ((j : ℕ) + 1 - (d + 1)) + 1 := by
      rw [natDegree_map_eq_of_injective Int.cast_injective,
        Ψ.degree_above j hjd]
      omega
    rw [fordFiniteDifference_leadingCoeff hold (by
      rw [leadingCoeff_map_of_injective Int.cast_injective, hlead]
      positivity) (by exact_mod_cast (ne_of_gt hy)),
      leadingCoeff_map_of_injective Int.cast_injective,
      hlead]
    have hfac : ((j : ℕ) + 1 - d).factorial =
        ((j : ℕ) + 1 - d) *
          (((j : ℕ) + 1 - (d + 1)).factorial) := by
      have hs : (j : ℕ) + 1 - d =
          ((j : ℕ) + 1 - (d + 1)) + 1 := by omega
      rw [hs, Nat.factorial_succ]
    rw [hfac]
    have hstep : (j : ℕ) + 1 - (d + 1) + 1 =
        (j : ℕ) + 1 - d := by omega
    rw [hstep]
    push_cast
    field_simp
    apply mul_inv_cancel₀
    apply ne_of_gt
    exact_mod_cast Nat.sub_pos_of_lt hjd

theorem fordIntegerDifferenceSystem_T_bounds
    {T P y : ℕ} (hy : 0 < y) (hyP : y ≤ P) :
    T ≤ y * T ∧ y * T ≤ P * T := by
  constructor
  · exact Nat.le_mul_of_pos_left T hy
  · exact Nat.mul_le_mul_right T hyP

#print axioms fordIntegerFiniteDifference_eval
#print axioms fordIntegerFiniteDifference_map
#print axioms fordIntegerDifferenceSystem
#print axioms fordIntegerDifferenceSystem_T_bounds

end

end GafniTao

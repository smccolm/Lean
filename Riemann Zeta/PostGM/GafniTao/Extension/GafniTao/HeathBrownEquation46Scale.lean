import GafniTao.HeathBrownEquation61Algebra

/-!
# Heath--Brown equation (46) and the equation-(61) absorption range

In the first case of the discrete twelfth-moment argument the source chooses
`G` in the range `G <= T^(1/3)`.  Cubing this comparison is the exact input
needed to show that the first term of equation (61) is at least one (once
`log T >= 1`), hence is absorbed by its square.  These lemmas keep the
physical cube comparison explicit and separately prove its logarithmic
specialization.
-/

namespace GafniTao

noncomputable section

/-- The physical form of equation (46) makes the linear equation-(61) term
at least one. -/
theorem one_le_heathBrownEquation61First
    {T G L : Real}
    (hG : 0 < G) (hCube : G ^ (3 : Nat) <= T) (hL : 1 <= L) :
    1 <= heathBrownEquation61First T G L := by
  have hGcube : 0 < G ^ (3 : Nat) := pow_pos hG _
  have hRatio : 1 <= T / G ^ (3 : Nat) := by
    rw [le_div_iff₀ hGcube]
    simpa using hCube
  have hLsq : 1 <= L ^ (2 : Nat) := by nlinarith
  unfold heathBrownEquation61First
  nlinarith [mul_le_mul hRatio hLsq (by norm_num : (0 : Real) <= 1)
    (le_trans (by norm_num : (0 : Real) <= 1) hRatio)]

/-- Logarithmic specialization of the preceding equation-(46) comparison. -/
theorem one_le_heathBrownEquation61First_log
    {T G : Real}
    (hT : Real.exp 1 <= T) (hG : 0 < G)
    (hCube : G ^ (3 : Nat) <= T) :
    1 <= heathBrownEquation61First T G (Real.log T) := by
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hLog : 1 <= Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hT
    simpa only [Real.log_exp] using h
  exact one_le_heathBrownEquation61First hG hCube hLog

/-- Equation (61) in the source range, with the linear term already
absorbed and equation (43) substituted exactly. -/
theorem heathBrownEquation61_to_equation7_of_cube
    {R C T G V B : Real}
    (hC : 0 <= C) (hT : Real.exp 1 <= T)
    (hG : 0 < G) (hCube : G ^ (3 : Nat) <= T)
    (hV : 0 < V)
    (hScale : B * G * Real.log T ^ (2 : Nat) = V ^ (2 : Nat))
    (h61 : R <= C *
      (heathBrownEquation61First T G (Real.log T) +
        heathBrownEquation61Second T G (Real.log T))) :
    R <= 2 * C * B ^ (6 : Nat) * T ^ (2 : Nat) /
        V ^ (12 : Nat) * Real.log T ^ (16 : Nat) := by
  exact heathBrownEquation61_to_equation7 hC hG hV
    (one_le_heathBrownEquation61First_log hT hG hCube) hScale h61


end

end GafniTao

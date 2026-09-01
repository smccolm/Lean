import GafniTao.FordFiniteZetaSumBound

/-!
# Ford's physical finite-sum endpoint

This instantiates the finite dyadic estimate at the literal source endpoint
`M = floor t`.  The shell count is the exact base-two natural ceiling
`Nat.clog 2 M`; no real logarithmic upper bound is inserted at this stage.
-/

namespace GafniTao

noncomputable section

def fordFiniteEndpoint (t : ℝ) : ℕ := ⌊t⌋₊

def fordDyadicShellCount (t : ℝ) : ℕ := Nat.clog 2 (fordFiniteEndpoint t)

theorem fordFiniteEndpoint_pos {t : ℝ} (ht : 1 < t) :
    1 ≤ fordFiniteEndpoint t := by
  exact Nat.floor_pos.mpr ht.le

theorem fordFiniteEndpoint_le {t : ℝ} (ht : 1 < t) :
    (fordFiniteEndpoint t : ℝ) ≤ t := by
  exact Nat.floor_le (by positivity)

theorem fordFiniteEndpoint_le_two_pow_shellCount (t : ℝ) :
    fordFiniteEndpoint t ≤ 2 ^ fordDyadicShellCount t := by
  exact Nat.le_pow_clog (by omega) _

/-- Ford's finite Hurwitz-zeta sum bound at the exact natural endpoint
`floor t`, with the dyadic shell count chosen canonically. -/
theorem norm_fordFiniteHurwitzSum_floor_le_source
    (hFord : FordTheorem2)
    {sigma u t : ℝ}
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 1 < t) :
    ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t‖ ≤
      1 + 9.463 *
        (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  exact norm_fordFiniteHurwitzSum_le_source hFord hsigmaLower hsigmaUpper hu huOne ht
    (fordFiniteEndpoint_pos ht) (fordFiniteEndpoint_le ht)
    (fordFiniteEndpoint_le_two_pow_shellCount t)

#print axioms fordFiniteEndpoint_le_two_pow_shellCount
#print axioms norm_fordFiniteHurwitzSum_floor_le_source

end


end GafniTao

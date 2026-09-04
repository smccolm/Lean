import Mathlib

/-!
# Arithmetic ledger for Wooley Sections 9 and 10

The analytic iteration ends with a purely quantitative contradiction.  This
file records that arithmetic independently, so that no informal use of a
ceiling or division by a positive parameter remains in the eventual
concentration consumer.
-/

namespace GafniTao

noncomputable section

/-- The iteration length in Wooley equation (10.2). -/
def wooleyIterationLength (s k : ℕ) (Lambda : ℝ) : ℕ :=
  ⌈16 * (s : ℝ) * (k : ℝ) / Lambda⌉₊

theorem wooley_iteration_length_lower
    {s k : ℕ} {Lambda : ℝ} :
    16 * (s : ℝ) * (k : ℝ) / Lambda ≤
      (wooleyIterationLength s k Lambda : ℝ) := by
  exact Nat.le_ceil _

theorem wooley_iteration_length_pos
    {s k : ℕ} {Lambda : ℝ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hLambda : 0 < Lambda) :
    0 < wooleyIterationLength s k Lambda := by
  have hquot : 0 < 16 * (s : ℝ) * (k : ℝ) / Lambda := by positivity
  have hlower := wooley_iteration_length_lower
    (s := s) (k := k) (Lambda := Lambda)
  exact_mod_cast (lt_of_lt_of_le hquot hlower)

/-- The exact numerical contradiction at the end of Wooley Section 10.
The first inequality is supplied by the ceiling in (10.2), while the second
is what the lower/upper mean-value comparison would force in (10.10). -/
theorem wooley_iteration_final_bounds_contradict
    {s k N : ℕ} {Lambda : ℝ}
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hLambda : 0 < Lambda)
    (hLength : 16 * (s : ℝ) * (k : ℝ) / Lambda ≤ (N : ℝ))
    (hFinal : (N : ℝ) * Lambda / (2 * (k : ℝ)) ≤ 4 * (s : ℝ)) :
    False := by
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLambdaMul :
      16 * (s : ℝ) * (k : ℝ) ≤ (N : ℝ) * Lambda := by
    rw [div_le_iff₀ hLambda] at hLength
    simpa [mul_assoc] using hLength
  have hFinalMul :
      (N : ℝ) * Lambda ≤ 8 * (s : ℝ) * (k : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))] at hFinal
    nlinarith
  have hsReal : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  nlinarith

theorem wooley_iteration_length_final_bound_impossible
    {s k : ℕ} {Lambda : ℝ}
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hLambda : 0 < Lambda)
    (hFinal :
      (wooleyIterationLength s k Lambda : ℝ) * Lambda /
          (2 * (k : ℝ)) ≤ 4 * (s : ℝ)) :
    False :=
  wooley_iteration_final_bounds_contradict hs hk hLambda
    wooley_iteration_length_lower hFinal

/-- The source ratio `rho_j = j/(k-j+1)` used throughout Section 9. -/
def wooleyRho (k r : ℕ) : ℝ :=
  (r : ℝ) / ((k - r + 1 : ℕ) : ℝ)

/-- The source successor scale `b_j = ceil((k-j+1)b/j)`. -/
def wooleyNextB (k r b : ℕ) : ℕ :=
  ((k - r + 1) * b) ⌈/⌉ r

theorem wooleyRho_pos
    {k r : ℕ} (hr : 1 ≤ r) :
    0 < wooleyRho k r := by
  unfold wooleyRho
  positivity

theorem wooley_nextB_lower
    {k r b : ℕ} (hr : 1 ≤ r) :
    (k - r + 1) * b ≤ r * wooleyNextB k r b := by
  exact le_smul_ceilDiv (by omega : 0 < r)

theorem wooley_nextB_le_k_mul
    {k r b : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    wooleyNextB k r b ≤ k * b := by
  rw [wooleyNextB, ceilDiv_le_iff_le_mul (by omega : 0 < r)]
  have hkr : k - r + 1 ≤ k := by omega
  have hb : (k - r + 1) * b ≤ k * b :=
    Nat.mul_le_mul_right b hkr
  exact hb.trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (k * b) hr)

#print axioms wooley_iteration_length_lower
#print axioms wooley_iteration_length_pos
#print axioms wooley_iteration_final_bounds_contradict
#print axioms wooley_iteration_length_final_bound_impossible
#print axioms wooleyRho_pos
#print axioms wooley_nextB_lower
#print axioms wooley_nextB_le_k_mul

end

end GafniTao

import Mathlib.NumberTheory.ZetaValues
import PrimeNumberTheoremAnd.EulerMaclaurin

open Complex Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# The periodic Euler--Maclaurin functions in DFI equation (12)

DFI write their periodic function as a paired Fourier series.  The canonical
real representative is the periodized Bernoulli polynomial `B_j({x}) / j!`.
For `j = 1` its value at an integer is immaterial to every Lebesgue integral;
we use the right-continuous representative, which is exactly the `B1` used by
the pinned Euler--Maclaurin theorem.
-/

/-- The periodic Bernoulli representative of DFI's `ψ_j`. -/
noncomputable def dfiPsi (j : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun j (Int.fract x) / j.factorial

@[simp]
theorem dfiPsi_zero (x : ℝ) : dfiPsi 0 x = 1 := by
  simp [dfiPsi, bernoulliFun_zero]

/-- At first order the DFI periodic function is the first Bernoulli sawtooth
used by the project's exact Euler--Maclaurin formula. -/
theorem dfiPsi_one_eq_B1 (x : ℝ) (hx : 0 ≤ x) : dfiPsi 1 x = B1 x := by
  rw [dfiPsi, bernoulliFun_one]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, B1, Int.fract]
  rw [natCast_floor_eq_intCast_floor hx]

/-- `dfiPsi` is one-periodic. -/
theorem dfiPsi_add_intCast (j : ℕ) (x : ℝ) (n : ℤ) :
    dfiPsi j (x + n) = dfiPsi j x := by
  simp [dfiPsi, Int.fract_add_intCast]

/-- Away from the integer discontinuities of the first Bernoulli
representative, DFI's periodic function has parity `j`. -/
theorem dfiPsi_neg_of_fract_ne_zero (j : ℕ) (x : ℝ)
    (hx : Int.fract x ≠ 0) :
    dfiPsi j (-x) = (-1 : ℝ) ^ j * dfiPsi j x := by
  unfold dfiPsi
  rw [Int.fract_neg hx, bernoulliFun_eval_one_sub]
  ring

/-- The exceptional integer lattice is null, so the parity identity holds
almost everywhere in every Lebesgue integral used in DFI equation (12). -/
theorem dfiPsi_neg_ae (j : ℕ) :
    ∀ᵐ x : ℝ, dfiPsi j (-x) = (-1 : ℝ) ^ j * dfiPsi j x := by
  have hset : {x : ℝ | Int.fract x = 0} =
      Set.range (fun z : ℤ => (z : ℝ)) := by
    ext x
    constructor
    · intro hx
      refine ⟨⌊x⌋, ?_⟩
      change x - (⌊x⌋ : ℝ) = 0 at hx
      linarith
    · rintro ⟨z, rfl⟩
      simp
  have hcount : {x : ℝ | Int.fract x = 0}.Countable := by
    rw [hset]
    exact Set.countable_range _
  filter_upwards [hcount.ae_notMem (MeasureTheory.volume :
    MeasureTheory.Measure ℝ)] with x hx
  exact dfiPsi_neg_of_fract_ne_zero j x hx

/-- From order two onward the Bernoulli endpoint values match, so the
periodized DFI function is genuinely continuous. -/
theorem continuous_dfiPsi {j : ℕ} (hj : j ≠ 1) :
    Continuous (dfiPsi j) := by
  have hend : bernoulliFun j (0 : ℝ) = bernoulliFun j 1 :=
    (bernoulliFun_endpoints_eq_of_ne_one hj).symm
  have hcomp : Continuous (bernoulliFun j ∘ Int.fract) :=
    (continuous_bernoulliFun j).continuousOn.comp_fract'' hend
  unfold dfiPsi
  exact hcomp.div_const _

/-- For every order other than the sawtooth order one, parity holds
pointwise, including on the integer lattice because the Bernoulli endpoint
values then agree. -/
theorem dfiPsi_neg {j : ℕ} (hj : j ≠ 1) (x : ℝ) :
    dfiPsi j (-x) = (-1 : ℝ) ^ j * dfiPsi j x := by
  by_cases hx : Int.fract x = 0
  · have hnx : Int.fract (-x) = 0 := Int.fract_neg_eq_zero.mpr hx
    unfold dfiPsi
    rw [hx, hnx]
    have hend := bernoulliFun_endpoints_eq_of_ne_one hj
    have href := bernoulliFun_eval_one_sub (k := j) (x := (0 : ℝ))
    norm_num at href
    have hpar : bernoulliFun j (0 : ℝ) =
        (-1 : ℝ) ^ j * bernoulliFun j 0 := hend.symm.trans href
    calc
      bernoulliFun j 0 / (j.factorial : ℝ) =
          ((-1 : ℝ) ^ j * bernoulliFun j 0) / j.factorial :=
        congrArg (fun y : ℝ => y / j.factorial) hpar
      _ = (-1 : ℝ) ^ j *
          (bernoulliFun j 0 / (j.factorial : ℝ)) := by ring
  · exact dfiPsi_neg_of_fract_ne_zero j x hx

/-- The Bernoulli representative is uniformly bounded for each fixed order.
This is the precise form needed in DFI estimates (14)--(18): its constant may
depend on `j` and on no analytic scale. -/
theorem exists_bound_dfiPsi (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |dfiPsi j x| ≤ C := by
  let F : ℝ → ℝ := fun y => |bernoulliFun j y / j.factorial|
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hF.continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, fun x => ?_⟩
  have hfract : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hy : F (Int.fract x) ≤ C := hC ⟨Int.fract x, hfract, rfl⟩
  change F (Int.fract x) ≤ max 1 C
  exact hy.trans (le_max_right _ _)

/-- For orders at least two, the paired Fourier series printed immediately
after DFI equation (12) converges absolutely to `dfiPsi`.  The source starts
at `m = 1`; the `m = 0` term below is definitionally zero and lets us use
Mathlib's Bernoulli Fourier theorem without a reindexing wrapper. -/
theorem hasSum_dfiPsi_fourier {j : ℕ} (hj : 2 ≤ j) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (fun m : ℕ =>
        -(((2 : ℂ) * Real.pi * I * m) ^ j)⁻¹ *
          (fourier m (x : UnitAddCircle) +
            (-1 : ℂ) ^ j * fourier (-(m : ℤ)) (x : UnitAddCircle)))
      (dfiPsi j x : ℂ) := by
  have h := hasSum_one_div_nat_pow_mul_fourier hj hx
  have hm := h.mul_left (-(((2 : ℂ) * Real.pi * I) ^ j)⁻¹)
  have hm' : HasSum
      (fun m : ℕ =>
        -(((2 : ℂ) * Real.pi * I * m) ^ j)⁻¹ *
          (fourier m (x : UnitAddCircle) +
            (-1 : ℂ) ^ j * fourier (-(m : ℤ)) (x : UnitAddCircle)))
      (-(((2 : ℂ) * Real.pi * I) ^ j)⁻¹ *
        (-((2 : ℂ) * Real.pi * I) ^ j / j.factorial * bernoulliFun j x)) :=
    hm.congr_fun (fun m => by
      simp only [one_div]
      simp only [mul_pow, mul_inv_rev]
      ring)
  have hbern : bernoulliFun j (Int.fract x) = bernoulliFun j x := by
    rw [← Set.Ico_insert_right (zero_le_one' ℝ), Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · simp [bernoulliFun_endpoints_eq_of_ne_one (by omega : j ≠ 1)]
    · rw [Int.fract_eq_self.mpr hx]
  have htarget :
      -(((2 : ℂ) * Real.pi * I) ^ j)⁻¹ *
          (-((2 : ℂ) * Real.pi * I) ^ j / j.factorial * bernoulliFun j x) =
        (dfiPsi j x : ℂ) := by
    change _ = ((bernoulliFun j (Int.fract x) / j.factorial : ℝ) : ℂ)
    push_cast
    rw [hbern]
    have hbase : ((2 : ℂ) * Real.pi * I) ^ j ≠ 0 := by
      apply pow_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    field_simp
  rw [← htarget]
  exact hm'

end RiemannZeta.GuthMaynard

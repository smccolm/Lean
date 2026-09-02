import GafniTao.FordLemma51CoreBound

/-!
# Scale algebra for Ford's Lemma 5.1 specialization

The lemmas here contain the exact floor and logarithmic bridges needed to
specialize `M₁=N^(1/5)`, `M₂=N^(1/10)` and to use the central degree band.
-/

namespace GafniTao

noncomputable section

theorem ford_natFloor_ge_half {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  have hhalf : 1 ≤ x / 2 := by linarith
  linarith

theorem ford_rpow_lambda_eq
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t) :
    (N : ℝ) ^ fordLambda N t = t := by
  have hNr : (0 : ℝ) < N := by positivity
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  rw [Real.rpow_def_of_pos hNr]
  unfold fordLambda
  have hexp : Real.log (N : ℝ) * (Real.log t / Real.log (N : ℝ)) =
      Real.log t := by field_simp
  rw [hexp, Real.exp_log ht]

theorem ford_lambda_band_t_bounds
    {N k : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    (N : ℝ) ^ ((69 / 100 : ℝ) * k) ≤ t ∧
      t ≤ (N : ℝ) ^ ((7 / 10 : ℝ) * k) := by
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  rw [← ford_rpow_lambda_eq hN ht]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hNone hlower,
    Real.rpow_le_rpow_of_exponent_le hNone hupper⟩

theorem fordGoodDegree_real_bounds
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    (41 / 50 : ℝ) * k ≤ ((j : ℕ) + 1 : ℕ) ∧
      (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (87 / 100 : ℝ) * k := by
  obtain ⟨hlower, hupper⟩ := fordGoodDegree_mem_bounds hj
  have hlowerR : (41 : ℝ) * k ≤ 50 * (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlower
  have hupperR : (100 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ) ≤ 87 * k := by
    exact_mod_cast hupper
  constructor <;> norm_num at * <;> linarith

theorem fordGoodDegree_first_exponent
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    -((((j : ℕ) + 1 : ℕ) : ℝ) / 5) ≤ -(41 / 250 : ℝ) * k := by
  have h := (fordGoodDegree_real_bounds hj).1
  linarith

theorem fordGoodDegree_second_exponent
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    (7 / 10 : ℝ) * k - (((j : ℕ) + 1 : ℕ) : ℝ) ≤
      -(3 / 25 : ℝ) * k := by
  have h := (fordGoodDegree_real_bounds hj).1
  linarith

theorem fordGoodDegree_third_exponent
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    (7 / 10 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ) -
        (69 / 100 : ℝ) * k ≤ -(81 / 1000 : ℝ) * k := by
  have h := (fordGoodDegree_real_bounds hj).2
  linarith

theorem fordGoodDegree_fourth_exponent
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    -((((j : ℕ) + 1 : ℕ) : ℝ) / 10) ≤ -(41 / 500 : ℝ) * k := by
  have h := (fordGoodDegree_real_bounds hj).1
  linarith

theorem ford_two_le_tenth_scale {x : ℝ} (hx : 1024 ≤ x) :
    2 ≤ x ^ (1 / 10 : ℝ) := by
  have hbase : (0 : ℝ) ≤ 2 := by norm_num
  have hroot : (((2 : ℝ) ^ 10) ^ ((10 : ℕ)⁻¹ : ℝ)) = 2 :=
    Real.pow_rpow_inv_natCast hbase (by norm_num)
  have hpow : ((2 : ℝ) ^ 10) ^ (1 / 10 : ℝ) ≤
      x ^ (1 / 10 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity)
    · norm_num at hx ⊢
      exact hx
    · norm_num
  norm_num at hroot
  linarith

/-- Basic positivity, floor, and upper-scale facts for Ford's choices
`M₁=x^(1/5)` and `M₂=x^(1/10)`. -/
theorem ford_basic_scale_data {x : ℝ} (hx : 1024 ≤ x) :
    2 ≤ x ^ (1 / 5 : ℝ) ∧
    2 ≤ x ^ (1 / 10 : ℝ) ∧
    x ^ (1 / 5 : ℝ) / 2 ≤ (⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) ∧
    1 ≤ ⌊x ^ (1 / 5 : ℝ)⌋₊ ∧
    1 ≤ ⌊x ^ (1 / 10 : ℝ)⌋₊ ∧
    x ^ (1 / 5 : ℝ) ≤ x ∧
    x ^ (1 / 10 : ℝ) ≤ x ∧
    x ^ (1 / 5 : ℝ) * x ^ (1 / 10 : ℝ) ≤ x := by
  have hxone : (1 : ℝ) ≤ x := by linarith
  have htenth := ford_two_le_tenth_scale hx
  have hfifthMono : x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hfifth : 2 ≤ x ^ (1 / 5 : ℝ) := htenth.trans hfifthMono
  have hfloorF := ford_natFloor_ge_half hfifth
  have hfloorFone : 1 ≤ ⌊x ^ (1 / 5 : ℝ)⌋₊ := by
    exact_mod_cast (show (1 : ℝ) ≤ (⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) by linarith)
  have hfloorTone : 1 ≤ ⌊x ^ (1 / 10 : ℝ)⌋₊ :=
    Nat.floor_pos.mpr (by linarith)
  have hfifthTop := Real.rpow_le_rpow_of_exponent_le hxone
    (show (1 / 5 : ℝ) ≤ 1 by norm_num)
  have htenthTop := Real.rpow_le_rpow_of_exponent_le hxone
    (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hfifthTop' : x ^ (1 / 5 : ℝ) ≤ x := by simpa using hfifthTop
  have htenthTop' : x ^ (1 / 10 : ℝ) ≤ x := by simpa using htenthTop
  have hprodEq : x ^ (1 / 5 : ℝ) * x ^ (1 / 10 : ℝ) =
      x ^ (3 / 10 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < x)]
    congr 1
    norm_num
  have hprodTop : x ^ (1 / 5 : ℝ) * x ^ (1 / 10 : ℝ) ≤ x := by
    rw [hprodEq]
    simpa using Real.rpow_le_rpow_of_exponent_le hxone
      (show (3 / 10 : ℝ) ≤ 1 by norm_num)
  exact ⟨hfifth, htenth, hfloorF, hfloorFone, hfloorTone,
    hfifthTop', htenthTop', hprodTop⟩

#print axioms ford_natFloor_ge_half
#print axioms ford_rpow_lambda_eq
#print axioms ford_lambda_band_t_bounds
#print axioms fordGoodDegree_third_exponent
#print axioms ford_basic_scale_data

end

end GafniTao

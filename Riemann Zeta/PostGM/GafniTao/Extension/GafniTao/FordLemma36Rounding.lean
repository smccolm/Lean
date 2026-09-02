import GafniTao.FordLemma35Induction

/-!
# Ford Lemma 3.6: the rounded `r_n`

This module formalizes the choice
`r = floor(k - Delta/k + 1)` and the resulting two-sided estimate for Ford's
quantity `y`.  These are the entry inequalities used to verify (3.11).
-/

namespace GafniTao

noncomputable section

def fordR36 (k : ℕ) (delta : ℝ) : ℕ :=
  ⌊(k : ℝ) - delta / k + 1⌋₊

theorem fordR36_real_bounds
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    (k : ℝ) - delta / k ≤ fordR36 k delta ∧
      (fordR36 k delta : ℝ) ≤ (k : ℝ) - delta / k + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let x : ℝ := (k : ℝ) - delta / k + 1
  have hx : 0 ≤ x := by
    dsimp [x]
    have : delta / (k : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
      apply (div_le_iff₀ hkR).2
      nlinarith
    have hk26 : (26 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hfloor : (fordR36 k delta : ℝ) ≤ x := by
    exact Nat.floor_le hx
  have hnext : x < (fordR36 k delta : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  constructor
  · dsimp [x] at hnext
    linarith
  · exact hfloor

theorem fordR36_bounds
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaLower : (k : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    4 ≤ fordR36 k delta ∧ fordR36 k delta ≤ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hreal := fordR36_real_bounds hk hdeltaUpper
  have hdeltaDivLower : 1 ≤ delta / (k : ℝ) :=
    (le_div_iff₀ hkR).2 (by simpa using hdeltaLower)
  have hdeltaDivUpper : delta / (k : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
    apply (div_le_iff₀ hkR).2
    nlinarith
  have hk26 : (26 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · have hfourR : (4 : ℝ) ≤ fordR36 k delta := by
      linarith [hreal.1]
    exact_mod_cast hfourR
  · have hrkR : (fordR36 k delta : ℝ) ≤ k := by
      linarith [hreal.2]
    exact_mod_cast hrkR

theorem fordY35_rounded_bounds
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaLower : (k : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let a := delta / (k : ℝ)
    a * (2 * (k : ℝ) - a - 1) ≤
        fordY35 k (fordR36 k delta) delta ∧
      fordY35 k (fordR36 k delta) delta ≤
        a * (2 * (k : ℝ) - a + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let a : ℝ := delta / (k : ℝ)
  let q : ℝ := (k : ℝ) - fordR36 k delta
  have hreal := fordR36_real_bounds hk hdeltaUpper
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact (le_div_iff₀ hkR).2 (by simpa using hdeltaLower)
  have hqa : q ≤ a := by
    dsimp [q, a]
    linarith [hreal.1]
  have haq : a - 1 ≤ q := by
    dsimp [q, a]
    linarith [hreal.2]
  have hq0 : 0 ≤ q := by linarith
  have hfirst : 0 ≤ (a - q) * (a + q + 1) := mul_nonneg (sub_nonneg.mpr hqa)
    (by linarith)
  have hsecond : 0 ≤ (q - (a - 1)) * (q + a) :=
    mul_nonneg (sub_nonneg.mpr haq) (by linarith)
  have hdeltaEq : delta = a * (k : ℝ) := by
    dsimp [a]
    field_simp
  dsimp only
  change a * (2 * (k : ℝ) - a - 1) ≤
      2 * delta - q * (q + 1) ∧
    2 * delta - q * (q + 1) ≤ a * (2 * (k : ℝ) - a + 1)
  constructor <;> nlinarith

theorem fordY35_rounded_nonneg
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaLower : (k : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    0 ≤ fordY35 k (fordR36 k delta) delta := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let a : ℝ := delta / (k : ℝ)
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact (le_div_iff₀ hkR).2 (by simpa using hdeltaLower)
  have haUpper : a ≤ ((k : ℝ) - 1) / 2 := by
    dsimp [a]
    apply (div_le_iff₀ hkR).2
    nlinarith
  have hk26 : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hfactor : 0 ≤ 2 * (k : ℝ) - a - 1 := by linarith
  exact (mul_nonneg (by linarith) hfactor).trans
    (fordY35_rounded_bounds hk hdeltaLower hdeltaUpper).1

theorem fordPhiStar35_rounded_lower
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaLower : (k : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    1 / (((k + 1 : ℕ) : ℝ)) ≤
      fordPhiStar35 k (fordR36 k delta) delta := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let a : ℝ := delta / (k : ℝ)
  let r := fordR36 k delta
  have hr := (fordR36_bounds hk hdeltaLower hdeltaUpper).1
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy := fordY35_rounded_nonneg hk hdeltaLower hdeltaUpper
  have hden : 0 < 2 * (r : ℝ) * k + fordY35 k r delta := by positivity
  have hrUpper := (fordR36_real_bounds hk hdeltaUpper).2
  have hyUpper := (fordY35_rounded_bounds hk hdeltaLower hdeltaUpper).2
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact (le_div_iff₀ hkR).2 (by simpa using hdeltaLower)
  have hdenUpper :
      2 * (r : ℝ) * k + fordY35 k r delta ≤ 2 * (k : ℝ) * (k + 1) := by
    dsimp [a] at hrUpper hyUpper ⊢
    nlinarith [sq_nonneg (delta / (k : ℝ) - 1)]
  unfold fordPhiStar35
  rw [div_le_div_iff₀ (by positivity :
      (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) hden]
  push_cast
  simpa [r] using hdenUpper

#print axioms fordR36_real_bounds
#print axioms fordR36_bounds
#print axioms fordY35_rounded_bounds
#print axioms fordY35_rounded_nonneg
#print axioms fordPhiStar35_rounded_lower

end

end GafniTao

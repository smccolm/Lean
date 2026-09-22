import TaoTrudgianYang2025.HeathBrownModelJets

/-!
# Exact exponents in the Heath--Brown beta estimate

The displayed source formula is retained. Its algebraic identities connect
the kth-derivative scale T/N^k to three explicit monomials in T and N.
-/

noncomputable section

namespace TaoTrudgianYang2025

def heathBrownDerivativeExponent (k : ℕ) : ℝ :=
  1 / ((k : ℝ)*(k-1))

def heathBrownInverseExponent (k : ℕ) : ℝ :=
  2 / ((k : ℝ)^2*(k-1))

def heathBrownBetaBound (k : ℕ) (α : ℝ) : ℝ :=
  α + max ((1-(k : ℝ)*α)/((k : ℝ)*(k-1)))
    (max (-α/((k : ℝ)*(k-1)))
      (-2*α/((k : ℝ)*(k-1))-2*(1-(k : ℝ)*α)/((k : ℝ)^2*(k-1))))

theorem heathBrownDerivativeExponent_bounds {k : ℕ} (hk : 3 ≤ k) :
    0 < heathBrownDerivativeExponent k ∧
      (k : ℝ)*heathBrownDerivativeExponent k ≤ 1 ∧
      heathBrownDerivativeExponent k ≤ 1/6 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < k-1 := by linarith
  unfold heathBrownDerivativeExponent
  refine ⟨by positivity,?_,?_⟩
  · calc
      (k : ℝ)*(1/((k : ℝ)*(k-1))) = (k : ℝ)/((k : ℝ)*(k-1)) := by ring
      _ ≤ 1 := (div_le_iff₀ (mul_pos hp hm)).mpr (by nlinarith)
  · apply (div_le_iff₀ (mul_pos hp hm)).mpr
    nlinarith

theorem heathBrownInverseExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < heathBrownInverseExponent k := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold heathBrownInverseExponent
  have hm : (0 : ℝ) < k-1 := by linarith
  positivity

theorem heathBrownInverseExponent_identity {k : ℕ} (hk : 3 ≤ k) :
    (k : ℝ)*heathBrownInverseExponent k = 2*heathBrownDerivativeExponent k := by
  have hp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold heathBrownInverseExponent heathBrownDerivativeExponent
  field_simp

theorem heathBrownBetaBound_eq_max {k : ℕ} (hk : 3 ≤ k) (α : ℝ) :
    heathBrownBetaBound k α =
      max (heathBrownDerivativeExponent k+α*(1-(k : ℝ)*heathBrownDerivativeExponent k))
        (max (α*(1-heathBrownDerivativeExponent k)) (α-heathBrownInverseExponent k)) := by
  have hp : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hm : (k : ℝ)-1 ≠ 0 := by
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold heathBrownBetaBound heathBrownDerivativeExponent heathBrownInverseExponent
  rw [add_max,add_max]
  congr 1
  · ring
  · congr 1
    · ring
    · field_simp
      ring

theorem heathBrownBetaBound_nonneg {k : ℕ} (hk : 3 ≤ k)
    {α : ℝ} (hα : 0 ≤ α) : 0 ≤ heathBrownBetaBound k α := by
  rw [heathBrownBetaBound_eq_max hk]
  have hd := (heathBrownDerivativeExponent_bounds hk).2.2
  have hz : 0 ≤ α*(1-heathBrownDerivativeExponent k) :=
    mul_nonneg hα (by linarith)
  exact hz.trans ((le_max_left _ _).trans (le_max_right _ _))

theorem heathBrown_physical_monomial {c T N : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hN : 0 < N)
    (k : ℕ) (η ζ r : ℝ) :
    N^(1+η-ζ)*(c*T/N^k)^r =
      c^r*N^η*T^r*N^(1-ζ-(k : ℝ)*r) := by
  apply Real.log_injOn_pos (show 0 < N^(1+η-ζ)*(c*T/N^k)^r by positivity)
    (show 0 < c^r*N^η*T^r*N^(1-ζ-(k : ℝ)*r) by positivity)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hN,Real.log_rpow (show 0 < c*T/N^k by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hc.ne' hT.ne',Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hc,Real.log_rpow hN,Real.log_rpow hT,Real.log_rpow hN]
  ring

end TaoTrudgianYang2025

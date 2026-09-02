import GafniTao.FordTheorem3Exponent

/-!
# Ford Theorem 3: asymptotic-coefficient form

The published theorem records an explicit coefficient.  For the Gafni--Tao
right-edge argument only finiteness of a coefficient depending on the fixed
moment parameters is used.  The theorem below therefore preserves Ford's
literal range and exponent while existentially absorbing the finite leading
constant supplied by the audited PNT prime packet.
-/

namespace GafniTao

noncomputable section

/-- Assembly at a supplied decomposition `s = n k + u`. -/
theorem ford_theorem_3_decomposed
    {n k u : ℕ} (hk : 1000 ≤ k) (hnLower : 2 * k ≤ n)
    (hnUpper : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)))
    (hu : u ≤ k) :
    ∃ C : ℝ, FordVinogradovMomentBound (n * k + u) k C
      ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * ((n * k + u : ℕ) : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ)))) := by
  let D₀ : ℝ := fordDeltaSequence36 k (n - 1)
  let D₁ : ℝ := fordDeltaSequence36 k n
  let E₀ : ℝ := (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
    (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ)))
  let E₁ : ℝ := (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
    (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
      169 / (100 * (k : ℝ)))
  let p : ℝ := ((k : ℝ) - u) / (k : ℝ)
  let q : ℝ := (u : ℝ) / (k : ℝ)
  have hk0 : (0 : ℝ) < k := by positivity
  have hp : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hu)) hk0.le
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hnSource₀ : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 := by
    linarith
  have hnSource₁ : ((n + 1 : ℕ) : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 := by
    push_cast
    linarith
  obtain ⟨C₀, hmoment₀, hD₀⟩ :=
    fordLemma36_native hk hnLower hnSource₀
  obtain ⟨C₁, hmoment₁, hD₁⟩ :=
    fordLemma36_native hk (by omega : 2 * k ≤ n + 1) hnSource₁
  have hinterp := hmoment₀.interpolate (by omega : 1 ≤ k) hu hmoment₁
  have hweighted : p * D₀ + q * D₁ ≤ p * E₀ + q * E₁ := by
    dsimp [D₀, D₁, E₀, E₁]
    exact add_le_add (mul_le_mul_of_nonneg_left hD₀ hp)
      (mul_le_mul_of_nonneg_left hD₁ hq)
  have hfinal : p * E₀ + q * E₁ ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * ((n * k + u : ℕ) : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ))) := by
    simpa [p, q, E₀, E₁] using
      (ford_theorem3_weighted_delta_le (n := n) hk hu)
  refine ⟨C₀ ^ p * C₁ ^ q, ?_⟩
  exact hinterp.mono_delta (hweighted.trans hfinal)

/-- Ford Theorem 3 in the exact published `k ≥ 1000` moment range and with
the exact exponent `Delta_s`. -/
theorem ford_theorem_3_native
    {s k : ℕ} (hk : 1000 ≤ k) (hsLower : 2 * k ^ 2 ≤ s)
    (hsUpper : (s : ℝ) ≤
      (k : ℝ) ^ 2 / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8))) :
    ∃ C : ℝ, FordVinogradovMomentBound s k C
      ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * (s : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ)))) := by
  let n : ℕ := s / k
  let u : ℕ := s % k
  have hkPos : 0 < k := by omega
  have hnLower : 2 * k ≤ n := by
    apply (Nat.le_div_iff_mul_le hkPos).2
    dsimp [n]
    simpa [pow_two, mul_assoc] using hsLower
  have huLt : u < k := by
    dsimp [u]
    exact Nat.mod_lt _ hkPos
  have hu : u ≤ k := huLt.le
  have hnMul : n * k ≤ s := by
    dsimp [n]
    exact Nat.div_mul_le_self s k
  have hnLeDiv : (n : ℝ) ≤ (s : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k)]
    exact_mod_cast hnMul
  have hsDivUpper : (s : ℝ) / (k : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < k)]
    calc
      (s : ℝ) ≤ (k : ℝ) ^ 2 / 2 *
          (1 / 2 + Real.log (3 * (k : ℝ) / 8)) := hsUpper
      _ = ((k : ℝ) / 2 *
          (1 / 2 + Real.log (3 * (k : ℝ) / 8))) * k := by ring
  have hnUpper : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) :=
    hnLeDiv.trans hsDivUpper
  obtain ⟨C, hC⟩ := ford_theorem_3_decomposed hk hnLower hnUpper hu
  have hdecomp : n * k + u = s := by
    dsimp [n, u]
    simpa [Nat.mul_comm] using Nat.div_add_mod s k
  rw [hdecomp] at hC
  exact ⟨C, hC⟩

#print axioms ford_theorem_3_decomposed
#print axioms ford_theorem_3_native

end

end GafniTao

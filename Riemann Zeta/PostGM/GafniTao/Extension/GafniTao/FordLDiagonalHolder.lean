import GafniTao.FordLAwayFourier
import GafniTao.FordKPowerMoment

/-!
# Ford Lemma 3.3: Hölder for the diagonal branch

This is the literal two-factor Hölder step
`R ≤ L^(1-1/k) J^(1/k)` for the reduced `(k-1)`-coordinate mean.  Counts are
identified with their normalized-torus integrals before the inequality is
stated, so no detached analytic certificate is introduced.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

theorem ford_lintegral_two_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (A B : α → ENNReal) (p q : ℝ)
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hsum : p + q = 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫⁻ a, A a ^ p * B a ^ q ∂μ) ≤
      (∫⁻ a, A a ∂μ) ^ p * (∫⁻ a, B a ∂μ) ^ q := by
  let f : Fin 2 → α → ENNReal := ![A, B]
  let w : Fin 2 → ℝ := ![p, q]
  have hf : ∀ i ∈ Finset.univ, AEMeasurable (f i) μ := by
    intro i hi
    fin_cases i <;> simp [f, hA, hB]
  have hw : ∑ i ∈ Finset.univ, w i = 1 := by
    simpa [Fin.sum_univ_two, w] using hsum
  have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i hi
    fin_cases i <;> simp [w, hp, hq]
  simpa [Fin.prod_univ_two, f, w] using
    (ENNReal.lintegral_prod_norm_pow_le Finset.univ hf hw hw0)

theorem ford_diagonal_holder_point
    {k : ℕ} (hk : 1 ≤ k) (x z : ENNReal) :
    (x ^ k * z) ^ (1 - 1 / (k : ℝ)) * z ^ (1 / (k : ℝ)) =
      x ^ (k - 1) * z := by
  let p : ℝ := 1 - 1 / (k : ℝ)
  let q : ℝ := 1 / (k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ p := by
    dsimp [p]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkp : (k : ℝ) * p = (k - 1 : ℕ) := by
    dsimp [p]
    rw [Nat.cast_sub hk]
    norm_num
    field_simp
  have hpq : p + q = 1 := by
    dsimp [p, q]
    field_simp
    ring
  simp_rw [← ENNReal.rpow_natCast]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp, ← ENNReal.rpow_mul]
  calc
    x ^ ((k : ℝ) * p) * z ^ p * z ^ q =
        x ^ ((k : ℝ) * p) * z ^ (p + q) := by
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hp hq]
    _ = x ^ ((k - 1 : ℕ) : ℝ) * z := by
      rw [hkp, hpq, ENNReal.rpow_one]

theorem fordL_reduced_holder
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ)
    (hk : 1 ≤ k) (hpq : 0 < p * q) :
    (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ENNReal) ≤
      (fordLCount Ψ s P Q p q r : ENNReal) ^ (1 - 1 / (k : ℝ)) *
        (fordVinogradovMomentNat s k Q : ENNReal) ^ (1 / (k : ℝ)) := by
  let E : UnitAddTorus (Fin k) → ℝ :=
    fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ
  let F : UnitAddTorus (Fin k) → ℝ := fun α ↦
    ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
  let A : UnitAddTorus (Fin k) → ENNReal := fun α ↦
    ENNReal.ofReal (E α ^ k * F α)
  let B : UnitAddTorus (Fin k) → ENNReal := fun α ↦ ENNReal.ofReal (F α)
  let a : ℝ := 1 - 1 / (k : ℝ)
  let b : ℝ := 1 / (k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hA : AEMeasurable A (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      (((continuous_fordLCoordinateEnergy Ψ).pow k).mul
        ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s))))
      |>.aemeasurable
  have hB : AEMeasurable B (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s)))
      |>.aemeasurable
  have hholder := ford_lintegral_two_holder A B a b hA hB hab ha hb
  have hleft : (∫⁻ α, A α ^ a * B α ^ b ∂fordTorusMeasure k) =
      ENNReal.ofReal
        (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℝ) := by
    calc
      _ = ∫⁻ α, ENNReal.ofReal (E α ^ (k - 1) * F α)
          ∂fordTorusMeasure k := by
        apply lintegral_congr
        intro α
        have hE : 0 ≤ E α := fordLCoordinateEnergy_nonneg Ψ α
        have hF : 0 ≤ F α := by dsimp [F]; positivity
        have hAe : A α = ENNReal.ofReal (E α) ^ k * ENNReal.ofReal (F α) := by
          simp [A, ENNReal.ofReal_mul, ENNReal.ofReal_pow, hE]
        have hBe : B α = ENNReal.ofReal (F α) := by rfl
        rw [hAe, hBe]
        rw [ford_diagonal_holder_point hk]
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, hE]
      _ = ENNReal.ofReal (∫ α, E α ^ (k - 1) * F α
          ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordL_energy_integrand Ψ s Q q (k - 1))
          (Filter.Eventually.of_forall fun α ↦
            mul_nonneg (pow_nonneg (fordLCoordinateEnergy_nonneg Ψ α) _)
              (by positivity))).symm
      _ = _ := by
        rw [show (∫ α, E α ^ (k - 1) * F α ∂fordTorusMeasure k) =
          (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℝ) by
            exact fordLReduced_real_mean_eq_count Ψ s Q q]
  have hrightA : (∫⁻ α, A α ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordLCount Ψ s P Q p q r : ℝ) := by
    calc
      _ = ENNReal.ofReal (∫ α, E α ^ k * F α ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordL_energy_integrand Ψ s Q q k)
          (Filter.Eventually.of_forall fun α ↦
            mul_nonneg (pow_nonneg (fordLCoordinateEnergy_nonneg Ψ α) _)
              (by positivity))).symm
      _ = _ := by rw [fordL_real_mean_eq_count Ψ s Q q]
  have hrightB : (∫⁻ α, B α ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordVinogradovMomentNat s k Q : ℝ) := by
    calc
      _ = ENNReal.ofReal (fordPowerMomentIntegral k s Q (p * q)) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordPowerMoment_integrand k s Q (p * q))
          (Filter.Eventually.of_forall fun _ ↦ by positivity)).symm
      _ = _ := by rw [fordPowerMomentIntegral_eq_vinogradov hpq]
  rw [hleft, hrightA, hrightB] at hholder
  simpa [a, b] using hholder

#print axioms ford_lintegral_two_holder
#print axioms ford_diagonal_holder_point
#print axioms fordL_reduced_holder

end

end GafniTao

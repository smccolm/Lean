import GafniTao.FordKRepeatedIntegral

/-!
# Ford Lemma 3.2: the three-factor Hölder estimate

This file proves the exact exponent split
`1-1/k, 1/(2k), 1/(2k)` used in the repeated-coordinate contradiction.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

theorem ford_lintegral_three_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (A B C : α → ENNReal) (p q r : ℝ)
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hC : AEMeasurable C μ)
    (hsum : p + q + r = 1) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) :
    (∫⁻ a, A a ^ p * B a ^ q * C a ^ r ∂μ) ≤
      (∫⁻ a, A a ∂μ) ^ p * (∫⁻ a, B a ∂μ) ^ q *
        (∫⁻ a, C a ∂μ) ^ r := by
  let f : Fin 3 → α → ENNReal := ![A, B, C]
  let w : Fin 3 → ℝ := ![p, q, r]
  have hf : ∀ i ∈ Finset.univ, AEMeasurable (f i) μ := by
    intro i hi
    fin_cases i <;> simp [f, hA, hB, hC]
  have hw : ∑ i ∈ Finset.univ, w i = 1 := by
    simpa [Fin.sum_univ_three, w] using hsum
  have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i hi
    fin_cases i <;> simp [w, hp, hq, hr]
  simpa [Fin.prod_univ_three, f, w, mul_assoc] using
    (ENNReal.lintegral_prod_norm_pow_le Finset.univ hf hw hw0)

theorem ford_three_holder_point
    {k s : ℕ} (hk : 1 ≤ k) (x y z : ENNReal) :
    (x ^ (2 * k) * z ^ (2 * s)) ^ (1 - 1 / (k : ℝ)) *
        (z ^ (2 * s)) ^ (1 / (2 * k : ℝ)) *
          (y ^ (2 * k) * z ^ (2 * s)) ^ (1 / (2 * k : ℝ)) =
      x ^ ((2 * k - 2 : ℕ) : ℝ) * y *
        z ^ ((2 * s : ℕ) : ℝ) := by
  let p : ℝ := 1 - 1 / (k : ℝ)
  let q : ℝ := 1 / (2 * k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ p := by
    dsimp [p]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hs0 : 0 ≤ (2 * (s : ℝ)) := by positivity
  have hsp : 0 ≤ (2 * (s : ℝ)) * p := mul_nonneg hs0 hp
  have hsq : 0 ≤ (2 * (s : ℝ)) * q := mul_nonneg hs0 hq
  have hxp : (2 * (k : ℝ)) * p = (2 * k - 2 : ℕ) := by
    dsimp [p]
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * k)]
    push_cast
    field_simp
  have hyq : (2 * (k : ℝ)) * q = 1 := by
    dsimp [q]
    field_simp
  have hzsum : p + q + q = 1 := by
    dsimp [p, q]
    field_simp
    ring
  have hzexp : (2 * (s : ℝ)) * p + (2 * (s : ℝ)) * q +
      (2 * (s : ℝ)) * q = (2 * (s : ℝ)) * (p + q + q) := by ring
  simp_rw [← ENNReal.rpow_natCast]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
    ENNReal.mul_rpow_of_nonneg _ _ hq]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc
    x ^ (((2 * k : ℕ) : ℝ) * p) * z ^ (((2 * s : ℕ) : ℝ) * p) *
          z ^ (((2 * s : ℕ) : ℝ) * q) *
          (y ^ (((2 * k : ℕ) : ℝ) * q) *
            z ^ (((2 * s : ℕ) : ℝ) * q)) =
        x ^ (((2 * k : ℕ) : ℝ) * p) *
          y ^ (((2 * k : ℕ) : ℝ) * q) *
          (z ^ (((2 * s : ℕ) : ℝ) * p) *
            z ^ (((2 * s : ℕ) : ℝ) * q) *
            z ^ (((2 * s : ℕ) : ℝ) * q)) := by ac_rfl
    _ = x ^ (((2 * k : ℕ) : ℝ) * p) *
          y ^ (((2 * k : ℕ) : ℝ) * q) *
          z ^ (((2 * s : ℕ) : ℝ) * p +
            ((2 * s : ℕ) : ℝ) * q +
            ((2 * s : ℕ) : ℝ) * q) := by
      push_cast
      rw [← ENNReal.rpow_add_of_nonneg _ _ hsp hsq,
        ← ENNReal.rpow_add_of_nonneg _ _ (add_nonneg hsp hsq) hsq]
    _ = x ^ ((2 * k - 2 : ℕ) : ℝ) * y *
          z ^ ((2 * s : ℕ) : ℝ) := by
      push_cast
      rw [hxp, hyq, hzexp, hzsum, ENNReal.rpow_one]
      norm_num

def fordPowerMomentIntegral (k s Q q : ℕ) : ℝ :=
  ∫ a : UnitAddTorus (Fin k),
    ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s) ∂fordTorusMeasure k

theorem integrable_fordPowerMoment_integrand (k s Q q : ℕ) :
    Integrable (fun a : UnitAddTorus (Fin k) ↦
      ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  exact ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s)).continuousOn
    |>.integrableOn_compact isCompact_univ

theorem fordK_repeated_integral_holder
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal (fordKRepeatedIntegral Ψ s P Q q) ≤
      ENNReal.ofReal (fordKFourier Ψ s P Q q) ^ (1 - 1 / (k : ℝ)) *
        ENNReal.ofReal (fordPowerMomentIntegral k s Q q) ^
          (1 / (2 * k : ℝ)) *
        ENNReal.ofReal
          (fordKFourier (fordDoubleIntegerPolynomialSystem Ψ) s P Q q) ^
            (1 / (2 * k : ℝ)) := by
  let F : UnitAddTorus (Fin k) → ℝ := fun a ↦
    ‖fordPolynomialFullWeylSum (P := P) Ψ a‖
  let F₂ : UnitAddTorus (Fin k) → ℝ := fun a ↦
    ‖fordPolynomialDoubleWeylSum (P := P) Ψ a‖
  let f : UnitAddTorus (Fin k) → ℝ := fun a ↦
    ‖fordPowerFullWeylSum k Q q a‖
  let A : UnitAddTorus (Fin k) → ENNReal := fun a ↦
    ENNReal.ofReal (F a ^ (2 * k) * f a ^ (2 * s))
  let B : UnitAddTorus (Fin k) → ENNReal := fun a ↦
    ENNReal.ofReal (f a ^ (2 * s))
  let C : UnitAddTorus (Fin k) → ENNReal := fun a ↦
    ENNReal.ofReal (F₂ a ^ (2 * k) * f a ^ (2 * s))
  let p : ℝ := 1 - 1 / (k : ℝ)
  let r : ℝ := 1 / (2 * k : ℝ)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ p := by
    dsimp [p]
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : p + r + r = 1 := by
    dsimp [p, r]
    field_simp
    ring
  have hA : AEMeasurable A (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      ((((continuous_fordPolynomialFullWeylSum Ψ).norm.pow (2 * k)).mul
        ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s))))).aemeasurable
  have hB : AEMeasurable B (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s))).aemeasurable
  have hC : AEMeasurable C (fordTorusMeasure k) := by
    dsimp [C, F₂]
    unfold fordPolynomialDoubleWeylSum fordCharacterSum
    exact (ENNReal.continuous_ofReal.comp
      (((continuous_finsetSum _ fun _ _ ↦ by fun_prop).norm.pow (2 * k)).mul
        ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s)))).aemeasurable
  have hholder := ford_lintegral_three_holder A B C p r r
    hA hB hC hsum hp hr hr
  have hleft : (∫⁻ a, A a ^ p * B a ^ r * C a ^ r ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordKRepeatedIntegral Ψ s P Q q) := by
    calc
      (∫⁻ a, A a ^ p * B a ^ r * C a ^ r ∂fordTorusMeasure k) =
          ∫⁻ a, ENNReal.ofReal
            (F a ^ (2 * k - 2) * F₂ a * f a ^ (2 * s))
            ∂fordTorusMeasure k := by
        apply lintegral_congr
        intro a
        have hF : 0 ≤ F a := by dsimp [F]; positivity
        have hF₂ : 0 ≤ F₂ a := by dsimp [F₂]; positivity
        have hf : 0 ≤ f a := by dsimp [f]; positivity
        have hAe : A a = ENNReal.ofReal (F a) ^ (2 * k) *
            ENNReal.ofReal (f a) ^ (2 * s) := by
          simp [A, ENNReal.ofReal_mul, ENNReal.ofReal_pow, hF, hf]
        have hBe : B a = ENNReal.ofReal (f a) ^ (2 * s) := by
          simp [B, ENNReal.ofReal_pow, hf]
        have hCe : C a = ENNReal.ofReal (F₂ a) ^ (2 * k) *
            ENNReal.ofReal (f a) ^ (2 * s) := by
          simp [C, ENNReal.ofReal_mul, ENNReal.ofReal_pow, hF₂, hf]
        have hpoint := ford_three_holder_point (s := s) hk
          (ENNReal.ofReal (F a)) (ENNReal.ofReal (F₂ a))
          (ENNReal.ofReal (f a))
        rw [hAe, hBe, hCe]
        rw [hpoint]
        simp [ENNReal.rpow_natCast, ENNReal.ofReal_mul,
          ENNReal.ofReal_pow, hF, hF₂, hf, mul_assoc]
        rw [show (2 : ℝ) * (s : ℝ) = ((2 * s : ℕ) : ℝ) by norm_num,
          ENNReal.rpow_natCast]
      _ = ENNReal.ofReal (∫ a,
            F a ^ (2 * k - 2) * F₂ a * f a ^ (2 * s)
            ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordKRepeated_integrand Ψ s P Q q)
          (Filter.Eventually.of_forall fun _ ↦ by positivity)).symm
      _ = _ := rfl
  have hAI : (∫⁻ a, A a ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordKFourier Ψ s P Q q) := by
    exact (ofReal_integral_eq_lintegral_ofReal
      (by
        rw [← integrableOn_univ]
        exact (((continuous_fordPolynomialFullWeylSum Ψ).norm.pow (2 * k)).mul
          ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s))).continuousOn
          |>.integrableOn_compact isCompact_univ)
      (Filter.Eventually.of_forall fun _ ↦ by positivity)).symm
  have hBI : (∫⁻ a, B a ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordPowerMomentIntegral k s Q q) := by
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_fordPowerMoment_integrand k s Q q)
      (Filter.Eventually.of_forall fun _ ↦ by positivity)).symm
  have hCI : (∫⁻ a, C a ∂fordTorusMeasure k) =
      ENNReal.ofReal
        (fordKFourier (fordDoubleIntegerPolynomialSystem Ψ) s P Q q) := by
    calc
      (∫⁻ a, C a ∂fordTorusMeasure k) =
          ENNReal.ofReal (∫ a,
            F₂ a ^ (2 * k) * f a ^ (2 * s) ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal
          (by
            rw [← integrableOn_univ]
            dsimp [F₂]
            unfold fordPolynomialDoubleWeylSum fordCharacterSum
            exact (((continuous_finsetSum _ fun _ _ ↦ by fun_prop).norm.pow
              (2 * k)).mul
              ((continuous_fordPowerFullWeylSum k Q q).norm.pow
                (2 * s))).continuousOn
              |>.integrableOn_compact isCompact_univ)
          (Filter.Eventually.of_forall fun _ ↦ by positivity)).symm
      _ = _ := by
        unfold fordKFourier
        apply congrArg ENNReal.ofReal
        apply integral_congr_ae
        filter_upwards [] with a
        dsimp [F₂, f]
        rw [fordPolynomialDoubleWeylSum_eq_doubleSystem]
  rw [hleft, hAI, hBI, hCI] at hholder
  exact hholder

#print axioms ford_three_holder_point
#print axioms ford_lintegral_three_holder
#print axioms fordK_repeated_integral_holder

end

end GafniTao

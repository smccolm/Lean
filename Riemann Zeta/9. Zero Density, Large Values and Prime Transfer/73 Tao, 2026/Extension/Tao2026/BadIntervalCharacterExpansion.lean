import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Probability.Independence.Integration
import Tao2026.BadIntervalSmallPrimeMoment

/-!
# Dirichlet-character expansion for the Proposition 6.6 anti-sieve

This module connects the primitive residue-class fibers produced by the
fiftieth-moment expansion to Mathlib's exact orthogonality theorem for all
Dirichlet characters modulo the tuple lcm.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

/-- Exact normalized Dirichlet-character orthogonality for a primitive
natural residue.  This is the indicator identity used in the source after
the Chinese remainder theorem. -/
theorem primitiveResidueIndicator_eq_dirichletCharacterAverage
    {q a b : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    ((if b ≡ a [MOD q] then 1 else 0 : ℝ) : ℂ) =
      (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * χ (b : ZMod q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ haUnit (b : ZMod q)]
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  by_cases hab : b ≡ a [MOD q]
  · have hcast : (a : ZMod q) = (b : ZMod q) := by
      exact (ZMod.natCast_eq_natCast_iff a b q).mpr hab.symm
    simp [hab, hcast, htot]
  · have hcast : (a : ZMod q) ≠ (b : ZMod q) := by
      intro h
      have hab' : a ≡ b [MOD q] :=
        (ZMod.natCast_eq_natCast_iff a b q).mp h
      exact hab hab'.symm
    simp [hab, hcast]

/-- Character observable of the full source product on the prime-tuple
probability space. -/
def taoPrimeTupleCharacterObservable
    {q : ℕ} (χ : DirichletCharacter ℂ q) (m' : ℕ)
    (ω : TaoPrimeTuple) : ℂ :=
  χ (taoPrimeTupleStart m' ω : ZMod q)

/-- Its literal expectation under the independent dyadic-prime law. -/
def taoPrimeTupleCharacterExpectation
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) : ℂ :=
  ∫ ω, taoPrimeTupleCharacterObservable χ m' ω
    ∂taoPrimeTupleMeasure P hP

/-- Coordinate character observable, retaining the distinguished square on
`p₀` and exponent one on the other 1000 coordinates. -/
def taoPrimeCoordinateCharacterObservable
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : Fin 1001) (p : ℕ) : ℂ :=
  if j = 0 then χ (p : ZMod q) ^ (2 : ℕ) else χ (p : ZMod q)

/-- Literal expectation of one coordinate character observable. -/
def taoPrimeCoordinateCharacterExpectation
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (j : Fin 1001) : ℂ :=
  ∫ ω, taoPrimeCoordinateCharacterObservable χ j (ω j)
    ∂taoPrimeTupleMeasure P hP

/-- Pointwise factorization of the character of
`p₀²p₁⋯p₁₀₀₀m'` into the residual factor and 1001 coordinate factors. -/
theorem taoPrimeTupleCharacterObservable_eq_coordinateProduct
    {q : ℕ} (χ : DirichletCharacter ℂ q) (m' : ℕ)
    (ω : TaoPrimeTuple) :
    taoPrimeTupleCharacterObservable χ m' ω =
      χ (m' : ZMod q) *
        ∏ j, taoPrimeCoordinateCharacterObservable χ j (ω j) := by
  classical
  simp only [taoPrimeTupleCharacterObservable, taoPrimeTupleStart,
    taoPrimeTupleTailProduct, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow,
    taoPrimeCoordinateCharacterObservable]
  have hprod :
      (∏ j : Fin 1001,
          if j = 0 then χ (ω j : ZMod q) ^ (2 : ℕ)
          else χ (ω j : ZMod q)) =
        χ (ω 0 : ZMod q) ^ (2 : ℕ) *
          ∏ j ∈ Finset.univ.erase (0 : Fin 1001), χ (ω j : ZMod q) := by
    have herase :
        (∏ j ∈ Finset.univ.erase (0 : Fin 1001),
            if j = 0 then χ (ω j : ZMod q) ^ (2 : ℕ)
            else χ (ω j : ZMod q)) =
          ∏ j ∈ Finset.univ.erase (0 : Fin 1001), χ (ω j : ZMod q) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [← Finset.prod_erase_mul (s := Finset.univ)
      (f := fun j : Fin 1001 =>
        if j = 0 then χ (ω j : ZMod q) ^ (2 : ℕ)
        else χ (ω j : ZMod q)) (Finset.mem_univ (0 : Fin 1001))]
    simp only [if_pos]
    rw [herase]
    ring
  rw [hprod]
  rw [Nat.cast_prod, map_prod]
  ring

theorem integrable_taoPrimeTupleCharacterObservable
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) :
    Integrable (taoPrimeTupleCharacterObservable χ m')
      (taoPrimeTupleMeasure P hP) := by
  apply Integrable.of_bound
    ((measurable_of_countable _).aestronglyMeasurable) 1
  filter_upwards [] with ω
  exact χ.norm_le_one _

/-- Every full tuple-character expectation has norm at most one.  This direct
integral bound is especially useful for the principal character: it keeps its
single main-term contribution separate from the 1000-coordinate AM--GM step. -/
theorem norm_taoPrimeTupleCharacterExpectation_le_one
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) :
    ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ ≤ 1 := by
  unfold taoPrimeTupleCharacterExpectation
  calc
    ‖∫ ω, taoPrimeTupleCharacterObservable χ m' ω
        ∂taoPrimeTupleMeasure P hP‖ ≤
        1 * (taoPrimeTupleMeasure P hP).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with ω
      exact χ.norm_le_one _
    _ = 1 := by simp

/-- Independence factors the full character expectation exactly into the
distinguished square-coordinate expectation and the other 1000 coordinate
expectations. -/
theorem taoPrimeTupleCharacterExpectation_eq_coordinateProduct
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) :
    taoPrimeTupleCharacterExpectation P hP χ m' =
      χ (m' : ZMod q) *
        ∏ j, taoPrimeCoordinateCharacterExpectation P hP χ j := by
  unfold taoPrimeTupleCharacterExpectation
  calc
    (∫ ω, taoPrimeTupleCharacterObservable χ m' ω
        ∂taoPrimeTupleMeasure P hP) =
        ∫ ω, χ (m' : ZMod q) *
          ∏ j, taoPrimeCoordinateCharacterObservable χ j (ω j)
          ∂taoPrimeTupleMeasure P hP := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        taoPrimeTupleCharacterObservable_eq_coordinateProduct χ m' ω
    _ = χ (m' : ZMod q) *
        ∫ ω, ∏ j, taoPrimeCoordinateCharacterObservable χ j (ω j)
          ∂taoPrimeTupleMeasure P hP := by
      rw [integral_const_mul]
    _ = χ (m' : ZMod q) *
        ∏ j, ∫ ω, taoPrimeCoordinateCharacterObservable χ j (ω j)
          ∂taoPrimeTupleMeasure P hP := by
      rw [(iIndepFun_taoPrimeTuple P hP).integral_fun_prod_comp
        (fun j => (measurable_pi_apply j).aemeasurable)
        (fun j => (measurable_of_countable
          (taoPrimeCoordinateCharacterObservable χ j)).aestronglyMeasurable)]
    _ = χ (m' : ZMod q) *
        ∏ j, taoPrimeCoordinateCharacterExpectation P hP χ j := rfl

/-- The normalized character average over one finite dyadic prime band.  At
`j = 0` this averages the squared character value; at all other coordinates
it is the ordinary prime character average. -/
def taoDyadicPrimeCoordinateCharacterAverage
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : Fin 1001) (P : ℕ) : ℂ :=
  ((taoDyadicPrimeBand P).card : ℂ)⁻¹ *
    ∑ p ∈ taoDyadicPrimeBand P,
      taoPrimeCoordinateCharacterObservable χ j p

/-- A coordinate expectation under the product model is exactly the
normalized finite character average over its prescribed dyadic prime band. -/
theorem taoPrimeCoordinateCharacterExpectation_eq_dyadicAverage
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (j : Fin 1001) :
    taoPrimeCoordinateCharacterExpectation P hP χ j =
      taoDyadicPrimeCoordinateCharacterAverage χ j (P j) := by
  let f : ℕ → ℂ := taoPrimeCoordinateCharacterObservable χ j
  let ρ : PMF ℕ :=
    PMF.uniformOfFinset (taoDyadicPrimeBand (P j)) (hP j)
  have hf : Integrable f ρ.toMeasure := by
    apply Integrable.of_bound
      ((measurable_of_countable f).aestronglyMeasurable) 1
    filter_upwards [] with p
    unfold f taoPrimeCoordinateCharacterObservable
    split_ifs
    · simpa only [norm_pow] using
        pow_le_one₀ (norm_nonneg (χ (p : ZMod q))) (χ.norm_le_one _)
    · exact χ.norm_le_one _
  unfold taoPrimeCoordinateCharacterExpectation
  rw [← integral_map (μ := taoPrimeTupleMeasure P hP)
    (φ := fun ω : TaoPrimeTuple => ω j)
    (measurable_pi_apply j).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [map_eval_taoPrimeTupleMeasure]
  change (∫ p, f p ∂ρ.toMeasure) = _
  rw [PMF.integral_eq_tsum ρ f hf]
  rw [tsum_eq_sum (s := taoDyadicPrimeBand (P j)) (fun p hp => by
    unfold ρ
    rw [PMF.uniformOfFinset_apply_of_notMem (hP j) hp]
    simp)]
  have hsum :
      (∑ p ∈ taoDyadicPrimeBand (P j), (ρ p).toReal • f p) =
        ∑ p ∈ taoDyadicPrimeBand (P j),
          (((taoDyadicPrimeBand (P j)).card : ENNReal)⁻¹).toReal • f p := by
    apply Finset.sum_congr rfl
    intro p hp
    unfold ρ
    rw [PMF.uniformOfFinset_apply_of_mem (hP j) hp]
  rw [hsum, ← Finset.smul_sum]
  unfold taoDyadicPrimeCoordinateCharacterAverage
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  have hcast :
      (((((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ : ℝ) : ℂ)) =
        ((taoDyadicPrimeBand (P j)).card : ℂ)⁻¹ := by
    simp
  rw [hcast]

/-- The ordinary normalized Dirichlet-character average over the primes in
`[P,2P)`, corresponding to every non-distinguished tuple coordinate. -/
def taoDyadicPrimeCharacterAverage
    {q : ℕ} (χ : DirichletCharacter ℂ q) (P : ℕ) : ℂ :=
  ((taoDyadicPrimeBand P).card : ℂ)⁻¹ *
    ∑ p ∈ taoDyadicPrimeBand P, χ (p : ZMod q)

theorem taoDyadicPrimeCoordinateCharacterAverage_eq_characterAverage
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : Fin 1001) (P : ℕ)
    (hj : j ≠ 0) :
    taoDyadicPrimeCoordinateCharacterAverage χ j P =
      taoDyadicPrimeCharacterAverage χ P := by
  simp [taoDyadicPrimeCoordinateCharacterAverage,
    taoDyadicPrimeCharacterAverage, taoPrimeCoordinateCharacterObservable,
    hj]

/-- Every coordinate character expectation has modulus at most one.  This
discards the distinguished squared coordinate in the source argument. -/
theorem norm_taoPrimeCoordinateCharacterExpectation_le_one
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (j : Fin 1001) :
    ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖ ≤ 1 := by
  unfold taoPrimeCoordinateCharacterExpectation
  calc
    ‖∫ ω, taoPrimeCoordinateCharacterObservable χ j (ω j)
        ∂taoPrimeTupleMeasure P hP‖ ≤
        1 * (taoPrimeTupleMeasure P hP).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with ω
      unfold taoPrimeCoordinateCharacterObservable
      split_ifs
      · simpa only [norm_pow] using
          pow_le_one₀ (norm_nonneg (χ (ω j : ZMod q))) (χ.norm_le_one _)
      · exact χ.norm_le_one _
    _ = 1 := by simp

/-- After exact independence, the residual character and the distinguished
square-coordinate cost at most one; only the 1000 ordinary prime-character
averages remain. -/
theorem norm_taoPrimeTupleCharacterExpectation_le_tailCharacterAverages
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) :
    ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ ≤
      ∏ j ∈ Finset.univ.erase (0 : Fin 1001),
        ‖taoDyadicPrimeCharacterAverage χ (P j)‖ := by
  rw [taoPrimeTupleCharacterExpectation_eq_coordinateProduct]
  simp only [norm_mul, norm_prod]
  have htail_nonneg :
      0 ≤ ∏ j ∈ Finset.univ.erase (0 : Fin 1001),
        ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc
    ‖χ (m' : ZMod q)‖ *
        ∏ j, ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖ ≤
        ∏ j, ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (χ.norm_le_one (m' : ZMod q))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (∏ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖) *
        ‖taoPrimeCoordinateCharacterExpectation P hP χ 0‖ := by
      exact (Finset.prod_erase_mul Finset.univ
        (fun j : Fin 1001 =>
          ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖)
        (Finset.mem_univ (0 : Fin 1001))).symm
    _ ≤ ∏ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoPrimeCoordinateCharacterExpectation P hP χ j‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_taoPrimeCoordinateCharacterExpectation_le_one P hP χ 0)
        htail_nonneg
    _ = ∏ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [taoPrimeCoordinateCharacterExpectation_eq_dyadicAverage]
      rw [taoDyadicPrimeCoordinateCharacterAverage_eq_characterAverage]
      exact Finset.ne_of_mem_erase hj

/-- A finite nonempty product of nonnegative reals is bounded by the sum of
the corresponding `card`th powers.  This convenient weak AM--GM form has no
normalizing denominator, exactly as needed by the source's `≪` estimate. -/
theorem prod_le_sum_pow_card_of_nonempty
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ≤ ∑ i ∈ s, (f i) ^ s.card := by
  let t : Finset ℝ := s.image f
  have ht : t.Nonempty := hs.image f
  let M : ℝ := t.max' ht
  have hle : ∀ i ∈ s, f i ≤ M := by
    intro i hi
    exact Finset.le_max' t (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hprod : (∏ i ∈ s, f i) ≤ ∏ _i ∈ s, M :=
    Finset.prod_le_prod (fun i hi => hf i hi) hle
  have hMmem : M ∈ t := Finset.max'_mem t ht
  rcases Finset.mem_image.mp hMmem with ⟨i, hi, hfi⟩
  have hterm : M ^ s.card ≤ ∑ j ∈ s, (f j) ^ s.card := by
    rw [← hfi]
    exact Finset.single_le_sum
      (fun j hj => pow_nonneg (hf j hj) s.card) hi
  have hconst : (∏ _i ∈ s, M) = M ^ s.card := by simp
  rw [hconst] at hprod
  exact hprod.trans hterm

/-- The exact source reduction after independence and weak AM--GM: a full
tuple-character expectation is controlled by the sum of the 1000th powers
of the ordinary dyadic prime character averages. -/
theorem norm_taoPrimeTupleCharacterExpectation_le_sum_pow
    {q : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (χ : DirichletCharacter ℂ q) (m' : ℕ) :
    ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  let s : Finset (Fin 1001) := Finset.univ.erase 0
  have hs : s.Nonempty := by
    refine ⟨(1 : Fin 1001), ?_⟩
    simp [s]
  have hcard : s.card = 1000 := by
    simp [s]
  calc
    ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ ≤
        ∏ j ∈ s, ‖taoDyadicPrimeCharacterAverage χ (P j)‖ := by
      exact norm_taoPrimeTupleCharacterExpectation_le_tailCharacterAverages
        P hP χ m'
    _ ≤ ∑ j ∈ s,
        ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ s.card := by
      exact prod_le_sum_pow_card_of_nonempty s hs
        (fun j => ‖taoDyadicPrimeCharacterAverage χ (P j)‖)
        (fun _ _ => norm_nonneg _)
    _ = ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
      simp only [s, hcard]

/-- Pointwise character expansion of one primitive residue-class fiber. -/
theorem primitiveResidueFiber_indicator_eq_characterSum
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (m' : ℕ) (ω : TaoPrimeTuple) :
    ((if taoPrimeTupleStart m' ω ≡ a [MOD q] then 1 else 0 : ℝ) : ℂ) =
      (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterObservable χ m' ω := by
  simpa only [taoPrimeTupleCharacterObservable] using
    primitiveResidueIndicator_eq_dirichletCharacterAverage hq ha
      (b := taoPrimeTupleStart m' ω)

/-- Integrated character expansion of a primitive residue-class probability.
This is the exact finite identity preceding the source's triangle inequality. -/
theorem primitiveResidueFiber_probability_eq_characterExpectations
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (m' : ℕ) :
    (((taoPrimeTupleMeasure P hP).real
      {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} : ℝ) : ℂ) =
      (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterExpectation P hP χ m' := by
  let μ := taoPrimeTupleMeasure P hP
  let E : Set TaoPrimeTuple :=
    {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have hχint : ∀ χ : DirichletCharacter ℂ q,
      Integrable
        (fun ω => χ ((a : ZMod q)⁻¹) *
          taoPrimeTupleCharacterObservable χ m' ω) μ := by
    intro χ
    exact (integrable_taoPrimeTupleCharacterObservable P hP χ m').const_mul _
  calc
    (((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} : ℝ) : ℂ) =
        ∫ ω, (if taoPrimeTupleStart m' ω ≡ a [MOD q]
          then (1 : ℂ) else 0) ∂μ := by
      change ((μ.real E : ℝ) : ℂ) = _
      rw [show (fun ω : TaoPrimeTuple =>
          if taoPrimeTupleStart m' ω ≡ a [MOD q]
          then (1 : ℂ) else 0) = E.indicator (fun _ => (1 : ℂ)) by
        funext ω
        simp only [E, Set.indicator, Set.mem_setOf_eq]]
      rw [integral_indicator_const (1 : ℂ) hE]
      simp
    _ = ∫ ω, (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) *
              taoPrimeTupleCharacterObservable χ m' ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        by_cases hω : taoPrimeTupleStart m' ω ≡ a [MOD q]
        · simpa [hω] using
            primitiveResidueFiber_indicator_eq_characterSum hq ha m' ω
        · simpa [hω] using
            primitiveResidueFiber_indicator_eq_characterSum hq ha m' ω
    _ = (1 / (q.totient : ℂ)) *
        ∫ ω, ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterObservable χ m' ω ∂μ := by
      rw [integral_const_mul]
    _ = (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          ∫ ω, χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterObservable χ m' ω ∂μ := by
      congr 1
      exact integral_finsetSum Finset.univ fun χ _hχ => hχint χ
    _ = (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterExpectation P hP χ m' := by
      congr 1
      apply Finset.sum_congr rfl
      intro χ _hχ
      rw [integral_const_mul]
      rfl

/-- The source triangle-inequality consequence of the exact character
identity.  The phase contributed by the primitive residue has norm at most
one, so only the norms of the character expectations remain. -/
theorem primitiveResidueFiber_probability_le_characterExpectations
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (m' : ℕ) :
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} ≤
      ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ := by
  have hEq := primitiveResidueFiber_probability_eq_characterExpectations
    hq ha P hP m'
  have hprobNonneg : 0 ≤ (taoPrimeTupleMeasure P hP).real
      {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} :=
    MeasureTheory.measureReal_nonneg
  calc
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} =
        ‖(((taoPrimeTupleMeasure P hP).real
          {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprobNonneg]
    _ = ‖(1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterExpectation P hP χ m'‖ :=
      congrArg norm hEq
    _ = ‖(1 / (q.totient : ℂ))‖ *
        ‖∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterExpectation P hP χ m'‖ := norm_mul _ _
    _ ≤ ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖χ ((a : ZMod q)⁻¹) *
            taoPrimeTupleCharacterExpectation P hP χ m'‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro χ _hχ
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (χ.norm_le_one ((a : ZMod q)⁻¹))

/-- Primitive residue-fiber probability after the complete character,
independence, and weak AM--GM reductions.  The remaining analytic input is
precisely a bound for high moments of dyadic prime character averages. -/
theorem primitiveResidueFiber_probability_le_primeCharacterMoments
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (m' : ℕ) :
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} ≤
      ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  calc
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} ≤
        ‖(1 / (q.totient : ℂ))‖ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ :=
      primitiveResidueFiber_probability_le_characterExpectations
        hq ha P hP m'
    _ ≤ ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro χ _hχ
      exact norm_taoPrimeTupleCharacterExpectation_le_sum_pow P hP χ m'

/-- The lcm attached to every actual ordered 50-tuple in the small-prime
moment expansion is positive. -/
theorem taoSmallPrimeTupleModulus_pos_of_mem
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    0 < taoSmallPrimeTupleModulus t := by
  rw [Nat.pos_iff_ne_zero, taoSmallPrimeTupleModulus,
    Finset.lcm_ne_zero_iff]
  intro j _hj
  have htj := Fintype.mem_piFinset.mp ht j
  exact (mem_taoSmallAntiSieveIndices.mp htj).2.2.1.ne_zero

/-- An lcm of `k` primes is at most `2^k` times its Euler totient.  Repeated
primes only make this estimate stronger. -/
theorem finset_lcm_le_two_pow_card_mul_totient_of_prime
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Nat.Prime (f i)) :
    s.lcm f ≤ 2 ^ s.card * (s.lcm f).totient := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpa : Nat.Prime (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Nat.Prime (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hih := ih hfs
      rw [Finset.lcm_insert, Finset.card_insert_of_notMem ha]
      by_cases hd : f a ∣ s.lcm f
      · have hlcm : lcm (f a) (s.lcm f) = s.lcm f := by
          exact (lcm_eq_right_iff _ _ (by simp)).2 hd
        rw [hlcm]
        calc
          s.lcm f ≤ 2 ^ s.card * (s.lcm f).totient := hih
          _ ≤ 2 ^ (s.card + 1) * (s.lcm f).totient := by
            apply Nat.mul_le_mul_right
            exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ s.card)
      · have hcop : Nat.Coprime (f a) (s.lcm f) :=
          hpa.coprime_iff_not_dvd.mpr hd
        have hlcm : lcm (f a) (s.lcm f) = f a * s.lcm f := by
          change Nat.lcm (f a) (s.lcm f) = f a * s.lcm f
          exact hcop.lcm_eq_mul
        rw [hlcm, Nat.totient_mul hcop,
          Nat.totient_prime hpa]
        have hpTwo : 2 ≤ f a := hpa.two_le
        have hpBound : f a ≤ 2 * (f a - 1) := by
          omega
        calc
          f a * s.lcm f ≤
              (2 * (f a - 1)) *
                (2 ^ s.card * (s.lcm f).totient) :=
            Nat.mul_le_mul hpBound hih
          _ = 2 ^ (s.card + 1) *
              ((f a - 1) * (s.lcm f).totient) := by ring

/-- Explicit source coefficient comparison for a modulus formed from the
ordered 50-tuple of selected small primes. -/
theorem taoSmallPrimeTupleModulus_le_two_pow_fifty_mul_totient
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    taoSmallPrimeTupleModulus t ≤
      2 ^ (50 : ℕ) * (taoSmallPrimeTupleModulus t).totient := by
  unfold taoSmallPrimeTupleModulus
  simpa using finset_lcm_le_two_pow_card_mul_totient_of_prime
    (Finset.univ : Finset (Fin 50)) (fun j => (t j).2)
    (fun j _hj =>
      (mem_taoSmallAntiSieveIndices.mp
        (Fintype.mem_piFinset.mp ht j)).2.2.1)

/-- Real-valued form of the source's `1/φ(q) ≪ 1/q` replacement, with the
explicit absolute constant `2^50` for a 50-prime tuple modulus. -/
theorem norm_one_div_taoSmallPrimeTupleTotient_le
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    ‖(1 / ((taoSmallPrimeTupleModulus t).totient : ℂ))‖ ≤
      (2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t := by
  have hq : 0 < taoSmallPrimeTupleModulus t :=
    taoSmallPrimeTupleModulus_pos_of_mem ht
  have hφ : 0 < (taoSmallPrimeTupleModulus t).totient :=
    Nat.totient_pos.mpr hq
  rw [norm_div, norm_one]
  simp only [norm_natCast]
  rw [div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)]
  have hcast : (taoSmallPrimeTupleModulus t : ℝ) ≤
      (2 ^ (50 : ℕ) : ℝ) *
        ((taoSmallPrimeTupleModulus t).totient : ℝ) := by
    exact_mod_cast taoSmallPrimeTupleModulus_le_two_pow_fifty_mul_totient ht
  simpa only [one_mul] using hcast

/-- The complete character-moment estimate for one ordered 50-tuple from the
small-prime expansion, including the impossible-event branch. -/
theorem taoSmallPrimeJointDivisibilityProbability_le_primeCharacterMoments
    {x H : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (taoPrimeTupleMeasure P hP).real
        {ω | TaoSmallPrimeJointDivisibilityEvent m' t ω} ≤
      ‖(1 / ((taoSmallPrimeTupleModulus t).totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  rcases taoSmallPrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
      m' ht with hEmpty | ⟨a, ha, hFiber⟩
  · rw [hEmpty]
    simp only [measureReal_empty]
    positivity
  · rw [hFiber]
    exact primitiveResidueFiber_probability_le_primeCharacterMoments
      (taoSmallPrimeTupleModulus_pos_of_mem ht) ha P hP m'

/-- Source-facing form of the tuple probability estimate, with the totient
denominator replaced by the explicit `2^50/q` lcm weight. -/
theorem taoSmallPrimeJointDivisibilityProbability_le_modulusCharacterMoments
    {x H : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (taoPrimeTupleMeasure P hP).real
        {ω | TaoSmallPrimeJointDivisibilityEvent m' t ω} ≤
      ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  calc
    (taoPrimeTupleMeasure P hP).real
        {ω | TaoSmallPrimeJointDivisibilityEvent m' t ω} ≤
        ‖(1 / ((taoSmallPrimeTupleModulus t).totient : ℂ))‖ *
          ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) :=
      taoSmallPrimeJointDivisibilityProbability_le_primeCharacterMoments
        P hP m' ht
    _ ≤ ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
        (norm_one_div_taoSmallPrimeTupleTotient_le ht)
      exact Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

/-- The literal fiftieth moment is bounded by the corresponding finite sum of
all-character 1000th moments, tuple by tuple.  No analytic character-sum
estimate is assumed here; this exposes exactly the remaining Lemma 5.1 input. -/
theorem taoSmallPrimeFiftiethMoment_le_sum_primeCharacterMoments
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoSmallPrimeFiftiethMoment P hP x H m' ≤
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          (‖(1 / ((taoSmallPrimeTupleModulus t).totient : ℂ))‖ *
            ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
              ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^
                  (1000 : ℕ)) := by
  rw [taoSmallPrimeFiftiethMoment_eq_sum_jointProbabilities]
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left
    (taoSmallPrimeJointDivisibilityProbability_le_primeCharacterMoments
      P hP m' ht)
  apply Finset.prod_nonneg
  intro j _hj
  have htj := Fintype.mem_piFinset.mp ht j
  have hp : Nat.Prime (t j).2 :=
    (mem_taoSmallAntiSieveIndices.mp htj).2.2.1
  exact Real.log_nonneg (by exact_mod_cast hp.one_le)

/-- Source-facing fiftieth-moment reduction with the tuple lcm in the
denominator and the explicit harmless constant `2^50`. -/
theorem taoSmallPrimeFiftiethMoment_le_sum_modulusCharacterMoments
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoSmallPrimeFiftiethMoment P hP x H m' ≤
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
            ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
              ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^
                  (1000 : ℕ)) := by
  rw [taoSmallPrimeFiftiethMoment_eq_sum_jointProbabilities]
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left
    (taoSmallPrimeJointDivisibilityProbability_le_modulusCharacterMoments
      P hP m' ht)
  apply Finset.prod_nonneg
  intro j _hj
  have htj := Fintype.mem_piFinset.mp ht j
  have hp : Nat.Prime (t j).2 :=
    (mem_taoSmallAntiSieveIndices.mp htj).2.2.1
  exact Real.log_nonneg (by exact_mod_cast hp.one_le)

/-- The remaining character-moment sum at one of the 1000 ordinary prime
coordinates. -/
def taoSmallPrimeCharacterMomentAtCoordinate
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) : ℝ :=
  ∑ t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
    (∏ k, Real.log (t k).2) *
      (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ))

/-- Reorder the finite tuple, character, and coordinate sums in the exact
source reduction. -/
theorem taoSmallPrimeFiftiethMoment_le_sum_coordinateCharacterMoments
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoSmallPrimeFiftiethMoment P hP x H m' ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
  calc
    taoSmallPrimeFiftiethMoment P hP x H m' ≤
        ∑ t ∈ Fintype.piFinset
            (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
          (∏ j, Real.log (t j).2) *
            (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
              ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
                ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                  ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^
                    (1000 : ℕ)) :=
      taoSmallPrimeFiftiethMoment_le_sum_modulusCharacterMoments
        P hP x H m'
    _ = ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
      simp only [taoSmallPrimeCharacterMomentAtCoordinate,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]

/-- Exact finite pigeonhole step from the source: one of the 1000 ordinary
prime coordinates controls the full reordered character-moment sum, at the
explicit cost `1000`. -/
theorem exists_taoSmallPrimeFiftiethMoment_le_coordinateCharacterMoment
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
  let s : Finset (Fin 1001) := Finset.univ.erase 0
  let A : Fin 1001 → ℝ :=
    taoSmallPrimeCharacterMomentAtCoordinate P x H
  have hs : s.Nonempty := by
    refine ⟨(1 : Fin 1001), ?_⟩
    simp [s]
  let values : Finset ℝ := s.image A
  have hvalues : values.Nonempty := hs.image A
  let M : ℝ := values.max' hvalues
  have hMmem : M ∈ values := Finset.max'_mem values hvalues
  rcases Finset.mem_image.mp hMmem with ⟨j, hj, hAj⟩
  refine ⟨j, hj, ?_⟩
  have hle : ∀ k ∈ s, A k ≤ M := by
    intro k hk
    exact Finset.le_max' values (A k)
      (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  have hsum : (∑ k ∈ s, A k) ≤ s.card • M :=
    Finset.sum_le_card_nsmul s A M hle
  have hcard : s.card = 1000 := by simp [s]
  calc
    taoSmallPrimeFiftiethMoment P hP x H m' ≤ ∑ k ∈ s, A k :=
      taoSmallPrimeFiftiethMoment_le_sum_coordinateCharacterMoments
        P hP x H m'
    _ ≤ s.card • M := hsum
    _ = 1000 * taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
      simp only [hcard, nsmul_eq_mul, Nat.cast_ofNat]
      change 1000 * M = 1000 * A j
      rw [hAj]

end

end Tao2026

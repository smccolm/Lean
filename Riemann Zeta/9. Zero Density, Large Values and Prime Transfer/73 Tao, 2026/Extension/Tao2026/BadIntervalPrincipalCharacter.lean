import Tao2026.PrimeCharacterSums
import Tao2026.BadIntervalLargePrimeCharacter

/-!
# Principal-character separation for the large-prime probabilities

The complete character expansion contains one principal character and many
nonprincipal characters.  Applying the 1000-coordinate weak AM--GM estimate
to the principal character would charge the main term 1000 times.  This file
separates that character first, bounds its full tuple expectation directly by
one, and applies AM--GM only to the nonprincipal remainder.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

/-- A primitive residue fiber has one principal main term plus a
nonprincipal-character error.  In particular, the main term is charged once,
not once for each of the 1000 ordinary prime coordinates. -/
theorem primitiveResidueFiber_probability_le_principal_add_nonprincipalMoments
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (m' : ℕ) :
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} ≤
      ‖(1 / (q.totient : ℂ))‖ *
        (1 + ∑ χ ∈ taoNonprincipalCharacters q,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  calc
    (taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} ≤
      ‖(1 / (q.totient : ℂ))‖ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖taoPrimeTupleCharacterExpectation P hP χ m'‖ :=
      primitiveResidueFiber_probability_le_characterExpectations
        hq ha P hP m'
    _ = ‖(1 / (q.totient : ℂ))‖ *
        (‖taoPrimeTupleCharacterExpectation P hP
            (1 : DirichletCharacter ℂ q) m'‖ +
          ∑ χ ∈ taoNonprincipalCharacters q,
            ‖taoPrimeTupleCharacterExpectation P hP χ m'‖) := by
      congr 1
      unfold taoNonprincipalCharacters
      rw [← Finset.sum_erase_add _ _
        (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
      ac_rfl
    _ ≤ ‖(1 / (q.totient : ℂ))‖ *
        (1 + ∑ χ ∈ taoNonprincipalCharacters q,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply add_le_add
      · exact norm_taoPrimeTupleCharacterExpectation_le_one P hP 1 m'
      · apply Finset.sum_le_sum
        intro χ _hχ
        exact norm_taoPrimeTupleCharacterExpectation_le_sum_pow P hP χ m'

/-- Proposition 6.7 precursor with the principal character isolated before
the high-moment estimate. -/
theorem taoLargePrimeProbability_le_principal_add_nonprincipalMoments
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1) :
    taoLargePrimeProbability P hP m' a ≤
      ‖(1 / (a.2.totient : ℂ))‖ *
        (1 + ∑ χ ∈ taoNonprincipalCharacters a.2,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  rcases taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
      (m' := m') (a := a) hp hpl with hEmpty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeProbability, hEmpty, MeasureTheory.measureReal_empty]
    exact mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one
      (Finset.sum_nonneg fun χ _ => Finset.sum_nonneg fun j _ =>
        pow_nonneg (norm_nonneg _) _))
  · rw [taoLargePrimeProbability, hset]
    exact primitiveResidueFiber_probability_le_principal_add_nonprincipalMoments
      hp.pos hr P hP m'

/-- Proposition 6.8 precursor for distinct prime moduli, again with exactly
one principal main term modulo the product. -/
theorem taoLargePrimeJointProbability_le_principal_add_nonprincipalMoments
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1) :
    taoLargePrimeJointProbability P hP m' a b ≤
      ‖(1 / ((a.2 * b.2).totient : ℂ))‖ *
        (1 + ∑ χ ∈ taoNonprincipalCharacters (a.2 * b.2),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  rcases taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
      (m' := m') (a := a) (b := b) hp hq hpq hpa hqb with
    hEmpty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeJointProbability, hEmpty,
      MeasureTheory.measureReal_empty]
    exact mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one
      (Finset.sum_nonneg fun χ _ => Finset.sum_nonneg fun j _ =>
        pow_nonneg (norm_nonneg _) _))
  · rw [taoLargePrimeJointProbability, hset]
    exact primitiveResidueFiber_probability_le_principal_add_nonprincipalMoments
      (Nat.mul_pos hp.pos hq.pos) hr P hP m'

/-- The principal character is the coprimality indicator on natural
residues. -/
theorem principalDirichletCharacter_apply_natCast (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      if Nat.Coprime n q then 1 else 0 := by
  by_cases h : Nat.Coprime n q
  · simp [h, MulChar.one_apply, (ZMod.isUnit_iff_coprime n q).mpr h]
  · have hn : ¬ IsUnit (n : ZMod q) := by
      simpa only [ZMod.isUnit_iff_coprime] using h
    rw [if_neg h]
    exact MulCharClass.map_nonunit (1 : DirichletCharacter ℂ q) hn

/-- Exact real mass of one coordinate atom under its uniform dyadic-prime
law. -/
theorem taoPrimeTupleMeasure_eval_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) (p : ℕ) :
    (taoPrimeTupleMeasure P hP).real {ω | ω j = p} =
      if p ∈ taoDyadicPrimeBand (P j) then
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ else 0 := by
  have h := taoPrimeTupleMeasure_eval_mem P hP j ({p} : Set ℕ)
    ((Set.to_countable ({p} : Set ℕ)).measurableSet)
  have hset : {ω : TaoPrimeTuple | ω j ∈ ({p} : Set ℕ)} =
      {ω | ω j = p} := by
    ext ω
    simp
  rw [hset] at h
  rw [Measure.real, h]
  by_cases hp : p ∈ taoDyadicPrimeBand (P j)
  · rw [if_pos hp]
    simp only [Set.mem_singleton_iff]
    have hfilter :
        (taoDyadicPrimeBand (P j)).filter (fun x => x = p) = {p} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hx => hx.2
      · intro hx
        subst x
        exact ⟨hp, rfl⟩
    rw [hfilter]
    simp
  · rw [if_neg hp]
    simp [hp]

/-- A fixed prime can occupy at most one point of a dyadic prime band, so the
probability that it divides one sampled coordinate is at most one atom. -/
theorem taoPrimeTupleMeasure_eval_prime_dvd_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) {p : ℕ} (hp : Nat.Prime p) :
    (taoPrimeTupleMeasure P hP).real {ω | p ∣ ω j} ≤
      ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
  have h := taoPrimeTupleMeasure_eval_mem P hP j {n : ℕ | p ∣ n}
    ((Set.to_countable {n : ℕ | p ∣ n}).measurableSet)
  have hset : {ω : TaoPrimeTuple | ω j ∈ {n : ℕ | p ∣ n}} =
      {ω | p ∣ ω j} := rfl
  rw [hset] at h
  rw [Measure.real, h, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  have hcard :
      ((taoDyadicPrimeBand (P j)).filter
        (fun n => n ∈ {n : ℕ | p ∣ n})).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have haData := Finset.mem_filter.mp ha
    have hbData := Finset.mem_filter.mp hb
    have haPrime := (mem_taoDyadicPrimeBand.mp haData.1).1
    have hbPrime := (mem_taoDyadicPrimeBand.mp hbData.1).1
    have hpa : p = a := (Nat.prime_dvd_prime_iff_eq hp haPrime).mp haData.2
    have hpb : p = b := (Nat.prime_dvd_prime_iff_eq hp hbPrime).mp hbData.2
    exact hpa.symm.trans hpb
  have hcardReal :
      (((taoDyadicPrimeBand (P j)).filter
        (fun n => n ∈ {n : ℕ | p ∣ n})).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  have hdenom : 0 < ((taoDyadicPrimeBand (P j)).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (hP j))
  rw [div_eq_mul_inv]
  convert mul_le_mul_of_nonneg_right hcardReal (inv_nonneg.mpr hdenom.le) using 1 <;>
    simp

/-- Collision event for a fixed prime: it divides at least one of the 1001
sampled coordinates. -/
def TaoPrimeTuplePrimeCollision (p : ℕ) (w : TaoPrimeTuple) : Prop :=
  ∃ j : Fin 1001, p ∣ w j

/-- Union bound for all coordinate collisions with a fixed prime. -/
theorem taoPrimeTuplePrimeCollision_probability_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {p : ℕ} (hp : Nat.Prime p) :
    (taoPrimeTupleMeasure P hP).real
        {w | TaoPrimeTuplePrimeCollision p w} ≤
      ∑ j : Fin 1001, ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
  have hset : {w : TaoPrimeTuple | TaoPrimeTuplePrimeCollision p w} =
      ⋃ j ∈ (Finset.univ : Finset (Fin 1001)), {w | p ∣ w j} := by
    ext w
    simp [TaoPrimeTuplePrimeCollision]
  rw [hset]
  calc
    (taoPrimeTupleMeasure P hP).real
        (⋃ j ∈ (Finset.univ : Finset (Fin 1001)), {w | p ∣ w j}) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin 1001)),
        (taoPrimeTupleMeasure P hP).real {w | p ∣ w j} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin 1001)),
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _hj
      exact taoPrimeTupleMeasure_eval_prime_dvd_le P hP j hp
    _ = ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by simp

/-- If the residual factor is coprime to a prime, failure of coprimality for
the full tuple product forces a coordinate collision with that prime. -/
theorem not_coprime_taoPrimeTupleStart_subset_primeCollision
    {p m' : ℕ} (hp : Nat.Prime p) (hm : Nat.Coprime m' p) :
    {w : TaoPrimeTuple | ¬ Nat.Coprime (taoPrimeTupleStart m' w) p} ⊆
      {w | TaoPrimeTuplePrimeCollision p w} := by
  intro w hw
  have hdiv : p ∣ taoPrimeTupleStart m' w := by
    by_contra hnot
    exact hw ((hp.coprime_iff_not_dvd.mpr hnot).symm)
  unfold taoPrimeTupleStart at hdiv
  rcases hp.dvd_mul.mp hdiv with hleft | hmdiv
  · rcases hp.dvd_mul.mp hleft with hzero | htail
    · exact ⟨0, hp.dvd_of_dvd_pow hzero⟩
    · rcases (Prime.dvd_finsetProd_iff hp.prime
        (fun j : Fin 1001 => w j)).mp htail with ⟨j, _hj, hdj⟩
      exact ⟨j, hdj⟩
  · exact False.elim ((hp.coprime_iff_not_dvd.mp hm.symm) hmdiv)

/-- Event on which the full tuple product is coprime to a modulus. -/
def TaoPrimeTupleCoprimeEvent (q m' : ℕ) : Set TaoPrimeTuple :=
  {w | Nat.Coprime (taoPrimeTupleStart m' w) q}

/-- The full principal-character expectation is exactly the probability of
coprimality of the tuple product with the modulus. -/
theorem taoPrimeTuplePrincipalCharacterExpectation_eq_coprimeProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (q m' : ℕ) :
    taoPrimeTupleCharacterExpectation P hP
        (1 : DirichletCharacter ℂ q) m' =
      (((taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent q m') : ℝ) : ℂ) := by
  let μ := taoPrimeTupleMeasure P hP
  have hE : MeasurableSet (TaoPrimeTupleCoprimeEvent q m') :=
    (Set.to_countable _).measurableSet
  unfold taoPrimeTupleCharacterExpectation
  calc
    (∫ w, taoPrimeTupleCharacterObservable
        (1 : DirichletCharacter ℂ q) m' w ∂μ) =
        ∫ w, (TaoPrimeTupleCoprimeEvent q m').indicator
          (fun _ => (1 : ℂ)) w ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [show taoPrimeTupleCharacterObservable
          (1 : DirichletCharacter ℂ q) m' w =
          if Nat.Coprime (taoPrimeTupleStart m' w) q then 1 else 0 by
        exact principalDirichletCharacter_apply_natCast q
          (taoPrimeTupleStart m' w)]
      simp only [TaoPrimeTupleCoprimeEvent, Set.indicator,
        Set.mem_setOf_eq]
    _ = (((taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent q m') : ℝ) : ℂ) := by
      rw [integral_indicator_const (1 : ℂ) hE]
      simp [μ]

/-- Quantitative principal-character collision loss for one prime modulus. -/
theorem taoPrimeTuplePrincipalCoprimeDeficit_le_primeCollision
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {p m' : ℕ} (hp : Nat.Prime p) (hm : Nat.Coprime m' p) :
    1 - (taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent p m') ≤
      ∑ j : Fin 1001, ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
  have hE : MeasurableSet (TaoPrimeTupleCoprimeEvent p m') :=
    (Set.to_countable _).measurableSet
  have hcompl : (TaoPrimeTupleCoprimeEvent p m')ᶜ =
      {w : TaoPrimeTuple |
        ¬ Nat.Coprime (taoPrimeTupleStart m' w) p} := by
    ext w
    simp [TaoPrimeTupleCoprimeEvent]
  have hmeasureCompl := measureReal_compl
    (μ := taoPrimeTupleMeasure P hP) hE
  rw [hcompl] at hmeasureCompl
  have hmono :
      (taoPrimeTupleMeasure P hP).real
          {w : TaoPrimeTuple |
            ¬ Nat.Coprime (taoPrimeTupleStart m' w) p} ≤
        (taoPrimeTupleMeasure P hP).real
          {w | TaoPrimeTuplePrimeCollision p w} :=
    measureReal_mono
      (not_coprime_taoPrimeTupleStart_subset_primeCollision hp hm)
  calc
    1 - (taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent p m') =
        (taoPrimeTupleMeasure P hP).real
          {w : TaoPrimeTuple |
            ¬ Nat.Coprime (taoPrimeTupleStart m' w) p} := by
      simpa using hmeasureCompl.symm
    _ ≤ (taoPrimeTupleMeasure P hP).real
        {w | TaoPrimeTuplePrimeCollision p w} := hmono
    _ ≤ ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ :=
      taoPrimeTuplePrimeCollision_probability_le P hP hp

/-- For a product of two prime moduli, failure of coprimality forces a
collision with at least one of the two primes. -/
theorem not_coprime_taoPrimeTupleStart_mul_subset_primeCollision_union
    {p q m' : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hm : Nat.Coprime m' (p * q)) :
    {w : TaoPrimeTuple |
        ¬ Nat.Coprime (taoPrimeTupleStart m' w) (p * q)} ⊆
      {w | TaoPrimeTuplePrimeCollision p w} ∪
        {w | TaoPrimeTuplePrimeCollision q w} := by
  intro w hw
  have hmFactors : Nat.Coprime m' p ∧ Nat.Coprime m' q :=
    Nat.coprime_mul_iff_right.mp hm
  have hwFactors :
      ¬ Nat.Coprime (taoPrimeTupleStart m' w) p ∨
        ¬ Nat.Coprime (taoPrimeTupleStart m' w) q := by
    exact not_and_or.mp (fun h => hw (Nat.coprime_mul_iff_right.mpr h))
  rcases hwFactors with hwp | hwq
  · left
    exact not_coprime_taoPrimeTupleStart_subset_primeCollision
      hp hmFactors.1 hwp
  · right
    exact not_coprime_taoPrimeTupleStart_subset_primeCollision
      hq hmFactors.2 hwq

/-- Union bound for collisions with either of two fixed primes. -/
theorem taoPrimeTuplePrimeCollision_union_probability_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (taoPrimeTupleMeasure P hP).real
        ({w | TaoPrimeTuplePrimeCollision p w} ∪
          {w | TaoPrimeTuplePrimeCollision q w}) ≤
      2 * ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
  let S : ℝ := ∑ j : Fin 1001,
    ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹
  calc
    (taoPrimeTupleMeasure P hP).real
        ({w | TaoPrimeTuplePrimeCollision p w} ∪
          {w | TaoPrimeTuplePrimeCollision q w}) ≤
      (taoPrimeTupleMeasure P hP).real
          {w | TaoPrimeTuplePrimeCollision p w} +
        (taoPrimeTupleMeasure P hP).real
          {w | TaoPrimeTuplePrimeCollision q w} :=
      measureReal_union_le _ _
    _ ≤ S + S := add_le_add
      (taoPrimeTuplePrimeCollision_probability_le P hP hp)
      (taoPrimeTuplePrimeCollision_probability_le P hP hq)
    _ = 2 * ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
      dsimp [S]
      ring

/-- Quantitative principal-character collision loss for the product of two
prime moduli. -/
theorem taoPrimeTuplePrincipalCoprimeDeficit_mul_le_primeCollisions
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {p q m' : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hm : Nat.Coprime m' (p * q)) :
    1 - (taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent (p * q) m') ≤
      2 * ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
  have hE : MeasurableSet (TaoPrimeTupleCoprimeEvent (p * q) m') :=
    (Set.to_countable _).measurableSet
  have hcompl : (TaoPrimeTupleCoprimeEvent (p * q) m')ᶜ =
      {w : TaoPrimeTuple |
        ¬ Nat.Coprime (taoPrimeTupleStart m' w) (p * q)} := by
    ext w
    simp [TaoPrimeTupleCoprimeEvent]
  have hmeasureCompl := measureReal_compl
    (μ := taoPrimeTupleMeasure P hP) hE
  rw [hcompl] at hmeasureCompl
  have hmono :
      (taoPrimeTupleMeasure P hP).real
          {w : TaoPrimeTuple |
            ¬ Nat.Coprime (taoPrimeTupleStart m' w) (p * q)} ≤
        (taoPrimeTupleMeasure P hP).real
          ({w | TaoPrimeTuplePrimeCollision p w} ∪
            {w | TaoPrimeTuplePrimeCollision q w}) :=
    measureReal_mono
      (not_coprime_taoPrimeTupleStart_mul_subset_primeCollision_union
        hp hq hm)
  calc
    1 - (taoPrimeTupleMeasure P hP).real
        (TaoPrimeTupleCoprimeEvent (p * q) m') =
        (taoPrimeTupleMeasure P hP).real
          {w : TaoPrimeTuple |
            ¬ Nat.Coprime (taoPrimeTupleStart m' w) (p * q)} := by
      simpa using hmeasureCompl.symm
    _ ≤ (taoPrimeTupleMeasure P hP).real
        ({w | TaoPrimeTuplePrimeCollision p w} ∪
          {w | TaoPrimeTuplePrimeCollision q w}) := hmono
    _ ≤ 2 * ∑ j : Fin 1001,
        ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ :=
      taoPrimeTuplePrimeCollision_union_probability_le P hP hp hq

/-- Exact primitive-fiber error decomposition around the principal main term.
Only the principal expectation deficit and nonprincipal high moments remain. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le
    {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q)
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) (m' : ℕ) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} : ℝ) : ℂ) -
        (1 / (q.totient : ℂ))‖ ≤
      ‖(1 / (q.totient : ℂ))‖ *
        (‖taoPrimeTupleCharacterExpectation P hP
            (1 : DirichletCharacter ℂ q) m' - 1‖ +
          ∑ χ ∈ taoNonprincipalCharacters q,
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  let c : ℂ := 1 / (q.totient : ℂ)
  let E : DirichletCharacter ℂ q → ℂ := fun χ =>
    taoPrimeTupleCharacterExpectation P hP χ m'
  let f : DirichletCharacter ℂ q → ℂ := fun χ =>
    χ ((a : ZMod q)⁻¹) * E χ
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).mpr ha
  have hphase :
      (1 : DirichletCharacter ℂ q) ((a : ZMod q)⁻¹) = 1 := by
    have haUnitInt : IsUnit ((a : ℤ) : ZMod q) := by
      simpa using haUnit
    have hinv : IsUnit (((a : ℤ) : ZMod q)⁻¹) :=
      ZMod.isUnit_inv haUnitInt
    exact MulChar.one_apply (by simpa using hinv)
  have hsplit :
      (∑ χ : DirichletCharacter ℂ q, f χ) =
        f 1 + ∑ χ ∈ taoNonprincipalCharacters q, f χ := by
    unfold taoNonprincipalCharacters
    rw [← Finset.sum_erase_add _ _
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
    ac_rfl
  have hEq := primitiveResidueFiber_probability_eq_characterExpectations
    hq ha P hP m'
  have hdiff :
      (((taoPrimeTupleMeasure P hP).real
          {ω | taoPrimeTupleStart m' ω ≡ a [MOD q]} : ℝ) : ℂ) - c =
        c * ((E 1 - 1) +
          ∑ χ ∈ taoNonprincipalCharacters q, f χ) := by
    change _ - c = _
    rw [hEq]
    change c * (∑ χ : DirichletCharacter ℂ q, f χ) - c = _
    rw [hsplit]
    simp only [f, hphase, one_mul]
    ring
  rw [hdiff, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  calc
    ‖(E 1 - 1) + (∑ χ ∈ taoNonprincipalCharacters q, f χ)‖ ≤
        ‖E 1 - 1‖ +
          ‖(∑ χ ∈ taoNonprincipalCharacters q, f χ)‖ :=
      norm_add_le _ _
    _ ≤ ‖E 1 - 1‖ +
        ∑ χ ∈ taoNonprincipalCharacters q, ‖f χ‖ := by
      exact add_le_add (le_refl _) (norm_sum_le _ _)
    _ ≤ ‖E 1 - 1‖ +
        ∑ χ ∈ taoNonprincipalCharacters q, ‖E χ‖ := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro χ _hχ
      simp only [f, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ ≤ ‖E 1 - 1‖ +
        ∑ χ ∈ taoNonprincipalCharacters q,
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro χ _hχ
      exact norm_taoPrimeTupleCharacterExpectation_le_sum_pow P hP χ m'

/-- Source-shaped deviation estimate for one prime modulus.  The first error
is the explicit coordinate-collision majorant; the second is purely
nonprincipal. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime
    {p a m' : ℕ} (hp : Nat.Prime p) (ha : Nat.Coprime a p)
    (hm : Nat.Coprime m' p) (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p]} : ℝ) : ℂ) -
        (1 / (p.totient : ℂ))‖ ≤
      ‖(1 / (p.totient : ℂ))‖ *
        ((∑ j : Fin 1001,
            ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
          ∑ χ ∈ taoNonprincipalCharacters p,
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  let r : ℝ := (taoPrimeTupleMeasure P hP).real
    (TaoPrimeTupleCoprimeEvent p m')
  have hrle : r ≤ 1 := measureReal_le_one
  have hprincipal :
      ‖taoPrimeTupleCharacterExpectation P hP
          (1 : DirichletCharacter ℂ p) m' - 1‖ ≤
        ∑ j : Fin 1001,
          ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
    rw [taoPrimeTuplePrincipalCharacterExpectation_eq_coprimeProbability]
    change ‖((r : ℝ) : ℂ) - 1‖ ≤ _
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos]
    · simpa [r] using
        taoPrimeTuplePrincipalCoprimeDeficit_le_primeCollision P hP hp hm
    · linarith
  calc
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p]} : ℝ) : ℂ) -
        (1 / (p.totient : ℂ))‖ ≤
      ‖(1 / (p.totient : ℂ))‖ *
        (‖taoPrimeTupleCharacterExpectation P hP
            (1 : DirichletCharacter ℂ p) m' - 1‖ +
          ∑ χ ∈ taoNonprincipalCharacters p,
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) :=
      primitiveResidueFiber_probability_sub_main_norm_le hp.pos ha P hP m'
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add hprincipal (le_refl _)

/-- Source-shaped deviation estimate for a product of two prime moduli. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_mul
    {p q a m' : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : Nat.Coprime a (p * q)) (hm : Nat.Coprime m' (p * q))
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        ((2 * ∑ j : Fin 1001,
            ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
          ∑ χ ∈ taoNonprincipalCharacters (p * q),
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) := by
  let r : ℝ := (taoPrimeTupleMeasure P hP).real
    (TaoPrimeTupleCoprimeEvent (p * q) m')
  have hrle : r ≤ 1 := measureReal_le_one
  have hprincipal :
      ‖taoPrimeTupleCharacterExpectation P hP
          (1 : DirichletCharacter ℂ (p * q)) m' - 1‖ ≤
        2 * ∑ j : Fin 1001,
          ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹ := by
    rw [taoPrimeTuplePrincipalCharacterExpectation_eq_coprimeProbability]
    change ‖((r : ℝ) : ℂ) - 1‖ ≤ _
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos]
    · simpa [r] using
        taoPrimeTuplePrincipalCoprimeDeficit_mul_le_primeCollisions
          P hP hp hq hm
    · linarith
  calc
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        (‖taoPrimeTupleCharacterExpectation P hP
            (1 : DirichletCharacter ℂ (p * q)) m' - 1‖ +
          ∑ χ ∈ taoNonprincipalCharacters (p * q),
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) :=
      primitiveResidueFiber_probability_sub_main_norm_le
        (Nat.mul_pos hp.pos hq.pos) ha P hP m'
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add hprincipal (le_refl _)

end

end Tao2026

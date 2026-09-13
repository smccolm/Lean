import Tao2026.ExceptionalCharacterAggregate
import Tao2026.SmallPrimeMertens

/-!
# Exceptional conductor union for the small-prime moment

This module identifies the finite union of all nontrivial divisor conductors
arising from the ordered small-prime tuple moduli. It proves squarefreeness
and the `cutoff^50` range bound, applies the aggregate Lemma 5.1 bridge, and
inserts the resulting single uniform moment bound into the literal weighted
exceptional conductor sum.
-/

namespace Tao2026

open Filter
open scoped Classical

theorem taoSmallPrimeTupleModulus_squarefree
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    Squarefree (taoSmallPrimeTupleModulus t) := by
  rw [taoSmallPrimeTupleModulus_eq_support_prod ht]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      (taoSmallPrimeTupleSupport_pairwise_coprime ht hp hq hpq)
  · intro p hp
    exact (taoSmallPrimeTupleSupport_prime_le ht hp).1.squarefree

theorem taoSmallPrimeTupleModulus_le_cutoff_pow_fifty
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    taoSmallPrimeTupleModulus t ≤ taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) := by
  rw [taoSmallPrimeTupleModulus_eq_support_prod ht]
  have hprod := Finset.prod_le_pow_card (taoSmallPrimeTupleSupport t) id
    (taoSmallAntiSievePrimeCutoff x)
    (fun p hp => (taoSmallPrimeTupleSupport_prime_le ht hp).2)
  have hcutoff : 1 ≤ taoSmallAntiSievePrimeCutoff x := by
    let k : Fin 50 := ⟨0, by norm_num⟩
    have hk := mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht k)
    exact (hk.2.2.1.one_le.trans hk.2.2.2.1)
  exact hprod.trans (Nat.pow_le_pow_right hcutoff
    (card_taoSmallPrimeTupleSupport_le_fifty t))

noncomputable def taoSmallPrimeExceptionalConductors (x H : ℕ) : Finset ℕ :=
  (Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)).biUnion
    fun t => (taoSmallPrimeTupleModulus t).divisors.erase 1

theorem mem_taoSmallPrimeExceptionalConductors {x H d : ℕ} :
    d ∈ taoSmallPrimeExceptionalConductors x H ↔
      ∃ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1 := by
  simp [taoSmallPrimeExceptionalConductors]

theorem taoSmallPrimeExceptionalConductors_squarefree
    {x H d : ℕ} (hd : d ∈ taoSmallPrimeExceptionalConductors x H) :
    Squarefree d := by
  obtain ⟨t, ht, hdt⟩ := mem_taoSmallPrimeExceptionalConductors.mp hd
  have hdiv := (Finset.mem_erase.mp hdt).2
  have hmodsq := taoSmallPrimeTupleModulus_squarefree ht
  exact Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hdiv) hmodsq

theorem taoSmallPrimeExceptionalConductors_le_cutoff_pow_fifty
    {x H d : ℕ} (hd : d ∈ taoSmallPrimeExceptionalConductors x H) :
    d ≤ taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) := by
  obtain ⟨t, ht, hdt⟩ := mem_taoSmallPrimeExceptionalConductors.mp hd
  have hdivMem := (Finset.mem_erase.mp hdt).2
  have hmodPos := taoSmallPrimeTupleModulus_pos_of_mem ht
  have hdmod : d ≤ taoSmallPrimeTupleModulus t :=
    Nat.le_of_dvd hmodPos (Nat.dvd_of_mem_divisors hdivMem)
  exact hdmod.trans (taoSmallPrimeTupleModulus_le_cutoff_pow_fifty ht)

/-- The fiftieth power of the small-prime cutoff is eventually already below
the lower distinguished-prime scale `⌊z^(9/10)⌋`. This is the numerical
exponent gap `50 / 100 < 9 / 10`, with both floors retained exactly. -/
theorem eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_lt_lowerScale :
    ∀ᶠ x : ℕ in atTop,
      taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) <
        taoZPowerFloor (9 / 10 : ℝ) x := by
  have hgap : ∀ᶠ x : ℕ in atTop,
      (2 : ℝ) ≤ (taoZ x) ^ (2 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_taoZ_atTop).eventually (eventually_ge_atTop 2)
  have hzOne := tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hgap, hzOne] with x hgapx hzx
  have hzpos : 0 < taoZ x := taoZ_pos x
  have hcut : (taoSmallAntiSievePrimeCutoff x : ℝ) ≤
      (taoZ x) ^ (1 / 100 : ℝ) := by
    exact Nat.floor_le (Real.rpow_nonneg hzpos.le _)
  have hcutPow : (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℝ) ≤
      (taoZ x) ^ (1 / 2 : ℝ) := by
    calc
      (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) =
          (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ ((taoZ x) ^ (1 / 100 : ℝ)) ^ (50 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hcut (by norm_num)
      _ = (taoZ x) ^ ((1 / 100 : ℝ) * 50) :=
        (Real.rpow_mul hzpos.le _ _).symm
      _ = (taoZ x) ^ (1 / 2 : ℝ) := by norm_num
  have hhalf : (taoZ x) ^ (1 / 2 : ℝ) ≤
      (taoZ x) ^ (9 / 10 : ℝ) / 2 := by
    have hm : 2 * (taoZ x) ^ (1 / 2 : ℝ) ≤
        (taoZ x) ^ (2 / 5 : ℝ) * (taoZ x) ^ (1 / 2 : ℝ) := by
      gcongr
    have heq : (taoZ x) ^ (2 / 5 : ℝ) * (taoZ x) ^ (1 / 2 : ℝ) =
        (taoZ x) ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hzpos]
      norm_num
    linarith
  have hfloor := Nat.div_two_lt_floor
    (Real.one_le_rpow hzx (by norm_num : (0 : ℝ) ≤ 9 / 10))
  change (taoZ x) ^ (9 / 10 : ℝ) / 2 <
    (taoZPowerFloor (9 / 10 : ℝ) x : ℝ) at hfloor
  exact_mod_cast hcutPow.trans_lt (hhalf.trans_lt hfloor)

theorem eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_lowerScale :
    ∀ᶠ x : ℕ in atTop,
      taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) ≤
        taoZPowerFloor (9 / 10 : ℝ) x := by
  filter_upwards [
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_lt_lowerScale] with x hx
  exact hx.le

/-- Any scale above the lower distinguished-prime cutoff eventually gives
enough room for every small-prime tuple conductor in the Burgess range. -/
theorem eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_burgessRange :
    ∀ᶠ x : ℕ in atTop, ∀ Z : ℕ,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ Z →
      (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent) := by
  filter_upwards [eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_lowerScale,
    (tendsto_taoZPowerFloor_atTop (by norm_num : (0 : ℝ) < 9 / 10)).eventually
      (eventually_ge_atTop 1)] with x hcut hfloor Z hZ
  have hcutZ : (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℝ) ≤ Z := by
    exact_mod_cast hcut.trans hZ
  have hZone : (1 : ℝ) ≤ Z := by exact_mod_cast hfloor.trans hZ
  calc
    (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℝ) ≤ Z := hcutZ
    _ = (Z : ℝ) ^ (1 : ℝ) := by simp
    _ ≤ (Z : ℝ) ^ (taoBurgessPeriodExponent * (1 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le hZone (by
        norm_num [taoBurgessPeriodExponent])
    _ = Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]

theorem isAdmissible_taoSmallPrimeExceptionalConductors
    {x H Z : ℕ}
    (hrange : (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    IsAdmissibleTaoExceptionalConductorSet
      (taoSmallPrimeExceptionalConductors x H) Z := by
  constructor
  · intro d hd
    exact taoSmallPrimeExceptionalConductors_squarefree hd
  · intro d hd
    calc
      (d : ℝ) ≤ (taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) : ℕ) := by
        exact_mod_cast taoSmallPrimeExceptionalConductors_le_cutoff_pow_fifty hd
      _ ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent) := by
        simpa only [Nat.cast_pow] using hrange

/-- Burgess-conditional uniform squared-moment bound for the union of every
conductor generated by the small-prime tuple expansion. -/
theorem exists_eventually_taoSmallPrimeExceptionalConductorMoment_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (x H : ℕ → ℕ)
    (hrange : ∀ᶠ Z : ℕ in atTop,
      (taoSmallAntiSievePrimeCutoff (x Z) ^ (50 : ℕ) : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      ∑ d ∈ taoSmallPrimeExceptionalConductors (x Z) (H Z),
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ K := by
  have hD : ∀ᶠ Z : ℕ in atTop,
      IsAdmissibleTaoExceptionalConductorSet
        (taoSmallPrimeExceptionalConductors (x Z) (H Z)) Z := by
    filter_upwards [hrange] with Z hZ
    exact isAdmissible_taoSmallPrimeExceptionalConductors hZ
  obtain ⟨K, hKpos, hcard, hmoment⟩ :=
    exists_eventually_conductorExceptional_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess (fun Z => taoSmallPrimeExceptionalConductors (x Z) (H Z)) hD
  exact ⟨K, hKpos, hmoment⟩

theorem sum_tupleDivisorExceptional_sq_le_conductorUnion
    {x H Z : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
      ∑ χ ∈ taoExceptionalPrimitiveCharacters d Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2) ≤
    ∑ d ∈ taoSmallPrimeExceptionalConductors x H,
      ∑ χ ∈ taoExceptionalPrimitiveCharacters d Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact mem_taoSmallPrimeExceptionalConductors.mpr ⟨t, ht, hd⟩
  · intro d hd hnot
    exact Finset.sum_nonneg fun χ hχ => sq_nonneg _

/-- Inserting one uniform union moment into the literal exceptional part of
the small-prime tuple sum leaves precisely the already-summed logarithmic lcm
coefficient. -/
theorem taoSmallPrimeExceptionalConductorSum_le_of_unionMoment
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) {K : ℝ}
    (hmoment :
      (∑ d ∈ taoSmallPrimeExceptionalConductors x H,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d (P j),
          ‖taoNormalizedPrimeCharacterSum χ (P j)‖ ^ 2) ≤ K) :
    taoSmallPrimeExceptionalConductorSum P x H j ≤
      (2 : ℝ) ^ (50 : ℕ) * K *
        ∑ t ∈ Fintype.piFinset
            (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
          (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t := by
  unfold taoSmallPrimeExceptionalConductorSum
  calc
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
      (∏ k, Real.log (t k).2) *
        (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
          ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
            ∑ ψ ∈ taoExceptionalPrimitiveCharacters d (P j),
              ‖taoNormalizedPrimeCharacterSum ψ (P j)‖ ^ (2 : ℕ))) ≤
      ∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
      (∏ k, Real.log (t k).2) *
        (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) * K) := by
      apply Finset.sum_le_sum
      intro t ht
      have hinner :=
        (sum_tupleDivisorExceptional_sq_le_conductorUnion
          (Z := P j) ht).trans hmoment
      have hlog : 0 ≤ ∏ k, Real.log (t k).2 := by
        exact Finset.prod_nonneg fun k hk =>
          Real.log_nonneg (by
            exact_mod_cast (mem_taoSmallAntiSieveIndices.mp
              (Fintype.mem_piFinset.mp ht k)).2.2.1.one_le)
      have hcoef : 0 ≤
          ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner hcoef) hlog
    _ = (2 : ℝ) ^ (50 : ℕ) * K *
        ∑ t ∈ Fintype.piFinset
            (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
          (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

theorem taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_unionMoment
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) {K : ℝ}
    (hK : 0 ≤ K)
    (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x)
    (hmoment :
      (∑ d ∈ taoSmallPrimeExceptionalConductors x H,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d (P j),
          ‖taoNormalizedPrimeCharacterSum χ (P j)‖ ^ 2) ≤ K) :
    taoSmallPrimeExceptionalConductorSum P x H j ≤
      (2 : ℝ) ^ (50 : ℕ) * K *
        ((H : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) := by
  exact (taoSmallPrimeExceptionalConductorSum_le_of_unionMoment
      P x H j hmoment).trans
    (mul_le_mul_of_nonneg_left
      (sum_taoSmallAntiSieveTupleCoefficient_le_log_pow_fifty x H hcutoff)
      (mul_nonneg (pow_nonneg (by norm_num) _) hK))

/-- The uniform aggregate theorem may be evaluated along every one of the
`1001` large-prime scale selectors simultaneously, provided those scales lie
above the lower distinguished-prime cutoff. -/
theorem exists_eventually_taoSmallPrimeExceptionalConductorMoment_le_of_lowerScale
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (P : ℕ → Fin 1001 → ℕ) (H : ℕ → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop, ∀ j,
      ∑ d ∈ taoSmallPrimeExceptionalConductors x (H x),
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ 2 ≤ K := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess
  rw [eventually_atTop] at huniform
  obtain ⟨Z₀, hZ₀⟩ := huniform
  have hlower : ∀ᶠ x : ℕ in atTop,
      Z₀ ≤ taoZPowerFloor (9 / 10 : ℝ) x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 9 / 10)).eventually (eventually_ge_atTop Z₀)
  refine ⟨K, hK, ?_⟩
  filter_upwards [
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_burgessRange,
    hscale, hlower] with x hrange hxscale hxlower j
  have hadmissible := isAdmissible_taoSmallPrimeExceptionalConductors
    (x := x) (H := H x) (Z := P x j) (hrange (P x j) (hxscale j))
  exact hZ₀ (P x j) (hxlower.trans (hxscale j)) _ hadmissible

/-- Burgess plus the lower-scale condition therefore bounds the literal
exceptional-conductor contribution for all `1001` selectors by the completed
logarithmic lcm coefficient. -/
theorem exists_eventually_taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (P : ℕ → Fin 1001 → ℕ) (H : ℕ → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop, ∀ j,
      taoSmallPrimeExceptionalConductorSum (P x) x (H x) j ≤
        (2 : ℝ) ^ (50 : ℕ) * K *
          ((H x : ℝ) ^ (50 : ℕ) *
            ((50 : ℝ) ^ (50 : ℕ) * 50 *
              (Real.log 4 *
                  (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) := by
  obtain ⟨K, hK, hmoment⟩ :=
    exists_eventually_taoSmallPrimeExceptionalConductorMoment_le_of_lowerScale
      hC hburgess P H hscale
  have hcutoff : ∀ᶠ x : ℕ in atTop,
      0 < taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_gt_atTop 0)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmoment, hcutoff] with x hx hcutoffx j
  exact taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_unionMoment
    (P x) x (H x) j hK.le hcutoffx (hx j)

theorem exists_eventually_taoSmallPrimeExceptionalConductorSum_le_mul_principalMajorant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (P : ℕ → Fin 1001 → ℕ) (H : ℕ → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop, ∀ j,
      taoSmallPrimeExceptionalConductorSum (P x) x (H x) j ≤
        K * taoSmallPrimePrincipalMertensMajorant x (H x) := by
  obtain ⟨K, hK, hsum⟩ :=
    exists_eventually_taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_explicitBurgess
      hC hburgess P H hscale
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsum] with x hx j
  simpa only [taoSmallPrimePrincipalMertensMajorant,
    mul_assoc, mul_left_comm, mul_comm] using hx j

/-- Lower-scale selectors eventually land in nonempty dyadic prime bands. -/
theorem eventually_taoDyadicPrimeBand_nonempty_of_lowerScale
    (P : ℕ → Fin 1001 → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∀ᶠ x : ℕ in atTop, ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty := by
  have hbands := eventually_taoDyadicPrimeBand_nonempty
  rw [eventually_atTop] at hbands
  obtain ⟨Z₀, hZ₀⟩ := hbands
  have hlower : ∀ᶠ x : ℕ in atTop,
      Z₀ ≤ taoZPowerFloor (9 / 10 : ℝ) x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 9 / 10)).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hscale, hlower] with x hxscale hxlower j
  exact hZ₀ (P x j) (hxlower.trans (hxscale j))

/-- The small anti-sieve cutoff is eventually strictly below every
lower-scale selector, as required by the conductor reduction. -/
theorem eventually_taoSmallAntiSievePrimeCutoff_lt_of_lowerScale
    (P : ℕ → Fin 1001 → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∀ᶠ x : ℕ in atTop, ∀ j,
      taoSmallAntiSievePrimeCutoff x < P x j := by
  have hcutoff : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 1)
  filter_upwards [
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_lt_lowerScale,
    hscale, hcutoff] with x hpow hxscale hcutoffx j
  have hself : taoSmallAntiSievePrimeCutoff x ≤
      taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hcutoffx (by norm_num : (1 : ℕ) ≤ 50)
  exact hself.trans_lt (hpow.trans_le (hxscale j))

/-- At any scale above `cutoff^50`, the explicit unexceptional totient error
is no larger than the principal Mertens majorant. -/
theorem taoSmallPrimeTotientErrorMajorant_le_principalMertensMajorant
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001)
    (hcutoff : 1 ≤ taoSmallAntiSievePrimeCutoff x)
    (hscale : taoSmallAntiSievePrimeCutoff x ^ (50 : ℕ) ≤ P j) :
    taoSmallPrimeTotientErrorMajorant P x H j ≤
      taoSmallPrimePrincipalMertensMajorant x H := by
  have hcOne : (1 : ℝ) ≤ taoSmallAntiSievePrimeCutoff x := by
    exact_mod_cast hcutoff
  have hpowCast : (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) ≤ P j := by
    exact_mod_cast hscale
  have hPOne : (1 : ℝ) ≤ P j := hcOne.trans
    ((show (taoSmallAntiSievePrimeCutoff x : ℝ) ≤
        (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) by
      simpa only [pow_one] using pow_le_pow_right₀ hcOne
        (by norm_num : (1 : ℕ) ≤ 50)).trans hpowCast)
  have hneg : (P j : ℝ) ^ (-(8 : ℝ)) ≤ (P j : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hPOne (by norm_num)
  have hprod : (P j : ℝ) ^ (-(8 : ℝ)) *
      (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) ≤ 1 := by
    calc
      _ ≤ (P j : ℝ) ^ (-(1 : ℝ)) *
          (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) := by gcongr
      _ = (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ) / P j := by
        rw [Real.rpow_neg_one]
        ring
      _ ≤ 1 := (div_le_one (by positivity)).2 hpowCast
  have hlogc : 0 ≤ Real.log (taoSmallAntiSievePrimeCutoff x) :=
    Real.log_nonneg hcOne
  have hbracket : Real.log 4 ≤
      Real.log 4 * (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
        Real.log (taoSmallAntiSievePrimeCutoff x) := by
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  have houter : 0 ≤ (2 : ℝ) ^ (50 : ℕ) * (H : ℝ) ^ (50 : ℕ) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by positivity) _)
  unfold taoSmallPrimeTotientErrorMajorant taoSmallPrimePrincipalMertensMajorant
  rw [mul_pow]
  calc
    ((2 : ℝ) ^ (50 : ℕ) * (P j : ℝ) ^ (-(8 : ℝ))) *
          ((H : ℝ) ^ (50 : ℕ) *
            (Real.log 4 ^ (50 : ℕ) *
              (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ))) =
        (2 : ℝ) ^ (50 : ℕ) * (H : ℝ) ^ (50 : ℕ) *
          Real.log 4 ^ (50 : ℕ) *
            ((P j : ℝ) ^ (-(8 : ℝ)) *
              (taoSmallAntiSievePrimeCutoff x : ℝ) ^ (50 : ℕ)) := by ring
    _ ≤ (2 : ℝ) ^ (50 : ℕ) * (H : ℝ) ^ (50 : ℕ) *
          Real.log 4 ^ (50 : ℕ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by positivity) _))
          (pow_nonneg (Real.log_nonneg (by norm_num)) _))
    _ ≤ (2 : ℝ) ^ (50 : ℕ) *
        ((H : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) := by
      have hconst : Real.log 4 ^ (50 : ℕ) ≤
          (50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ) := by
        calc
          Real.log 4 ^ (50 : ℕ) ≤
              (Real.log 4 *
                  (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ) :=
            pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hbracket _
          _ ≤ (50 : ℝ) ^ (50 : ℕ) * 50 *
              (Real.log 4 *
                  (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ) := by
            have hfactor : (1 : ℝ) ≤ (50 : ℝ) ^ (50 : ℕ) * 50 := by
              norm_num
            simpa only [one_mul, mul_assoc] using
              mul_le_mul_of_nonneg_right hfactor (pow_nonneg (by positivity) _)
      calc
        (2 : ℝ) ^ (50 : ℕ) * (H : ℝ) ^ (50 : ℕ) *
            Real.log 4 ^ (50 : ℕ) ≤
          ((2 : ℝ) ^ (50 : ℕ) * (H : ℝ) ^ (50 : ℕ)) *
            ((50 : ℝ) ^ (50 : ℕ) * 50 *
              (Real.log 4 *
                  (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ)) :=
          mul_le_mul_of_nonneg_left hconst houter
        _ = _ := by simp only [mul_assoc]

/-- Source-facing closure of the small-prime fiftieth-moment reduction:
conditional on the explicit Burgess estimate, the exceptional conductor term
is absorbed into a constant multiple of the fully elementary principal
Mertens majorant. -/
theorem exists_eventually_taoSmallPrimeFiftiethMoment_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (P : ℕ → Fin 1001 → ℕ)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoSmallPrimeFiftiethMoment (P x) (hP x) x (H x) (m' x) ≤
          1000 * ((1 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) +
            taoSmallPrimeTotientErrorMajorant (P x) x (H x) j) := by
  obtain ⟨K, hK, hexceptional⟩ :=
    exists_eventually_taoSmallPrimeExceptionalConductorSum_le_mul_principalMajorant_of_explicitBurgess
      hC hburgess P H hscale
  have hseparation :=
    eventually_taoSmallAntiSievePrimeCutoff_lt_of_lowerScale P hscale
  have hcutoff : ∀ᶠ x : ℕ in atTop,
      0 < taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_gt_atTop 0)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hexceptional, hseparation, hcutoff] with x hex hsep hcut
  obtain ⟨j, hj, hmoment⟩ :=
    exists_taoSmallPrimeFiftiethMoment_le_exceptional_add_elementary
      (P x) (hP x) x (H x) (m' x)
        (fun j hj => hsep j) hcut
  refine ⟨j, hj, hmoment.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    taoSmallPrimePrincipalMertensMajorant x (H x) +
          taoSmallPrimeExceptionalConductorSum (P x) x (H x) j +
        taoSmallPrimeTotientErrorMajorant (P x) x (H x) j ≤
      taoSmallPrimePrincipalMertensMajorant x (H x) +
          K * taoSmallPrimePrincipalMertensMajorant x (H x) +
        taoSmallPrimeTotientErrorMajorant (P x) x (H x) j := by
      gcongr
      exact hex j
    _ = (1 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) +
        taoSmallPrimeTotientErrorMajorant (P x) x (H x) j := by ring

/-- After also absorbing the explicit totient error, the entire small-prime
fiftieth moment is bounded by a fixed multiple of its elementary principal
majorant. -/
theorem exists_eventually_taoSmallPrimeFiftiethMoment_le_principalMajorant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (P : ℕ → Fin 1001 → ℕ)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hscale : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x (H x) (m' x) ≤
        1000 * (2 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) := by
  obtain ⟨K, hK, hmoment⟩ :=
    exists_eventually_taoSmallPrimeFiftiethMoment_le_of_explicitBurgess
      hC hburgess P hP H m' hscale
  have hcutoff : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 1)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmoment,
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_lowerScale,
    hscale, hcutoff] with x hx hcutPower hxscale hcutoffx
  obtain ⟨j, hj, hxj⟩ := hx
  have herror := taoSmallPrimeTotientErrorMajorant_le_principalMertensMajorant
    (P x) x (H x) j hcutoffx (hcutPower.trans (hxscale j))
  refine hxj.trans ?_
  calc
    1000 * ((1 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) +
        taoSmallPrimeTotientErrorMajorant (P x) x (H x) j) ≤
      1000 * ((1 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) +
        taoSmallPrimePrincipalMertensMajorant x (H x)) := by gcongr
    _ = 1000 * (2 + K) * taoSmallPrimePrincipalMertensMajorant x (H x) := by ring

end Tao2026

import Tao2026.BadIntervalLargePrimeDyadicScales

/-!
# Uniform adaptive large-prime blocks

The selector-level source estimates are uniformized here before summing the
dyadic grid.  In particular, the Burgess moment constant is chosen once and
works simultaneously for every admissible band at the current source scale.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- The explicit first-moment bracket produced by one adaptive source
dyadic block. -/
def taoLargePrimeSourceFirstMomentBlockMajorant
    (K : ℝ) (x r : ℕ) : ℝ :=
  ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
      (2 / ((2 ^ r : ℕ) : ℝ) +
        1003 * ((2 ^ r : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ))) +
    (K * ((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ)) *
      (256 * Real.log (taoZ x) ^ 2 / ((2 ^ r : ℕ) : ℝ))

/-- The explicit ordered covariance bracket produced by one pair of
adaptive source dyadic blocks. -/
def taoLargePrimeSourceCovarianceBlockMajorant
    (K : ℝ) (x r s : ℕ) : ℝ :=
  ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
      ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
      (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
        ((2 ^ r : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        ((2 ^ s : ℕ) : ℝ) ^ (-(1 : ℝ))) +
    (K * (((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
        ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
        ((2 ^ s : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
      (6144 * Real.log (taoZ x) ^ 3 /
        (((2 ^ r : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)))

/-- The PNT upper estimate holds simultaneously on the source dyadic grid. -/
theorem eventually_forall_card_taoLargePrimeSourceDyadicBand_le_two_mul_div_log :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤
        2 * (((2 ^ r : ℕ) : ℝ) / Real.log (2 ^ r : ℕ)) := by
  let Rel : ℕ → ℕ → Prop := fun x r =>
    r ∈ taoLargePrimeSourceDyadicExponents x
  let Good : ℕ → ℕ → Prop := fun _ r =>
    ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤
      2 * (((2 ^ r : ℕ) : ℝ) / Real.log (2 ^ r : ℕ))
  have hne : ∀ᶠ x : ℕ in atTop, ∃ r, Rel x r :=
    eventually_taoLargePrimeSourceDyadicExponents_nonempty.mono fun x hx =>
      ⟨hx.choose, hx.choose_spec⟩
  have hselector : ∀ f : ℕ → ℕ,
      (∀ᶠ x : ℕ in atTop, Rel x (f x)) →
        ∀ᶠ x : ℕ in atTop, Good x (f x) := by
    intro f hf
    have hf' : ∀ᶠ x : ℕ in atTop,
        f x ∈ taoLargePrimeSourceDyadicExponents x := by
      simpa only [Rel] using hf
    have hR :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hf'
    have hRtendsto : Tendsto (fun x : ℕ => 2 ^ f x) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      have hpow : ∀ᶠ x : ℕ in atTop,
          (b : ℝ) ≤ (taoZ x) ^ (1 / 200 : ℝ) :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
          tendsto_taoZ_atTop).eventually (eventually_ge_atTop (b : ℝ))
      filter_upwards [hpow, hR.lower] with x hpowX hRX
      exact_mod_cast hpowX.trans hRX
    exact hRtendsto.eventually
      eventually_card_taoDyadicPrimeBand_le_two_mul_div_log
  simpa only [Rel, Good] using
    (eventually_forall_of_forall_selector hne hselector)

/-- Every retained scale has logarithm at least `log z / 200`. -/
theorem eventually_forall_log_taoZ_div_two_hundred_le_log_sourceDyadicScale :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      (1 / 200 : ℝ) * Real.log (taoZ x) ≤
        Real.log (2 ^ r : ℕ) := by
  filter_upwards [eventually_taoLargePrimeSourceDyadicScale_bounds] with x hx
  intro r hr
  have hscale := hx r hr
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Real.rpow_pos_of_pos (taoZ_pos x) (1 / 200 : ℝ))
    (by positivity : (0 : ℝ) < (2 ^ r : ℕ)) hscale.1
  rw [Real.log_rpow (taoZ_pos x)] at hlog
  exact hlog

/-- The complete one-band bracket is uniformly `O(1 / log z)` over the
canonical source grid. -/
theorem eventually_forall_taoLargePrimeSourceFirstMomentBlockMajorant_le
    {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      taoLargePrimeSourceFirstMomentBlockMajorant K x r ≤
        500000 / Real.log (taoZ x) := by
  have habsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := 256 * K) (k := (3 : ℝ)) (a := (49 / 10000 : ℝ))
      (b := (0 : ℝ)) (mul_nonneg (by norm_num) hK) (by norm_num)
  filter_upwards
    [eventually_forall_card_taoLargePrimeSourceDyadicBand_le_two_mul_div_log,
      eventually_forall_log_taoZ_div_two_hundred_le_log_sourceDyadicScale,
      eventually_taoLargePrimeSourceDyadicScale_bounds, habsorb,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
        x hcard hlogLower hscale habsorbX hz
  intro r hr
  let R : ℝ := ((2 ^ r : ℕ) : ℝ)
  let L : ℝ := Real.log (taoZ x)
  let LR : ℝ := Real.log (2 ^ r : ℕ)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := by
    dsimp only [R]
    have htwo : 2 ≤ (2 ^ r : ℕ) := (hscale r hr).2.2
    exact_mod_cast (show 1 ≤ (2 ^ r : ℕ) by omega)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hLRLower : (1 / 200 : ℝ) * L ≤ LR := by
    simpa only [L, LR] using hlogLower r hr
  have hLRpos : 0 < LR := by nlinarith
  have hcardR : ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤
      2 * (R / LR) := by
    simpa only [R, LR] using hcard r hr
  have hdecayOne : R ^ (-(1 / 1000 : ℝ)) ≤ 1 := by
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hRone (by norm_num : (-(1 / 1000 : ℝ)) ≤ 0))
  have hRproduct : R * R ^ (-(1001 / 1000 : ℝ)) =
      R ^ (-(1 / 1000 : ℝ)) := by
    calc
      R * R ^ (-(1001 / 1000 : ℝ)) =
          R ^ (1 : ℝ) * R ^ (-(1001 / 1000 : ℝ)) := by
            rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + (-(1001 / 1000 : ℝ))) := by
        rw [Real.rpow_add hRpos]
      _ = R ^ (-(1 / 1000 : ℝ)) := by norm_num
  have hmainEq :
      (2 * (R / LR)) *
          (2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ))) =
        4 / LR + 2006 * R ^ (-(1 / 1000 : ℝ)) / LR := by
    field_simp [ne_of_gt hRpos, ne_of_gt hLRpos]
    nlinarith [hRproduct]
  have hmain :
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          (2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ))) ≤
        402000 / L := by
    have hfactor : 0 ≤
        2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ)) := by positivity
    calc
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          (2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ))) ≤
        (2 * (R / LR)) *
          (2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ))) :=
            mul_le_mul_of_nonneg_right hcardR hfactor
      _ = 4 / LR + 2006 * R ^ (-(1 / 1000 : ℝ)) / LR := hmainEq
      _ ≤ 2010 / LR := by
        apply (le_div_iff₀ hLRpos).2
        rw [add_mul]
        field_simp [ne_of_gt hLRpos]
        nlinarith
      _ ≤ 402000 / L := by
        apply (div_le_div_iff₀ hLRpos hLpos).2
        nlinarith
  have hRexceptionIdentity : R ^ (1 / 50 : ℝ) / R =
      R ^ (-(49 / 50 : ℝ)) := by
    calc
      R ^ (1 / 50 : ℝ) / R =
          R ^ (1 / 50 : ℝ) / R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = R ^ ((1 / 50 : ℝ) - 1) := by
        rw [Real.rpow_sub hRpos]
      _ = R ^ (-(49 / 50 : ℝ)) := by norm_num
  have hscaleLower : (taoZ x) ^ (1 / 200 : ℝ) ≤ R := by
    simpa only [R] using (hscale r hr).1
  have hdecay : R ^ (-(49 / 50 : ℝ)) ≤
      (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
    calc
      R ^ (-(49 / 50 : ℝ)) ≤
          ((taoZ x) ^ (1 / 200 : ℝ)) ^ (-(49 / 50 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos (taoZ_pos x) _) hscaleLower (by norm_num)
      _ = (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
        rw [← Real.rpow_mul (taoZ_pos x).le]
        congr 1
        norm_num
  have habsorbNat :
      (256 * K) * L ^ (3 : ℕ) / (taoZ x) ^ (49 / 10000 : ℝ) ≤ 1 := by
    have hx := habsorbX
    rw [Real.rpow_zero, div_one] at hx
    rw [show L ^ (3 : ℕ) = L ^ (3 : ℝ) from
      (Real.rpow_natCast L 3).symm]
    simpa only [L] using hx
  have hweightedDecay :
      (256 * K) * L ^ (3 : ℕ) * R ^ (-(49 / 50 : ℝ)) ≤ 1 := by
    calc
      (256 * K) * L ^ (3 : ℕ) * R ^ (-(49 / 50 : ℝ)) ≤
          (256 * K) * L ^ (3 : ℕ) *
            (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = (256 * K) * L ^ (3 : ℕ) /
          (taoZ x) ^ (49 / 10000 : ℝ) := by
        rw [Real.rpow_neg (taoZ_pos x).le]
        ring
      _ ≤ 1 := habsorbNat
  have hexception :
      (K * R ^ (1 / 50 : ℝ)) * (256 * L ^ 2 / R) ≤ 1 / L := by
    apply (le_div_iff₀ hLpos).2
    calc
      (K * R ^ (1 / 50 : ℝ)) * (256 * L ^ 2 / R) * L =
          (256 * K) * L ^ (3 : ℕ) *
            (R ^ (1 / 50 : ℝ) / R) := by ring
      _ =
          (256 * K) * L ^ (3 : ℕ) * R ^ (-(49 / 50 : ℝ)) := by
        rw [hRexceptionIdentity]
      _ ≤ 1 := hweightedDecay
  rw [taoLargePrimeSourceFirstMomentBlockMajorant]
  change
    ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          (2 / R + 1003 * R ^ (-(1001 / 1000 : ℝ))) +
        (K * R ^ (1 / 50 : ℝ)) * (256 * L ^ 2 / R) ≤ 500000 / L
  calc
    _ ≤ 402000 / L + 1 / L := add_le_add hmain hexception
    _ ≤ 500000 / L := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hLpos.le

/-- One Burgess constant controls all adaptive endpoint sets, simultaneously
in their threshold scale and admissible conductor finset. -/
theorem exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ R : ℕ, ∀ D : Finset ℕ, 2 ≤ R →
        (∀ j : Fin 1001,
          IsAdmissibleTaoExceptionalConductorSet D (P x j)) →
        ((taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) ≤
          K * (R : ℝ) ^ (1 / 50 : ℝ) := by
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess
  let K : ℝ := 1000 * M
  have hK : 0 < K := by dsimp [K]; positivity
  have hcoord : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      ∀ D : Finset ℕ,
        IsAdmissibleTaoExceptionalConductorSet D (P x j) →
        ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ (2 : ℕ) ≤ M := by
    intro j
    exact (hscale.tendsto_scale j).eventually hmoment
  have hall : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ Finset.univ.erase (0 : Fin 1001), ∀ D : Finset ℕ,
        IsAdmissibleTaoExceptionalConductorSet D (P x j) →
        ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ (2 : ℕ) ≤ M := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hcoord j
  refine ⟨K, hK, ?_⟩
  filter_upwards [hall] with x hmomentX
  intro R D hR hD
  have hRpos : 0 < R := by omega
  have hcard := card_taoLargePrimeAdaptiveExceptionalConductorsFor_le
    D (P x) R
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((taoLargePrimeAdaptiveExceptionalConductorsIn
            D (P x j) R).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) ≤
        _ := hcardReal
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        M * (R : ℝ) ^ (1 / 50 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact card_taoLargePrimeAdaptiveExceptionalConductorsIn_cast_le_of_moment
        hRpos (hmomentX j hj D (hD j))
    _ = K * (R : ℝ) ^ (1 / 50 : ℝ) := by
      dsimp [K]
      simp
      ring

/-- One Burgess constant controls all adaptive common-factor partner sets,
simultaneously in the threshold scale, fixed prime, and ambient range. -/
theorem exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalPartnersFor_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ S p lowerPrime upperPrime : ℕ, 2 ≤ S → Nat.Prime p →
        (∀ j : Fin 1001, (upperPrime : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ))) →
        ((taoLargePrimeAdaptiveExceptionalPartnersFor
          p lowerPrime upperPrime (P x) S).card : ℝ) ≤
            K * (S : ℝ) ^ (1 / 50 : ℝ) := by
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_eventually_cofactorExceptional_secondMoment_pointwise_le_of_explicitBurgess
      hC hburgess
  let K : ℝ := 1000 * M
  have hK : 0 < K := by dsimp [K]; positivity
  have hcoord : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      ∀ q₁ : ℕ, ∀ D : Finset ℕ,
        0 < q₁ → Squarefree q₁ →
        (∀ q₂ ∈ D, Squarefree q₂) →
        (∀ q₂ ∈ D, Nat.Coprime q₁ q₂) →
        (∀ q₂ ∈ D, (q₂ : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) →
        ∑ q₂ ∈ D,
          ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) (P x j),
            ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ 2 ≤ M := by
    intro j
    exact (hscale.tendsto_scale j).eventually hmoment
  have hall : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∀ q₁ : ℕ, ∀ D : Finset ℕ,
          0 < q₁ → Squarefree q₁ →
          (∀ q₂ ∈ D, Squarefree q₂) →
          (∀ q₂ ∈ D, Nat.Coprime q₁ q₂) →
          (∀ q₂ ∈ D, (q₂ : ℝ) ≤
            Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) →
          ∑ q₂ ∈ D,
            ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) (P x j),
              ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ 2 ≤ M := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hcoord j
  refine ⟨K, hK, ?_⟩
  filter_upwards [hall] with x hmomentX
  intro S p lowerPrime upperPrime hS hp hrange
  have hSpos : 0 < S := by omega
  let D := (taoLargeAntiSievePrimeRange lowerPrime upperPrime).erase p
  have hDsq : ∀ q ∈ D, Squarefree q := by
    intro q hq
    exact (mem_taoLargeAntiSievePrimeRange.mp
      (Finset.mem_of_mem_erase hq)).1.squarefree
  have hDcop : ∀ q ∈ D, Nat.Coprime p q := by
    intro q hq
    have hqPrime : Nat.Prime q :=
      (mem_taoLargeAntiSievePrimeRange.mp
        (Finset.mem_of_mem_erase hq)).1
    exact (Nat.coprime_primes hp hqPrime).mpr
      (Finset.ne_of_mem_erase hq).symm
  have hDrange : ∀ j : Fin 1001, ∀ q ∈ D, (q : ℝ) ≤
      Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) := by
    intro j q hq
    calc
      (q : ℝ) ≤ (upperPrime : ℝ) := by
        exact_mod_cast (mem_taoLargeAntiSievePrimeRange.mp
          (Finset.mem_of_mem_erase hq)).2.2
      _ ≤ Real.sqrt
          ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) := hrange j
  have hcard := card_taoLargePrimeAdaptiveExceptionalPartnersFor_le
    p lowerPrime upperPrime (P x) S
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalPartnersFor
        p lowerPrime upperPrime (P x) S).card : ℝ) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((taoLargePrimeAdaptiveExceptionalCofactorsIn p D
            (P x j) S).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((taoLargePrimeAdaptiveExceptionalPartnersFor
        p lowerPrime upperPrime (P x) S).card : ℝ) ≤ _ := hcardReal
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        M * (S : ℝ) ^ (1 / 50 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply card_taoLargePrimeAdaptiveExceptionalCofactorsIn_cast_le_of_moment
        hSpos
      exact hmomentX j hj p D hp.pos hp.squarefree hDsq hDcop (hDrange j)
    _ = K * (S : ℝ) ^ (1 / 50 : ℝ) := by
      dsimp [K]
      simp
      ring

/-- Uniform source-shape count for every mixed adaptive exceptional modulus
pair satisfying the explicit ambient conductor geometry. -/
theorem exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalModuliPairs_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ R S lowerPrime upperPrime : ℕ, 2 ≤ R → 2 ≤ S →
      (∀ j : Fin 1001,
        IsAdmissibleTaoExceptionalConductorSet
          (taoLargeAntiSievePrimeRange lowerPrime upperPrime) (P x j)) →
      taoDyadicPrimeBand R ⊆
        taoLargeAntiSievePrimeRange lowerPrime upperPrime →
      taoDyadicPrimeBand S ⊆
        taoLargeAntiSievePrimeRange lowerPrime upperPrime →
      (∀ p ∈ taoDyadicPrimeBand R, ∀ j : Fin 1001,
        (upperPrime : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ))) →
      ((taoLargePrimeAdaptiveExceptionalModuliPairs (P x) R S).card : ℝ) ≤
        K * ((R : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) +
          ((taoDyadicPrimeBand R).card : ℝ) *
            (S : ℝ) ^ (1 / 50 : ℝ)) := by
  obtain ⟨K₁, hK₁, hEndpoint⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale
  obtain ⟨K₂, hK₂, hPartners⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalPartnersFor_le_of_explicitBurgess
      hC hburgess hscale
  let K : ℝ := K₁ + K₁ + K₂
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hEndpoint, hPartners] with x hEndpointX hPartnersX
  intro R S lowerPrime upperPrime hR hS hD hBandR hBandS hPartnerRange
  let D := taoLargeAntiSievePrimeRange lowerPrime upperPrime
  have hEndpointR := hEndpointX R D hR (by simpa only [D] using hD)
  have hEndpointS := hEndpointX S D hS (by simpa only [D] using hD)
  have hA₁ : (((taoDyadicPrimeBand R).filter fun p =>
      p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) ≤
      K₁ * (R : ℝ) ^ (1 / 50 : ℝ) := by
    calc
      (((taoDyadicPrimeBand R).filter fun p =>
          p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) R).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (by
            intro p hp
            exact (Finset.mem_filter.mp hp).2)
      _ ≤ K₁ * (R : ℝ) ^ (1 / 50 : ℝ) := hEndpointR
  have hA₂ : (((taoDyadicPrimeBand S).filter fun q =>
      q ∈ taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) S).card : ℝ) ≤
      K₁ * (S : ℝ) ^ (1 / 50 : ℝ) := by
    calc
      (((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) S).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalConductorsFor D (P x) S).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (by
            intro q hq
            exact (Finset.mem_filter.mp hq).2)
      _ ≤ K₁ * (S : ℝ) ^ (1 / 50 : ℝ) := hEndpointS
  have hB : ∀ p ∈ taoDyadicPrimeBand R,
      (((taoDyadicPrimeBand S).filter fun q =>
        q ∈ taoLargePrimeAdaptiveExceptionalPartnersFor
          p lowerPrime upperPrime (P x) S).card : ℝ) ≤
        K₂ * (S : ℝ) ^ (1 / 50 : ℝ) := by
    intro p hp
    calc
      (((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeAdaptiveExceptionalPartnersFor
            p lowerPrime upperPrime (P x) S).card : ℝ) ≤
        ((taoLargePrimeAdaptiveExceptionalPartnersFor
          p lowerPrime upperPrime (P x) S).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (by
              intro q hq
              exact (Finset.mem_filter.mp hq).2)
      _ ≤ K₂ * (S : ℝ) ^ (1 / 50 : ℝ) :=
        hPartnersX S p lowerPrime upperPrime hS
          (mem_taoDyadicPrimeBand.mp hp).1 (hPartnerRange p hp)
  have hpair := card_taoLargePrimeAdaptiveExceptionalModuliPairs_cast_le
    (P x) R S lowerPrime upperPrime hBandR hBandS
      (K₁ * (R : ℝ) ^ (1 / 50 : ℝ))
      (K₁ * (S : ℝ) ^ (1 / 50 : ℝ))
      (K₂ * (S : ℝ) ^ (1 / 50 : ℝ)) hA₁ hA₂ hB
  let U : ℝ := (R : ℝ) ^ (1 / 50 : ℝ) *
    ((taoDyadicPrimeBand S).card : ℝ)
  let V : ℝ := ((taoDyadicPrimeBand R).card : ℝ) *
    (S : ℝ) ^ (1 / 50 : ℝ)
  have hUNonneg : 0 ≤ U := by dsimp [U]; positivity
  have hVNonneg : 0 ≤ V := by dsimp [V]; positivity
  have hK₁K : K₁ ≤ K := by dsimp [K]; linarith
  have hK₁K₂K : K₁ + K₂ ≤ K := by dsimp [K]; linarith
  calc
    ((taoLargePrimeAdaptiveExceptionalModuliPairs (P x) R S).card : ℝ) ≤
        K₁ * U + K₁ * V + K₂ * V := by
      dsimp only [D, U, V]
      convert hpair using 1
      all_goals ring
    _ = K₁ * U + (K₁ + K₂) * V := by ring
    _ ≤ K * U + K * V :=
      add_le_add (mul_le_mul_of_nonneg_right hK₁K hUNonneg)
        (mul_le_mul_of_nonneg_right hK₁K₂K hVNonneg)
    _ = K * (U + V) := by ring
    _ = K * ((R : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) +
          ((taoDyadicPrimeBand R).card : ℝ) *
            (S : ℝ) ^ (1 / 50 : ℝ)) := by rfl

/-! ## Simultaneous source blocks on the canonical dyadic grid -/

/-- Proposition 6.7's adaptive first-moment block holds simultaneously on
every retained source scale, with one Burgess constant. -/
theorem exists_eventually_forall_sum_taoLargePrimeProbability_adaptive_sourceBlock_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        taoLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              (2 / ((2 ^ r : ℕ) : ℝ) +
                1003 * ((2 ^ r : ℕ) : ℝ) ^
                  (-(1001 / 1000 : ℝ))) +
            (K * ((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ)) *
              (256 * Real.log (taoZ x) ^ 2 / ((2 ^ r : ℕ) : ℝ))) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
      hC hburgess hscale
  let Rel : ℕ → ℕ → Prop := fun x r =>
    r ∈ taoLargePrimeSourceDyadicExponents x
  let Good : ℕ → ℕ → Prop := fun x r =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
        (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        taoLargePrimeProbability (P x) hP (m' x) a) ≤
        (H x - 1 : ℕ) *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              (2 / ((2 ^ r : ℕ) : ℝ) +
                1003 * ((2 ^ r : ℕ) : ℝ) ^
                  (-(1001 / 1000 : ℝ))) +
            (K * ((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ)) *
              (256 * Real.log (taoZ x) ^ 2 / ((2 ^ r : ℕ) : ℝ)))
  have hne : ∀ᶠ x : ℕ in atTop, ∃ r, Rel x r :=
    eventually_taoLargePrimeSourceDyadicExponents_nonempty.mono fun x hx => by
      exact ⟨hx.choose, hx.choose_spec⟩
  have hselector : ∀ f : ℕ → ℕ,
      (∀ᶠ x : ℕ in atTop, Rel x (f x)) →
        ∀ᶠ x : ℕ in atTop, Good x (f x) := by
    intro f hf
    have hf' : ∀ᶠ x : ℕ in atTop,
        f x ∈ taoLargePrimeSourceDyadicExponents x := by
      simpa only [Rel] using hf
    let R : ℕ → ℕ := fun x => 2 ^ f x
    have hR : TaoLargePrimeDyadicBandSelector R :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hf'
    have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
      hscale hR hR (Filter.Eventually.of_forall fun _ => le_rfl)
    have herror := eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower
      hscale hR.toTaoLargePrimeSourceBandSelector
    have hcrude := eventually_taoLargePrimeProbability_le_crude_dyadicBand
      hscale hR m'
    have hHscale : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hf'] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x) hfX)
    filter_upwards [hcard, hgeom, herror, hcrude, hHscale,
      hR.eventually_two_le,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
        x hcardX hgeomX herrorX hcrudeX hHscaleX hRtwo hz
    intro hP
    have hD : ∀ j : Fin 1001,
        IsAdmissibleTaoExceptionalConductorSet
          (taoDyadicPrimeBand (R x)) (P x j) := by
      intro j
      have hambient := hgeomX.1 j
      have hsubset := hgeomX.2.1
      exact ⟨fun p hp => hambient.1 p (hsubset hp),
        fun p hp => hambient.2 p (hsubset hp)⟩
    have hcardFull := hcardX (R x) (taoDyadicPrimeBand (R x)) hRtwo hD
    have hcardFiltered :
        (((taoDyadicPrimeBand (R x)).filter fun p =>
          p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
            (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
          K * (R x : ℝ) ^ (1 / 50 : ℝ) := by
      calc
        (((taoDyadicPrimeBand (R x)).filter fun p =>
            p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
              (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) ≤
          ((taoLargePrimeAdaptiveExceptionalConductorsFor
            (taoDyadicPrimeBand (R x)) (P x) (R x)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (by
                intro p hp
                exact (Finset.mem_filter.mp hp).2)
        _ ≤ K * (R x : ℝ) ^ (1 / 50 : ℝ) := hcardFull
    have hB : 0 ≤
        256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by positivity
    have hblock := sum_taoLargePrimeProbability_adaptive_dyadicBlock_le
      (P x) hP (R x) (H x) (m' x) hRtwo hHscaleX
        (1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)))
        (256 * Real.log (taoZ x) ^ 2 / (R x : ℝ))
        (K * (R x : ℝ) ^ (1 / 50 : ℝ))
        (by positivity) hB (fun p hp => herrorX p hp) hcardFiltered
        (by
          intro a ha _haExceptional
          have haData := mem_taoLargeAntiSieveIndices.mp ha
          have haBand : a.2 ∈ taoDyadicPrimeBand (R x) := by
            rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
              (show 0 < R x by omega)]
            exact mem_taoLargeAntiSievePrimeRange.mpr haData.2.2
          have hshift : ¬a.2 ∣ a.1 :=
            Nat.not_dvd_of_pos_of_lt haData.1 (by omega)
          exact hcrudeX hP a haBand hshift)
    simpa only [Good, R] using hblock
  have hall := eventually_forall_of_forall_selector hne hselector
  refine ⟨K, hK, ?_⟩
  simpa only [Rel, Good] using hall

/-- Proposition 6.8's ordered adaptive covariance block holds
simultaneously on every ordered pair of retained source scales, with one
Burgess constant. -/
theorem exists_eventually_forall_sum_taoLargePrimeCovariance_adaptive_sourceTwoBand_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ s ∈ taoLargePrimeSourceDyadicExponents x, r ≤ s →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
        ∑ b ∈ (taoLargeAntiSieveIndices
          (2 ^ s - 1) (2 * 2 ^ s - 1) (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                ((2 ^ r : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                ((2 ^ s : ℕ) : ℝ) ^ (-(1 : ℝ))) +
            (K * (((2 ^ r : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
              ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
                ((2 ^ s : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                (((2 ^ r : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)))) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_forall_card_taoLargePrimeAdaptiveExceptionalModuliPairs_le_of_explicitBurgess
      hC hburgess hscale
  let Rel : ℕ → (ℕ × ℕ) → Prop := fun x rs =>
    rs.1 ∈ taoLargePrimeSourceDyadicExponents x ∧
      rs.2 ∈ taoLargePrimeSourceDyadicExponents x ∧ rs.1 ≤ rs.2
  let Good : ℕ → (ℕ × ℕ) → Prop := fun x rs =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ rs.1 - 1) (2 * 2 ^ rs.1 - 1) (H x),
        ∑ b ∈ (taoLargeAntiSieveIndices
          (2 ^ rs.2 - 1) (2 * 2 ^ rs.2 - 1) (H x)).filter
            (fun b => b.2 ≠ a.2),
          taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
        ((H x - 1 : ℕ) : ℝ) ^ 2 *
          (((taoDyadicPrimeBand (2 ^ rs.1)).card : ℝ) *
              ((taoDyadicPrimeBand (2 ^ rs.2)).card : ℝ) *
              (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
                ((2 ^ rs.1 : ℕ) : ℝ) ^ (-(1001 / 1000 : ℝ)) *
                ((2 ^ rs.2 : ℕ) : ℝ) ^ (-(1 : ℝ))) +
            (K * (((2 ^ rs.1 : ℕ) : ℝ) ^ (1 / 50 : ℝ) *
                ((taoDyadicPrimeBand (2 ^ rs.2)).card : ℝ) +
              ((taoDyadicPrimeBand (2 ^ rs.1)).card : ℝ) *
                ((2 ^ rs.2 : ℕ) : ℝ) ^ (1 / 50 : ℝ))) *
              (6144 * Real.log (taoZ x) ^ 3 /
                (((2 ^ rs.1 : ℕ) : ℝ) *
                  ((2 ^ rs.2 : ℕ) : ℝ))))
  have hne : ∀ᶠ x : ℕ in atTop, ∃ rs, Rel x rs :=
    eventually_taoLargePrimeSourceDyadicExponents_nonempty.mono fun x hx => by
      exact ⟨(hx.choose, hx.choose), hx.choose_spec, hx.choose_spec, le_rfl⟩
  have hselector : ∀ f : ℕ → (ℕ × ℕ),
      (∀ᶠ x : ℕ in atTop, Rel x (f x)) →
        ∀ᶠ x : ℕ in atTop, Good x (f x) := by
    intro f hf
    have hfR : ∀ᶠ x : ℕ in atTop,
        (f x).1 ∈ taoLargePrimeSourceDyadicExponents x := by
      exact hf.mono fun x hx => hx.1
    have hfS : ∀ᶠ x : ℕ in atTop,
        (f x).2 ∈ taoLargePrimeSourceDyadicExponents x := by
      exact hf.mono fun x hx => hx.2.1
    have hfRS : ∀ᶠ x : ℕ in atTop, (f x).1 ≤ (f x).2 := by
      exact hf.mono fun x hx => hx.2.2
    let R : ℕ → ℕ := fun x => 2 ^ (f x).1
    let S : ℕ → ℕ := fun x => 2 ^ (f x).2
    have hR : TaoLargePrimeDyadicBandSelector R :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hfR
    have hS : TaoLargePrimeDyadicBandSelector S :=
      taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents hfS
    have hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x := by
      filter_upwards [hfRS] with x hx
      exact Nat.pow_le_pow_right (by norm_num) hx
    have hgeom := eventually_taoLargePrimeAdaptive_commonRange_geometry
      hscale hR hS hRS
    have herror :=
      eventually_taoLargePrimeMixedAdaptiveCovarianceImprovedError_le_sourcePower
        hscale hR.toTaoLargePrimeSourceBandSelector
          hS.toTaoLargePrimeSourceBandSelector hRS
    have hcrude := eventually_taoLargePrimeJointProbability_le_crude_twoBand
      hscale hR hS m'
    have hHscaleR : ∀ᶠ x : ℕ in atTop, H x ≤ R x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hfR] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x).1 hfX)
    have hHscaleS : ∀ᶠ x : ℕ in atTop, H x ≤ S x - 1 := by
      filter_upwards
        [hH, eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one,
          hfS] with x hHX hgrid hfX
      exact hHX.trans (hgrid (f x).2 hfX)
    filter_upwards [hcard, hgeom, herror, hcrude, hHscaleR, hHscaleS,
      hR.eventually_two_le, hS.eventually_two_le,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
        x hcardX hgeomX herrorX hcrudeX hHRX hHSX hRtwo hStwo hz
    intro hP
    have hcardPair := hcardX (R x) (S x) (R x - 1) (2 * S x - 1)
      hRtwo hStwo hgeomX.1 hgeomX.2.1 hgeomX.2.2.1 hgeomX.2.2.2
    have hB : 0 ≤ 6144 * Real.log (taoZ x) ^ 3 /
        ((R x : ℝ) * (S x : ℝ)) := by
      exact div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg hz) 3))
        (mul_nonneg (by positivity) (by positivity))
    have hblock := sum_taoLargePrimeCovariance_adaptive_twoBand_le
      (P x) hP (R x) (S x) (H x) (m' x) hRtwo hStwo hHRX hHSX
        (taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)))
        (6144 * Real.log (taoZ x) ^ 3 / ((R x : ℝ) * (S x : ℝ)))
        (K * ((R x : ℝ) ^ (1 / 50 : ℝ) *
            ((taoDyadicPrimeBand (S x)).card : ℝ) +
          ((taoDyadicPrimeBand (R x)).card : ℝ) *
            (S x : ℝ) ^ (1 / 50 : ℝ)))
        (by
          unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
          unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
          unfold taoLargePrimeSourceJointPowerConstant
          positivity)
        hB (fun p hp q hq hpq _hpair => herrorX p q hp hq hpq)
        hcardPair
        (by
          intro a ha b hb _hbad
          have haData := mem_taoLargeAntiSieveIndices.mp ha
          have hbMem := (Finset.mem_filter.mp hb).1
          have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
          have haBand : a.2 ∈ taoDyadicPrimeBand (R x) := by
            rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
              (show 0 < R x by omega)]
            exact mem_taoLargeAntiSievePrimeRange.mpr haData.2.2
          have hbBand : b.2 ∈ taoDyadicPrimeBand (S x) := by
            rw [← taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
              (show 0 < S x by omega)]
            exact mem_taoLargeAntiSievePrimeRange.mpr hbData.2.2
          have hpq : a.2 ≠ b.2 := (Finset.mem_filter.mp hb).2.symm
          have hshiftA : ¬a.2 ∣ a.1 :=
            Nat.not_dvd_of_pos_of_lt haData.1 (by omega)
          have hshiftB : ¬b.2 ∣ b.1 :=
            Nat.not_dvd_of_pos_of_lt hbData.1 (by omega)
          exact hcrudeX hP a b haBand hbBand hpq hshiftA hshiftB)
    simpa only [Good, R, S] using hblock
  have hall := eventually_forall_of_forall_selector hne hselector
  refine ⟨K, hK, ?_⟩
  filter_upwards [hall] with x hx
  intro r hr s hs hrs hP
  exact hx (r, s) ⟨hr, hs, hrs⟩ hP

/-! ## Final dyadic first-moment summation -/

/-- The complete sum of the Proposition 6.7 adaptive block estimates over
all source dyadic scales is `O(H)`. -/
theorem eventually_sum_taoLargePrimeProbability_adaptive_sourceDyadicScales_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoLargePrimeProbability (P x) hP (m' x) a) ≤
        2000000 * (H x : ℝ) := by
  obtain ⟨K, hK, hblocks⟩ :=
    exists_eventually_forall_sum_taoLargePrimeProbability_adaptive_sourceBlock_le
      hC hburgess hscale H m' hH
  have hmajorant :=
    eventually_forall_taoLargePrimeSourceFirstMomentBlockMajorant_le hK.le
  filter_upwards [hblocks, hmajorant,
    eventually_card_taoLargePrimeSourceDyadicExponents_cast_le_log,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hblocksX hmajorantX hcardX hz
  intro hP
  let L : ℝ := Real.log (taoZ x)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hsumBlocks :
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoLargePrimeProbability (P x) hP (m' x) a) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) *
          taoLargePrimeSourceFirstMomentBlockMajorant K x r := by
    apply Finset.sum_le_sum
    intro r hr
    simpa only [taoLargePrimeSourceFirstMomentBlockMajorant] using
      hblocksX r hr hP
  calc
    (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargeAntiSieveIndices
          (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
          taoLargePrimeProbability (P x) hP (m' x) a) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) *
          taoLargePrimeSourceFirstMomentBlockMajorant K x r := hsumBlocks
    _ ≤ ∑ _r ∈ taoLargePrimeSourceDyadicExponents x,
        ((H x - 1 : ℕ) : ℝ) * (500000 / L) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (by simpa only [L] using hmajorantX r hr) (by positivity)
    _ = ((taoLargePrimeSourceDyadicExponents x).card : ℝ) *
        (((H x - 1 : ℕ) : ℝ) * (500000 / L)) := by simp
    _ ≤ (4 * L) * (((H x - 1 : ℕ) : ℝ) * (500000 / L)) := by
      exact mul_le_mul_of_nonneg_right (by simpa only [L] using hcardX)
        (by positivity)
    _ = 2000000 * ((H x - 1 : ℕ) : ℝ) := by
      field_simp [ne_of_gt hLpos]
      ring
    _ ≤ 2000000 * (H x : ℝ) := by
      gcongr
      exact_mod_cast Nat.sub_le (H x) 1

/-- Proposition 6.7 on the literal source prime range: its expected
large-prime contribution is `O(H)`. -/
theorem eventually_taoLargePrimeMean_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoLargePrimeMean (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ≤
        2000000 * (H x : ℝ) := by
  filter_upwards
    [eventually_sum_taoLargePrimeProbability_adaptive_sourceDyadicScales_le
      hC hburgess hscale H m' hH] with x hsum
  intro hP
  rw [taoLargePrimeMean_eq,
    taoLargeAntiSieveIndices_sourceCutoffs_eq,
    sum_taoLargePrimeSourceIndices_eq_sum_dyadicSlices]
  apply le_trans (Finset.sum_le_sum (fun r hr => ?_)) (hsum hP)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro a ha
      have haData := Finset.mem_product.mp ha
      rw [taoLargeAntiSieveIndices,
        taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand (by positivity)]
      exact Finset.mem_product.mpr
        ⟨haData.1, taoLargePrimeSourceDyadicPrimeSlice_subset_band x r haData.2⟩)
    (fun a _ _ => taoLargePrimeProbability_nonneg (P x) hP (m' x) a)

/-! ## Final dyadic covariance summation -/

/-- Every ordered covariance block retains the fixed saving
`z^(-1/200000)`, uniformly over the source grid. -/
theorem eventually_forall_taoLargePrimeSourceCovarianceBlockMajorant_le
    {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ x : ℕ in atTop,
      ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      ∀ s ∈ taoLargePrimeSourceDyadicExponents x, r ≤ s →
      taoLargePrimeSourceCovarianceBlockMajorant K x r s ≤
        (4 * taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant + 1) *
          (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
  have hconstant : 0 ≤ taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant := by
    unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
    unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
    unfold taoLargePrimeSourceJointPowerConstant
    positivity
  have habsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := 24576 * K) (k := (3 : ℝ)) (a := (979 / 200000 : ℝ))
      (b := (0 : ℝ)) (mul_nonneg (by norm_num) hK) (by norm_num)
  filter_upwards
    [eventually_forall_card_taoLargePrimeSourceDyadicBand_le_two_mul_div_log,
      eventually_forall_log_taoZ_div_two_hundred_le_log_sourceDyadicScale,
      eventually_taoLargePrimeSourceDyadicScale_bounds, habsorb,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 200))] with
        x hcard hlogLower hscale habsorbX hz
  intro r hr s hs hrs
  let R : ℝ := ((2 ^ r : ℕ) : ℝ)
  let S : ℝ := ((2 ^ s : ℕ) : ℝ)
  let L : ℝ := Real.log (taoZ x)
  let LR : ℝ := Real.log (2 ^ r : ℕ)
  let LS : ℝ := Real.log (2 ^ s : ℕ)
  let A : ℝ := taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hLlarge : (200 : ℝ) ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := by linarith
  have hLRLower : (1 / 200 : ℝ) * L ≤ LR := by
    simpa only [L, LR] using hlogLower r hr
  have hLSLower : (1 / 200 : ℝ) * L ≤ LS := by
    simpa only [L, LS] using hlogLower s hs
  have hLRone : 1 ≤ LR := by nlinarith
  have hLSone : 1 ≤ LS := by nlinarith
  have hLRpos : 0 < LR := zero_lt_one.trans_le hLRone
  have hLSpos : 0 < LS := zero_lt_one.trans_le hLSone
  have hcardR : ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤
      2 * (R / LR) := by simpa only [R, LR] using hcard r hr
  have hcardS : ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) ≤
      2 * (S / LS) := by simpa only [S, LS] using hcard s hs
  have hcardRcoarse : ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤ 2 * R := by
    calc
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) ≤ 2 * (R / LR) := hcardR
      _ ≤ 2 * R := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (div_le_iff₀ hLRpos).2 (by nlinarith)
  have hcardScoarse : ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) ≤ 2 * S := by
    calc
      ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) ≤ 2 * (S / LS) := hcardS
      _ ≤ 2 * S := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (div_le_iff₀ hLSpos).2 (by nlinarith)
  have hRproduct : R * R ^ (-(1001 / 1000 : ℝ)) =
      R ^ (-(1 / 1000 : ℝ)) := by
    calc
      R * R ^ (-(1001 / 1000 : ℝ)) =
          R ^ (1 : ℝ) * R ^ (-(1001 / 1000 : ℝ)) := by
            rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + (-(1001 / 1000 : ℝ))) := by
        rw [Real.rpow_add hRpos]
      _ = R ^ (-(1 / 1000 : ℝ)) := by norm_num
  have hSinverse : S * S ^ (-(1 : ℝ)) = 1 := by
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hSpos.ne'
  have hscaleLowerR : (taoZ x) ^ (1 / 200 : ℝ) ≤ R := by
    simpa only [R] using (hscale r hr).1
  have hscaleLowerS : (taoZ x) ^ (1 / 200 : ℝ) ≤ S := by
    simpa only [S] using (hscale s hs).1
  have hdecayR : R ^ (-(1 / 1000 : ℝ)) ≤
      (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
    calc
      R ^ (-(1 / 1000 : ℝ)) ≤
          ((taoZ x) ^ (1 / 200 : ℝ)) ^ (-(1 / 1000 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos (taoZ_pos x) _) hscaleLowerR (by norm_num)
      _ = (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
        rw [← Real.rpow_mul (taoZ_pos x).le]
        congr 1
        norm_num
  have hRstrongIdentity : R ^ (1 / 50 : ℝ) / R =
      R ^ (-(49 / 50 : ℝ)) := by
    calc
      R ^ (1 / 50 : ℝ) / R = R ^ (1 / 50 : ℝ) / R ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = R ^ ((1 / 50 : ℝ) - 1) := by rw [Real.rpow_sub hRpos]
      _ = R ^ (-(49 / 50 : ℝ)) := by norm_num
  have hSstrongIdentity : S ^ (1 / 50 : ℝ) / S =
      S ^ (-(49 / 50 : ℝ)) := by
    calc
      S ^ (1 / 50 : ℝ) / S = S ^ (1 / 50 : ℝ) / S ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = S ^ ((1 / 50 : ℝ) - 1) := by rw [Real.rpow_sub hSpos]
      _ = S ^ (-(49 / 50 : ℝ)) := by norm_num
  have hstrongR : R ^ (-(49 / 50 : ℝ)) ≤
      (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
    calc
      R ^ (-(49 / 50 : ℝ)) ≤
          ((taoZ x) ^ (1 / 200 : ℝ)) ^ (-(49 / 50 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos (taoZ_pos x) _) hscaleLowerR (by norm_num)
      _ = (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
        rw [← Real.rpow_mul (taoZ_pos x).le]
        congr 1
        norm_num
  have hstrongS : S ^ (-(49 / 50 : ℝ)) ≤
      (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
    calc
      S ^ (-(49 / 50 : ℝ)) ≤
          ((taoZ x) ^ (1 / 200 : ℝ)) ^ (-(49 / 50 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos (taoZ_pos x) _) hscaleLowerS (by norm_num)
      _ = (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
        rw [← Real.rpow_mul (taoZ_pos x).le]
        congr 1
        norm_num
  have himproved :
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
          (A * R ^ (-(1001 / 1000 : ℝ)) * S ^ (-(1 : ℝ))) ≤
        4 * A * (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
    calc
      ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
          (A * R ^ (-(1001 / 1000 : ℝ)) * S ^ (-(1 : ℝ))) ≤
        (2 * R) * (2 * S) *
          (A * R ^ (-(1001 / 1000 : ℝ)) * S ^ (-(1 : ℝ))) := by
            gcongr
      _ = 4 * A * (R * R ^ (-(1001 / 1000 : ℝ))) *
          (S * S ^ (-(1 : ℝ))) := by ring
      _ = 4 * A * R ^ (-(1 / 1000 : ℝ)) := by
        rw [hRproduct, hSinverse]
        ring
      _ ≤ 4 * A * (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdecayR
          (mul_nonneg (by norm_num) hconstant)
  have hexceptionCoarse :
      (K * (R ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
        ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          S ^ (1 / 50 : ℝ))) *
          (6144 * L ^ 3 / (R * S)) ≤
        (24576 * K) * L ^ (3 : ℕ) *
          (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
    have hinside : R ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
        ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          S ^ (1 / 50 : ℝ) ≤
        4 * R * S * (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
      calc
        R ^ (1 / 50 : ℝ) *
              ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
            ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
              S ^ (1 / 50 : ℝ) ≤
          R ^ (1 / 50 : ℝ) * (2 * S) +
            (2 * R) * S ^ (1 / 50 : ℝ) := by gcongr
        _ = 2 * R * S *
              (R ^ (1 / 50 : ℝ) / R + S ^ (1 / 50 : ℝ) / S) := by
          field_simp [ne_of_gt hRpos, ne_of_gt hSpos]
        _ = 2 * R * S *
              (R ^ (-(49 / 50 : ℝ)) + S ^ (-(49 / 50 : ℝ))) := by
          rw [hRstrongIdentity, hSstrongIdentity]
        _ ≤ 2 * R * S *
              (2 * (taoZ x) ^ (-(49 / 10000 : ℝ))) := by
          gcongr
          linarith
        _ = 4 * R * S * (taoZ x) ^ (-(49 / 10000 : ℝ)) := by ring
    calc
      (K * (R ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
        ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          S ^ (1 / 50 : ℝ))) * (6144 * L ^ 3 / (R * S)) ≤
        (K * (4 * R * S * (taoZ x) ^ (-(49 / 10000 : ℝ)))) *
          (6144 * L ^ 3 / (R * S)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hinside hK) (by positivity)
      _ = (24576 * K) * L ^ (3 : ℕ) *
          (taoZ x) ^ (-(49 / 10000 : ℝ)) := by
        field_simp [ne_of_gt hRpos, ne_of_gt hSpos]
        ring
  have habsorbNat :
      (24576 * K) * L ^ (3 : ℕ) /
          (taoZ x) ^ (979 / 200000 : ℝ) ≤ 1 := by
    have hx := habsorbX
    rw [Real.rpow_zero, div_one] at hx
    rw [show L ^ (3 : ℕ) = L ^ (3 : ℝ) from
      (Real.rpow_natCast L 3).symm]
    simpa only [L] using hx
  have hsplit : (taoZ x) ^ (-(49 / 10000 : ℝ)) =
      (1 / (taoZ x) ^ (979 / 200000 : ℝ)) *
        (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg (taoZ_pos x).le,
      ← Real.rpow_add (taoZ_pos x)]
    congr 1
    norm_num
  have hexception :
      (K * (R ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
        ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          S ^ (1 / 50 : ℝ))) *
          (6144 * L ^ 3 / (R * S)) ≤
        (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
    calc
      _ ≤ (24576 * K) * L ^ (3 : ℕ) *
          (taoZ x) ^ (-(49 / 10000 : ℝ)) := hexceptionCoarse
      _ = ((24576 * K) * L ^ (3 : ℕ) /
          (taoZ x) ^ (979 / 200000 : ℝ)) *
            (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
        rw [hsplit]
        ring
      _ ≤ 1 * (taoZ x) ^ (-(1 / 200000 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right habsorbNat
          (Real.rpow_nonneg (taoZ_pos x).le _)
      _ = (taoZ x) ^ (-(1 / 200000 : ℝ)) := one_mul _
  rw [taoLargePrimeSourceCovarianceBlockMajorant]
  change
    ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) *
          (A * R ^ (-(1001 / 1000 : ℝ)) * S ^ (-(1 : ℝ))) +
      (K * (R ^ (1 / 50 : ℝ) *
          ((taoDyadicPrimeBand (2 ^ s)).card : ℝ) +
        ((taoDyadicPrimeBand (2 ^ r)).card : ℝ) *
          S ^ (1 / 50 : ℝ))) * (6144 * L ^ 3 / (R * S)) ≤
      (4 * A + 1) * (taoZ x) ^ (-(1 / 200000 : ℝ))
  calc
    _ ≤ 4 * A * (taoZ x) ^ (-(1 / 200000 : ℝ)) +
        (taoZ x) ^ (-(1 / 200000 : ℝ)) := add_le_add himproved hexception
    _ = (4 * A + 1) * (taoZ x) ^ (-(1 / 200000 : ℝ)) := by ring

/-- The complete ordered off-diagonal covariance sum over source dyadic
scales is `O(H)`; the tiny block power saving absorbs both the scale count
and the second factor of `H`. -/
theorem eventually_sum_taoLargePrimeCovariance_adaptive_orderedSourceDyadicScales_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => r ≤ s),
          ∑ a ∈ taoLargeAntiSieveIndices
              (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
            ∑ b ∈ (taoLargeAntiSieveIndices
              (2 ^ s - 1) (2 * 2 ^ s - 1) (H x)).filter
                (fun b => b.2 ≠ a.2),
              taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
        (H x : ℝ) := by
  obtain ⟨K, hK, hblocks⟩ :=
    exists_eventually_forall_sum_taoLargePrimeCovariance_adaptive_sourceTwoBand_le
      hC hburgess hscale H m' hH
  let B : ℝ := 4 * taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant + 1
  have hA : 0 ≤ taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant := by
    unfold taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant
    unfold taoLargePrimeMixedAdaptiveSourceJointPowerConstant
    unfold taoLargePrimeSourceJointPowerConstant
    positivity
  have hB : 0 < B := by dsimp only [B]; linarith
  have hmajorant :=
    eventually_forall_taoLargePrimeSourceCovarianceBlockMajorant_le hK.le
  have hlogAbsorb := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := 16 * B) (k := (2 : ℝ)) (a := (1 / 400000 : ℝ))
      (b := (0 : ℝ)) (mul_nonneg (by norm_num) hB.le) (by norm_num)
  have hlengthAbsorb := eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
    (C := (1 : ℝ)) (δ := (1 / 400000 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hblocks, hmajorant,
    eventually_card_taoLargePrimeSourceDyadicExponents_cast_le_log,
    hlogAbsorb, hlengthAbsorb, hH,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with
      x hblocksX hmajorantX hcardX hlogAbsorbX hlengthAbsorbX hHX hz
  intro hP
  let L : ℝ := Real.log (taoZ x)
  let Zδ : ℝ := (taoZ x) ^ (1 / 200000 : ℝ)
  let Zhalf : ℝ := (taoZ x) ^ (1 / 400000 : ℝ)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hZδpos : 0 < Zδ := by
    dsimp only [Zδ]
    exact Real.rpow_pos_of_pos (taoZ_pos x) _
  have hZhalfPos : 0 < Zhalf := by
    dsimp only [Zhalf]
    exact Real.rpow_pos_of_pos (taoZ_pos x) _
  have hlogAbsorbNat : 16 * B * L ^ (2 : ℕ) ≤ Zhalf := by
    have hx := hlogAbsorbX
    rw [Real.rpow_zero, div_one] at hx
    have hx' : 16 * B * L ^ (2 : ℕ) / Zhalf ≤ 1 := by
      rw [show L ^ (2 : ℕ) = L ^ (2 : ℝ) from
        (Real.rpow_natCast L 2).symm]
      simpa only [L, Zhalf] using hx
    have := (div_le_iff₀ hZhalfPos).mp hx'
    simpa only [one_mul] using this
  have hlengthPower : (H x : ℝ) ≤ Zhalf := by
    calc
      (H x : ℝ) ≤ (taoTypicalLengthCutoff x : ℝ) := by
        exact_mod_cast hHX
      _ = 1 * (taoTypicalLengthCutoff x : ℝ) := by ring
      _ ≤ Zhalf := by simpa only [Zhalf] using hlengthAbsorbX
  have hhalfSquare : Zhalf * Zhalf = Zδ := by
    dsimp only [Zhalf, Zδ]
    rw [← Real.rpow_add (taoZ_pos x)]
    congr 1
    norm_num
  have hcoefficient : (4 * L) ^ (2 : ℕ) * B * (H x : ℝ) ≤ Zδ := by
    calc
      (4 * L) ^ (2 : ℕ) * B * (H x : ℝ) =
          (16 * B * L ^ (2 : ℕ)) * (H x : ℝ) := by ring
      _ ≤ Zhalf * Zhalf :=
        mul_le_mul hlogAbsorbNat hlengthPower (by positivity) hZhalfPos.le
      _ = Zδ := hhalfSquare
  have hsumBlocks :
      (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => r ≤ s),
          ∑ a ∈ taoLargeAntiSieveIndices
              (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
            ∑ b ∈ (taoLargeAntiSieveIndices
              (2 ^ s - 1) (2 * 2 ^ s - 1) (H x)).filter
                (fun b => b.2 ≠ a.2),
              taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => r ≤ s),
          ((H x - 1 : ℕ) : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro s hsFilter
    have hsData := Finset.mem_filter.mp hsFilter
    simpa only [taoLargePrimeSourceCovarianceBlockMajorant] using
      hblocksX r hr s hsData.1 hsData.2 hP
  have hHsub : (((H x - 1 : ℕ) : ℝ) : ℝ) ≤ (H x : ℝ) := by
    exact_mod_cast Nat.sub_le (H x) 1
  have htermNonneg : 0 ≤
      ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by positivity
  calc
    (∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => r ≤ s),
          ∑ a ∈ taoLargeAntiSieveIndices
              (2 ^ r - 1) (2 * 2 ^ r - 1) (H x),
            ∑ b ∈ (taoLargeAntiSieveIndices
              (2 ^ s - 1) (2 * 2 ^ s - 1) (H x)).filter
                (fun b => b.2 ≠ a.2),
              taoLargePrimeCovariance (P x) hP (m' x) a b) ≤
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => r ≤ s),
          ((H x - 1 : ℕ) : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s := hsumBlocks
    _ ≤ ∑ _r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ _s ∈ (taoLargePrimeSourceDyadicExponents x).filter (fun s => _r ≤ s),
          (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hsFilter
      have hsData := Finset.mem_filter.mp hsFilter
      have hmaj := hmajorantX r hr s hsData.1 hsData.2
      have hmaj' : taoLargePrimeSourceCovarianceBlockMajorant K x r s ≤
          B * (Zδ)⁻¹ := by
        simpa only [B, Zδ, Real.rpow_neg (taoZ_pos x).le] using hmaj
      have hmajNonneg : 0 ≤
          taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
        rw [taoLargePrimeSourceCovarianceBlockMajorant]
        positivity
      calc
        (((H x - 1 : ℕ) : ℝ) : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s ≤
          (H x : ℝ) ^ 2 *
            taoLargePrimeSourceCovarianceBlockMajorant K x r s := by
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (by positivity) hHsub 2) hmajNonneg
        _ ≤ (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) :=
          mul_le_mul_of_nonneg_left hmaj' (sq_nonneg _)
    _ ≤ ∑ _r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ _s ∈ taoLargePrimeSourceDyadicExponents x,
          (H x : ℝ) ^ 2 * (B * (Zδ)⁻¹) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => htermNonneg)
    _ = ((taoLargePrimeSourceDyadicExponents x).card : ℝ) ^ 2 *
        ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by simp; ring
    _ ≤ (4 * L) ^ 2 * ((H x : ℝ) ^ 2 * (B * (Zδ)⁻¹)) := by
      have hcardNonneg : 0 ≤
          ((taoLargePrimeSourceDyadicExponents x).card : ℝ) := by positivity
      have hcardSq := pow_le_pow_left₀ hcardNonneg
        (by simpa only [L] using hcardX) 2
      exact mul_le_mul_of_nonneg_right hcardSq htermNonneg
    _ = (H x : ℝ) *
        (((4 * L) ^ 2 * B * (H x : ℝ)) * (Zδ)⁻¹) := by ring
    _ ≤ (H x : ℝ) * (Zδ * (Zδ)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)
    _ = (H x : ℝ) := by
      rw [mul_inv_cancel₀ hZδpos.ne', mul_one]

end

end Tao2026

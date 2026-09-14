import Tao2026.BadIntervalTypicalAntiSieve
import Tao2026.BadIntervalPrimeTupleUniform

/-!
# Uniform Proposition 6.6 and its finite counting interface

The source applies Proposition 6.6 simultaneously to every admissible length
and every smooth remainder at a fixed ambient scale.  Sequence-wise eventual
bounds are not sufficient for that summation.  This module makes the actual
quantifier order explicit, retaining one Burgess-dependent constant before
the eventual `x`, `H`, and `m'` quantifiers.

It also records the exact conversion between the probability of the typical
event and the cardinality of the corresponding subset of the finite Cartesian
prime-band support.
-/

namespace Tao2026

open Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

noncomputable section

/-- Supported prime tuples for which the source interval is typical. -/
def taoPrimeTupleTypicalSupport
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime m' : ℕ) :
    Finset TaoPrimeTuple :=
  (taoPrimeTupleSupport P).filter fun ω =>
    TaoPrimeTupleTypicalEvent x H lowerPrime upperPrime m' ω

theorem mem_taoPrimeTupleTypicalSupport
    {P : Fin 1001 → ℕ} {x H lowerPrime upperPrime m' : ℕ}
    {ω : TaoPrimeTuple} :
    ω ∈ taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m' ↔
      ω ∈ taoPrimeTupleSupport P ∧
        TaoPrimeTupleTypicalEvent x H lowerPrime upperPrime m' ω := by
  simp [taoPrimeTupleTypicalSupport]

/-- The typical probability is exactly the supported tuple count times the
common atom of the finite product law. -/
theorem taoPrimeTupleTypicalProbability_eq_card_mul_atom
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) :
    taoPrimeTupleTypicalProbability P hP x H lowerPrime upperPrime m' =
      (taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card *
        (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
  rw [taoPrimeTupleTypicalProbability,
    taoPrimeTupleMeasure_apply_eq_card_mul_atom]
  congr 2

/-- Real-valued cardinality-ratio form of the same exact finite identity. -/
theorem taoPrimeTupleTypicalProbability_toReal_eq_card_div
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) :
    (taoPrimeTupleTypicalProbability P hP x H lowerPrime upperPrime m').toReal =
      (taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card /
        ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
  rw [taoPrimeTupleTypicalProbability_eq_card_mul_atom]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_prod]
  rw [div_eq_mul_inv]

/-- A probability upper bound gives the corresponding finite tuple-count
upper bound after multiplying by the exact product of band cardinalities. -/
theorem card_taoPrimeTupleTypicalSupport_le_of_probability
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) {B : ℝ}
    (hprob :
      (taoPrimeTupleTypicalProbability P hP x H lowerPrime upperPrime m').toReal ≤ B) :
    ((taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card : ℝ) ≤
      B * ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
  have hprodPos : 0 < ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
    exact Finset.prod_pos fun j _ => by
      exact_mod_cast (Finset.card_pos.mpr (hP j))
  rw [taoPrimeTupleTypicalProbability_toReal_eq_card_div] at hprob
  exact (div_le_iff₀ hprodPos).mp hprob

/-! ## Uniform large-prime moments -/

/-- The literal source mean bound is eventually simultaneous in the interval
length and remainder.  This is a logical uniformization of the already proved
sequence-form Proposition 6.7 endpoint. -/
theorem eventually_forall_taoLargePrimeMean_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      H ≤ taoTypicalLengthCutoff x →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoLargePrimeMean (P x) hP
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) H m' ≤
          2000000 * (H : ℝ) := by
  let R : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    a.1 ≤ taoTypicalLengthCutoff x
  let Q : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoLargePrimeMean (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) a.1 a.2 ≤
        2000000 * (a.1 : ℝ)
  have hne : ∀ᶠ x : ℕ in atTop, ∃ a : ℕ × ℕ, R x a :=
    Filter.Eventually.of_forall fun x => ⟨(0, 0), Nat.zero_le _⟩
  have hselector : ∀ f : ℕ → ℕ × ℕ,
      (∀ᶠ x : ℕ in atTop, R x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    simpa only [R, Q] using
      eventually_taoLargePrimeMean_sourceCutoffs_le hC hburgess hscale
        (fun x => (f x).1) (fun x => (f x).2) hf
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx H m' hHm
  exact hx (H, m') hHm

/-- The completed source variance bound is likewise simultaneous in the
length and remainder. -/
theorem eventually_forall_taoLargePrimeVariance_sourceCutoffs_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      H ≤ taoTypicalLengthCutoff x →
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
        taoLargePrimeVariance (P x) hP
            (taoLargePrimeSourceLowerCutoff x)
            (taoLargePrimeSourceUpperCutoff x) H m' ≤
          2000001 * (H : ℝ) := by
  let R : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    a.1 ≤ taoTypicalLengthCutoff x
  let Q : ℕ → (ℕ × ℕ) → Prop := fun x a =>
    ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      taoLargePrimeVariance (P x) hP
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) a.1 a.2 ≤
        2000001 * (a.1 : ℝ)
  have hne : ∀ᶠ x : ℕ in atTop, ∃ a : ℕ × ℕ, R x a :=
    Filter.Eventually.of_forall fun x => ⟨(0, 0), Nat.zero_le _⟩
  have hselector : ∀ f : ℕ → ℕ × ℕ,
      (∀ᶠ x : ℕ in atTop, R x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    simpa only [R, Q] using
      eventually_taoLargePrimeVariance_sourceCutoffs_le hC hburgess hscale
        (fun x => (f x).1) (fun x => (f x).2) hf
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx H m' hHm
  exact hx (H, m') hHm

/-! ## Uniform small-prime moment -/

/-- The elementary principal majorant is eventually bounded at the source
scale simultaneously for every interval length. -/
theorem eventually_forall_taoSmallPrimePrincipalMertensMajorant_le_logPower :
    ∀ᶠ x : ℕ in atTop, ∀ H : ℕ,
      taoSmallPrimePrincipalMertensMajorant x H ≤
        taoSmallPrimePrincipalLogPowerConstant *
          (H : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ) := by
  let R : ℕ → ℕ → Prop := fun _ _ => True
  let Q : ℕ → ℕ → Prop := fun x H =>
    taoSmallPrimePrincipalMertensMajorant x H ≤
      taoSmallPrimePrincipalLogPowerConstant *
        (H : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ)
  have hne : ∀ᶠ x : ℕ in atTop, ∃ H, R x H :=
    Filter.Eventually.of_forall fun _ => ⟨0, trivial⟩
  have hselector : ∀ f : ℕ → ℕ,
      (∀ᶠ x : ℕ in atTop, R x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f _
    exact eventually_taoSmallPrimePrincipalMertensMajorant_le_logPower f
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx H
  exact hx H trivial

/-- A canonical Burgess-dependent constant for the uniform exceptional
character second moment.  Naming the witness makes its independence from all
later dyadic-scale choices explicit. -/
def taoUniformExceptionalSecondMomentConstant
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) : ℝ :=
  Classical.choose
    (exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess)

theorem taoUniformExceptionalSecondMomentConstant_pos
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    0 < taoUniformExceptionalSecondMomentConstant hC hburgess :=
  (Classical.choose_spec
    (exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess)).1

theorem eventually_conductorExceptional_secondMoment_le_uniformConstant
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∀ᶠ Z : ℕ in atTop,
      ∀ D : Finset ℕ, IsAdmissibleTaoExceptionalConductorSet D Z →
        ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤
            taoUniformExceptionalSecondMomentConstant hC hburgess :=
  (Classical.choose_spec
    (exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess)).2

/-- One Burgess-dependent constant controls the complete small-prime
fiftieth moment simultaneously for every length and every remainder. -/
theorem eventually_forall_taoSmallPrimeFiftiethMoment_le_principalMajorant_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
          taoSmallPrimePrincipalMertensMajorant x H := by
  have hscaleNat : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j := by
    filter_upwards
      [eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale] with
        x hx j
    have hfloor : (taoZPowerFloor (9 / 10 : ℝ) x : ℝ) ≤
        (taoZ x) ^ (9 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
    exact_mod_cast hfloor.trans (hx j)
  let K := taoUniformExceptionalSecondMomentConstant hC hburgess
  have hK : 0 < K := taoUniformExceptionalSecondMomentConstant_pos hC hburgess
  have huniform :=
    eventually_conductorExceptional_secondMoment_le_uniformConstant hC hburgess
  rw [eventually_atTop] at huniform
  obtain ⟨Z₀, hZ₀⟩ := huniform
  have hlower : ∀ᶠ x : ℕ in atTop,
      Z₀ ≤ taoZPowerFloor (9 / 10 : ℝ) x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 9 / 10)).eventually (eventually_ge_atTop Z₀)
  have hseparation :=
    eventually_taoSmallAntiSievePrimeCutoff_lt_of_lowerScale P hscaleNat
  have hcutoffPos : ∀ᶠ x : ℕ in atTop,
      0 < taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_gt_atTop 0)
  have hcutoffOne : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 1)
  filter_upwards [
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_burgessRange,
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_lowerScale,
    hscaleNat, hlower, hseparation, hcutoffPos, hcutoffOne] with
      x hrange hcutPower hxscale hxlower hsep hcutPos hcutOne H m'
  obtain ⟨j, hj, hmoment⟩ :=
    exists_taoSmallPrimeFiftiethMoment_le_exceptional_add_elementary
      (P x) (hP x) x H m' (fun j hj => hsep j) hcutPos
  have hadmissible : IsAdmissibleTaoExceptionalConductorSet
      (taoSmallPrimeExceptionalConductors x H) (P x j) :=
    isAdmissible_taoSmallPrimeExceptionalConductors
      (hrange (P x j) (hxscale j))
  have hexceptionalMoment :
      (∑ d ∈ taoSmallPrimeExceptionalConductors x H,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ 2) ≤ K :=
    hZ₀ (P x j) (hxlower.trans (hxscale j)) _ hadmissible
  have hexceptional :
      taoSmallPrimeExceptionalConductorSum (P x) x H j ≤
        K * taoSmallPrimePrincipalMertensMajorant x H := by
    calc
      taoSmallPrimeExceptionalConductorSum (P x) x H j ≤
          (2 : ℝ) ^ (50 : ℕ) * K *
            ((H : ℝ) ^ (50 : ℕ) *
              ((50 : ℝ) ^ (50 : ℕ) * 50 *
                (Real.log 4 *
                    (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                  Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) :=
        taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_unionMoment
          (P x) x H j hK.le hcutPos hexceptionalMoment
      _ = K * taoSmallPrimePrincipalMertensMajorant x H := by
        rw [taoSmallPrimePrincipalMertensMajorant]
        ac_rfl
  have herror :=
    taoSmallPrimeTotientErrorMajorant_le_principalMertensMajorant
      (P x) x H j hcutOne (hcutPower.trans (hxscale j))
  calc
    taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          taoSmallPrimeExceptionalConductorSum (P x) x H j +
            taoSmallPrimeTotientErrorMajorant (P x) x H j) := hmoment
    _ ≤ 1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          K * taoSmallPrimePrincipalMertensMajorant x H +
            taoSmallPrimePrincipalMertensMajorant x H) := by gcongr
     _ = 1000 * (2 + K) * taoSmallPrimePrincipalMertensMajorant x H := by ring

/-- Existential compatibility wrapper for the named uniform constant. -/
theorem exists_eventually_forall_taoSmallPrimeFiftiethMoment_le_principalMajorant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (2 + K) * taoSmallPrimePrincipalMertensMajorant x H := by
  refine ⟨taoUniformExceptionalSecondMomentConstant hC hburgess,
    taoUniformExceptionalSecondMomentConstant_pos hC hburgess, ?_⟩
  exact
    eventually_forall_taoSmallPrimeFiftiethMoment_le_principalMajorant_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP

/-- The named, scale-independent constant in the logarithmic small-prime
moment bound. -/
def taoSmallPrimeUniformLogPowerConstant
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) : ℝ :=
  1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
    taoSmallPrimePrincipalLogPowerConstant

theorem taoSmallPrimeUniformLogPowerConstant_pos
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    0 < taoSmallPrimeUniformLogPowerConstant hC hburgess := by
  unfold taoSmallPrimeUniformLogPowerConstant
  exact mul_pos (mul_pos (by norm_num)
      (by linarith [taoUniformExceptionalSecondMomentConstant_pos hC hburgess]))
    taoSmallPrimePrincipalLogPowerConstant_pos

/-- Uniform source-scale form with the named scale-independent constant. -/
theorem eventually_forall_taoSmallPrimeFiftiethMoment_le_logPower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
          (H : ℝ) ^ (50 : ℕ) *
          Real.log (taoZ x) ^ (50 : ℕ) := by
  have hmoment :=
    eventually_forall_taoSmallPrimeFiftiethMoment_le_principalMajorant_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hmoment,
    eventually_forall_taoSmallPrimePrincipalMertensMajorant_le_logPower] with
      x hmomentX hmajorantX H m'
  calc
    taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
          taoSmallPrimePrincipalMertensMajorant x H :=
      hmomentX H m'
    _ ≤ 1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
        (taoSmallPrimePrincipalLogPowerConstant *
          (H : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (hmajorantX H)
        (mul_nonneg (by norm_num)
          (by linarith [taoUniformExceptionalSecondMomentConstant_pos hC hburgess]))
    _ = taoSmallPrimeUniformLogPowerConstant hC hburgess *
        (H : ℝ) ^ (50 : ℕ) *
        Real.log (taoZ x) ^ (50 : ℕ) := by
      unfold taoSmallPrimeUniformLogPowerConstant
      ring

/-- Existential compatibility wrapper for the named logarithmic constant. -/
theorem exists_eventually_forall_taoSmallPrimeFiftiethMoment_le_logPower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        A * (H : ℝ) ^ (50 : ℕ) *
          Real.log (taoZ x) ^ (50 : ℕ) := by
  exact ⟨taoSmallPrimeUniformLogPowerConstant hC hburgess,
    taoSmallPrimeUniformLogPowerConstant_pos hC hburgess,
    eventually_forall_taoSmallPrimeFiftiethMoment_le_logPower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP⟩

/-! ## Uniform source tails -/

/-- Uniform Markov bound for the small-prime branch at the literal source
threshold, using the named scale-independent constant. -/
theorem eventually_forall_taoSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ, 1 ≤ H →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
                (8 * iteratedLog x) <
            taoSmallPrimeContribution x H m' ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (50 : ℕ) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  have hmoment :=
    eventually_forall_taoSmallPrimeFiftiethMoment_le_logPower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hmoment,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmomentX hz hiter H m' hH
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H : ℝ) * L ^ (2 : ℕ) / (8 * I)
  let Q : ℝ := (taoPrimeTupleMeasure (P x) (hP x)).real
    {ω | T < taoSmallPrimeContribution x H m' ω}
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hmarkov :=
    taoSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
      (P x) (hP x) x H m' (T := T) hTpos.le
  have htail : T ^ (50 : ℕ) * Q ≤
      A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by
    exact hmarkov.trans (by simpa only [Q, T, L] using hmomentX H m')
  have hQ : Q ≤
      (A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 50)]
    simpa only [mul_comm] using htail
  change Q ≤ A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ)
  calc
    Q ≤ (A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := hQ
    _ = A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']

/-- Existential compatibility wrapper for the named small-prime tail
constant. -/
theorem exists_eventually_forall_taoSmallPrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ, 1 ≤ H →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
                (8 * iteratedLog x) <
            taoSmallPrimeContribution x H m' ω} ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (50 : ℕ) := by
  exact ⟨taoSmallPrimeUniformLogPowerConstant hC hburgess,
    taoSmallPrimeUniformLogPowerConstant_pos hC hburgess,
    eventually_forall_taoSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP⟩

/-- Uniform Chebyshev bound for the large-prime branch at the literal source
threshold above the completed mean. -/
theorem eventually_forall_taoLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | 2000000 * (H : ℝ) +
                (H : ℝ) * Real.log (taoZ x) /
                  (8 * iteratedLog x) <
            taoLargePrimeContribution
              (taoLargePrimeSourceLowerCutoff x)
              (taoLargePrimeSourceUpperCutoff x) H m' ω} ≤
        2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hmean := eventually_forall_taoLargePrimeMean_sourceCutoffs_le
    hC hburgess hscale
  have hvariance := eventually_forall_taoLargePrimeVariance_sourceCutoffs_le
    hC hburgess hscale
  filter_upwards [hmean, hvariance,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmeanX hvarianceX hz hiter H m' hH hHcut
  let μ := taoPrimeTupleMeasure (P x) (hP x)
  let X : TaoPrimeTuple → ℝ := taoLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) H m'
  let M : ℝ := taoLargePrimeMean (P x) (hP x)
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) H m'
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H : ℝ) * L / (8 * I)
  let Q : ℝ := μ.real {ω | 2000000 * (H : ℝ) + T < X ω}
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hsubset :
      {ω | 2000000 * (H : ℝ) + T < X ω} ⊆
        {ω | M + T ≤ X ω} := by
    intro ω hω
    change 2000000 * (H : ℝ) + T < X ω at hω
    have hm := hmeanX H m' hHcut (hP x)
    change M ≤ 2000000 * (H : ℝ) at hm
    change M + T ≤ X ω
    linarith
  have hchebyshev :=
    taoLargePrimeContribution_upperTail_measureReal_mul_sq_le_variance
      (P x) (hP x) (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) H m' (T := T) hTpos.le
  have htail : T ^ (2 : ℕ) * Q ≤ 2000001 * (H : ℝ) := by
    calc
      T ^ (2 : ℕ) * Q ≤
          T ^ (2 : ℕ) * μ.real {ω | M + T ≤ X ω} := by
        exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
          (sq_nonneg T)
      _ ≤ taoLargePrimeVariance (P x) (hP x)
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) H m' := by
        simpa only [μ, X, M] using hchebyshev
      _ ≤ 2000001 * (H : ℝ) := hvarianceX H m' hHcut (hP x)
  have hQ : Q ≤ 2000001 * (H : ℝ) / T ^ (2 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 2)]
    simpa only [mul_comm] using htail
  change Q ≤ 2000001 * (8 * I) ^ (2 : ℕ) /
    ((H : ℝ) * L ^ (2 : ℕ))
  calc
    Q ≤ 2000001 * (H : ℝ) / T ^ (2 : ℕ) := hQ
    _ = 2000001 * (8 * I) ^ (2 : ℕ) /
        ((H : ℝ) * L ^ (2 : ℕ)) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']

/-! ## Uniform Proposition 6.6 -/

/-- The named scale-independent constant bounds the three-branch anti-sieve
event simultaneously for all source-admissible lengths and remainders. -/
theorem eventually_forall_measureReal_taoSourceAntiSieveLargeEvent_le_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoSourceAntiSieveLargeEvent x H m' ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  have hsmall :=
    eventually_forall_taoSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  have hlarge :=
    eventually_forall_taoLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hsmall, hlarge,
    eventually_taoExceptionalPrimeLargeEvent_eq_empty] with
      x hsmallX hlargeX hexceptional H m' hH hHcut
  let E : Set TaoPrimeTuple :=
    {ω | TaoExceptionalPrimeLargeEvent x H m' ω}
  let S : Set TaoPrimeTuple :=
    {ω | (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) < taoSmallPrimeContribution x H m' ω}
  let L : Set TaoPrimeTuple :=
    {ω | 2000000 * (H : ℝ) +
          (H : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
        taoLargePrimeContribution
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) H m' ω}
  have hE : E = ∅ := by
    simpa only [E] using hexceptional H m' hH hHcut
  have hunion :
      {ω | TaoSourceAntiSieveLargeEvent x H m' ω} = (E ∪ S) ∪ L := by
    ext ω
    simp only [TaoSourceAntiSieveLargeEvent, E, S, L,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hunion]
  calc
    (taoPrimeTupleMeasure (P x) (hP x)).real ((E ∪ S) ∪ L) ≤
        (taoPrimeTupleMeasure (P x) (hP x)).real (E ∪ S) +
          (taoPrimeTupleMeasure (P x) (hP x)).real L :=
      measureReal_union_le _ _
    _ ≤ ((taoPrimeTupleMeasure (P x) (hP x)).real E +
          (taoPrimeTupleMeasure (P x) (hP x)).real S) +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      gcongr
      exact measureReal_union_le _ _
    _ = (taoPrimeTupleMeasure (P x) (hP x)).real S +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      rw [hE]
      simp
    _ ≤ A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
      exact add_le_add (by simpa only [S] using hsmallX H m' hH)
        (by simpa only [L] using hlargeX H m' hH hHcut)

/-- Existential compatibility wrapper for the named anti-sieve constant. -/
theorem exists_eventually_forall_measureReal_taoSourceAntiSieveLargeEvent_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoSourceAntiSieveLargeEvent x H m' ω} ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  exact ⟨taoSmallPrimeUniformLogPowerConstant hC hburgess,
    taoSmallPrimeUniformLogPowerConstant_pos hC hburgess,
    eventually_forall_measureReal_taoSourceAntiSieveLargeEvent_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP⟩

/-- The named scale-independent constant in source-facing Proposition 6.6. -/
def taoPrimeTupleTypicalUniformSourceConstant
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) : ℝ :=
  taoSmallPrimeUniformLogPowerConstant hC hburgess + 2000001

theorem taoPrimeTupleTypicalUniformSourceConstant_pos
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    0 < taoPrimeTupleTypicalUniformSourceConstant hC hburgess := by
  unfold taoPrimeTupleTypicalUniformSourceConstant
  linarith [taoSmallPrimeUniformLogPowerConstant_pos hC hburgess]

/-- Uniform source-facing Proposition 6.6 with a constant independent of the
dyadic scale family. -/
theorem eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleTypicalProbability (P x) (hP x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  let B := taoPrimeTupleTypicalUniformSourceConstant hC hburgess
  have hanti :=
    eventually_forall_measureReal_taoSourceAntiSieveLargeEvent_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hanti,
    eventually_taoPrimeTupleTypicalEvent_imp_taoSourceAntiSieveLargeEvent,
    eventually_taoTypicalLengthCutoff_cast_le_log_taoZ_pow_fortyEight,
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with
      x hantiX hinclusion hcutoff hiterX hlogZ H m' hH hHcut
  have hmeasure :
      (taoPrimeTupleTypicalProbability (P x) (hP x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
    change (taoPrimeTupleMeasure (P x) (hP x)).real
        {ω | TaoPrimeTupleTypicalEvent x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m' ω} ≤ _
    exact (measureReal_mono (fun ω hω =>
      hinclusion H (lowerPrime x) m' ω hω)).trans
        (hantiX H m' hH hHcut)
  let L : ℝ := Real.log (taoZ x)
  let J : ℝ := 8 * iteratedLog x
  let D : ℝ := (H : ℝ) * L ^ (2 : ℕ)
  have hLpos : 0 < L := by simpa only [L] using hlogZ
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJone : 1 ≤ J := by dsimp only [J]; nlinarith
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hHcast : (H : ℝ) ≤ L ^ (48 : ℕ) := by
    have hHreal : (H : ℝ) ≤ taoTypicalLengthCutoff x := by
      exact_mod_cast hHcut
    exact hHreal.trans (by simpa only [L] using hcutoff)
  have hdenom : D ≤ L ^ (50 : ℕ) := by
    dsimp only [D]
    calc
      (H : ℝ) * L ^ (2 : ℕ) ≤
          L ^ (48 : ℕ) * L ^ (2 : ℕ) := by gcongr
      _ = L ^ (50 : ℕ) := by ring
  have hfirst : A * J ^ (50 : ℕ) / L ^ (50 : ℕ) ≤
      A * J ^ (50 : ℕ) / D :=
    div_le_div_of_nonneg_left
      (mul_nonneg
        (taoSmallPrimeUniformLogPowerConstant_pos hC hburgess).le
        (pow_nonneg (by linarith [hJone]) 50)) hDpos hdenom
  have hJpow : J ^ (2 : ℕ) ≤ J ^ (50 : ℕ) :=
    pow_le_pow_right₀ hJone (by norm_num : (2 : ℕ) ≤ 50)
  have hsecond : 2000001 * J ^ (2 : ℕ) / D ≤
      2000001 * J ^ (50 : ℕ) / D := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJpow (by norm_num)) hDpos.le
  calc
    (taoPrimeTupleTypicalProbability (P x) (hP x) x H
        (lowerPrime x)
        (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
      A * J ^ (50 : ℕ) / L ^ (50 : ℕ) +
        2000001 * J ^ (2 : ℕ) / D := by
      simpa only [J, L, D] using hmeasure
    _ ≤ A * J ^ (50 : ℕ) / D +
        2000001 * J ^ (50 : ℕ) / D := add_le_add hfirst hsecond
    _ = B * J ^ (50 : ℕ) / D := by
      dsimp only [B, taoPrimeTupleTypicalUniformSourceConstant, A]
      ring
    _ = B * (8 * iteratedLog x) ^ (50 : ℕ) /
        ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := rfl

/-- Existential compatibility wrapper for the named Proposition 6.6
constant. -/
theorem exists_eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleTypicalProbability (P x) (hP x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  exact ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess,
    eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime⟩

/-- Uniform source-facing Proposition 6.6 at the fixed `z^(9/10)` lower
cutoff used by the original finite-row interface. -/
theorem exists_eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleTypicalProbability (P x) (hP x) x H
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  simpa using
    (exists_eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_of_explicitBurgess
      hC hburgess hscale hP (fun x => taoZPowerFloor (9 / 10 : ℝ) x))

/-- Finite-counting form of Proposition 6.6 with the named constant that is
independent of the dyadic scale family. -/
theorem eventually_forall_card_taoPrimeTupleTypicalSupport_le_source_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalSupport (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').card : ℝ) ≤
        (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
  have hprob :=
    eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hprob] with x hx H m' hH hHcut
  exact card_taoPrimeTupleTypicalSupport_le_of_probability
    (P x) (hP x) x H (lowerPrime x)
      (taoLargePrimeSourceUpperCutoff x) m' (hx H m' hH hHcut)

/-- The quantifier-order form used for moving finite scale selections: one
bound is chosen before an arbitrary source scale family. -/
theorem exists_uniformScale_taoPrimeTupleTypicalProbabilityConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (P : ℕ → Fin 1001 → ℕ), TaoPrimeTupleSourceScaleFamily P →
        ∀ hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty,
        ∀ lowerPrime : ℕ → ℕ,
          ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
            1 ≤ H → H ≤ taoTypicalLengthCutoff x →
            (taoPrimeTupleTypicalProbability (P x) (hP x) x H
                (lowerPrime x)
                (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
              B * (8 * iteratedLog x) ^ (50 : ℕ) /
                ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  refine ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess, ?_⟩
  intro P hscale hP lowerPrime
  exact
    eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime

/-- Finite-counting form of the uniform Proposition 6.6 endpoint. -/
theorem exists_eventually_forall_card_taoPrimeTupleTypicalSupport_le_source_withLower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalSupport (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').card : ℝ) ≤
        (B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
  obtain ⟨B, hB, hprob⟩ :=
    exists_eventually_forall_taoPrimeTupleTypicalProbability_toReal_le_source_withLower_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  refine ⟨B, hB, ?_⟩
  filter_upwards [hprob] with x hx H m' hH hHcut
  exact card_taoPrimeTupleTypicalSupport_le_of_probability
    (P x) (hP x) x H (lowerPrime x)
      (taoLargePrimeSourceUpperCutoff x) m' (hx H m' hH hHcut)

/-- Finite-counting form of Proposition 6.6 at the fixed `z^(9/10)` lower
cutoff. -/
theorem exists_eventually_forall_card_taoPrimeTupleTypicalSupport_le_source_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalSupport (P x) x H
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) m').card : ℝ) ≤
        (B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
  exact
    exists_eventually_forall_card_taoPrimeTupleTypicalSupport_le_source_withLower_of_explicitBurgess
      hC hburgess hscale hP (fun x => taoZPowerFloor (9 / 10 : ℝ) x)

end

end Tao2026

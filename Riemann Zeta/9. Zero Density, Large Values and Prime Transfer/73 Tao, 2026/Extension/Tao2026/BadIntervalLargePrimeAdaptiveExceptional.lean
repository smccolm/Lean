import Tao2026.BadIntervalLargePrimeErrorPower
import Tao2026.ExceptionalCharacterCofactorUniform

/-!
# Scale-adaptive exceptional conductors for the large-prime blocks

The fixed exceptional threshold at prime-sum scale `Z` gives a
`Z^(2/125)` cardinality bound.  At the lower end of Tao's modulus range this
is not strong enough to be rewritten as the required `R^(1/50)` bound.

This module uses the general tail conclusion of Lemma 5.1 at the threshold
`max (Z^(-1/125)) (R^(-1/100))`.  The maximum keeps the family inside the
fixed exceptional family to which the uniform squared-moment theorem applies,
while its second term gives the exact `R^(1/50)` cardinality after Chebyshev.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- The scale-adaptive threshold used for a modulus band starting at `R` and
a prime-character average at scale `Z`. -/
def taoLargePrimeAdaptiveThreshold (Z R : ℕ) : ℝ :=
  max (taoExceptionalPrimeCharacterThreshold Z)
    ((R : ℝ) ^ (-(1 / 100 : ℝ)))

theorem taoLargePrimeAdaptiveThreshold_nonneg (Z R : ℕ) :
    0 ≤ taoLargePrimeAdaptiveThreshold Z R := by
  exact le_trans (taoExceptionalPrimeCharacterThreshold_nonneg Z)
    (le_max_left _ _)

theorem taoLargePrimeAdaptiveThreshold_pos {Z R : ℕ} (hR : 0 < R) :
    0 < taoLargePrimeAdaptiveThreshold Z R := by
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hR) _).trans_le
    (le_max_right _ _)

/-- Exceptional primitive characters whose normalized prime sum reaches the
adaptive modulus-band threshold. -/
def taoLargePrimeAdaptiveExceptionalCharacters (q Z R : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  (taoExceptionalPrimitiveCharacters q Z).filter fun χ =>
    taoLargePrimeAdaptiveThreshold Z R ≤
      ‖taoNormalizedPrimeCharacterSum χ Z‖

theorem mem_taoLargePrimeAdaptiveExceptionalCharacters
    {q Z R : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoLargePrimeAdaptiveExceptionalCharacters q Z R ↔
      χ ∈ taoExceptionalPrimitiveCharacters q Z ∧
        taoLargePrimeAdaptiveThreshold Z R ≤
          ‖taoNormalizedPrimeCharacterSum χ Z‖ := by
  simp [taoLargePrimeAdaptiveExceptionalCharacters]

theorem taoLargePrimeAdaptiveExceptionalCharacters_subset
    (q Z R : ℕ) :
    taoLargePrimeAdaptiveExceptionalCharacters q Z R ⊆
      taoExceptionalPrimitiveCharacters q Z := by
  exact Finset.filter_subset _ _

/-- Conductors in `D` carrying at least one adaptively exceptional primitive
character. -/
def taoLargePrimeAdaptiveExceptionalConductorsIn
    (D : Finset ℕ) (Z R : ℕ) : Finset ℕ :=
  D.filter fun q =>
    (taoLargePrimeAdaptiveExceptionalCharacters q Z R).Nonempty

theorem taoLargePrimeAdaptiveExceptionalConductorsIn_subset
    (D : Finset ℕ) (Z R : ℕ) :
    taoLargePrimeAdaptiveExceptionalConductorsIn D Z R ⊆ D := by
  exact Finset.filter_subset _ _

theorem card_taoLargePrimeAdaptiveExceptionalConductorsIn_le
    (D : Finset ℕ) (Z R : ℕ) :
    (taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card ≤
      ∑ q ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card := by
  calc
    (taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card =
        ∑ q ∈ taoLargePrimeAdaptiveExceptionalConductorsIn D Z R, 1 := by simp
    _ ≤ ∑ q ∈ taoLargePrimeAdaptiveExceptionalConductorsIn D Z R,
        (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.one_le_card.mpr (Finset.mem_filter.mp hq).2
    _ ≤ ∑ q ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoLargePrimeAdaptiveExceptionalConductorsIn_subset D Z R)
        (fun _ _ _ => Nat.zero_le _)

private theorem sum_adaptiveCharacter_card_mul_sq_le
    (D : Finset ℕ) (Z R : ℕ) :
    ((∑ q ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card : ℕ) : ℝ) *
        ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤
      ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
  let t : ℝ := (R : ℝ) ^ (-(1 / 100 : ℝ))
  have htNonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hcast :
      ((∑ q ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card : ℕ) : ℝ) *
          t ^ (2 : ℕ) =
        ∑ q ∈ D, ∑ _χ ∈ taoLargePrimeAdaptiveExceptionalCharacters q Z R,
          t ^ (2 : ℕ) := by
    push_cast
    simp [Finset.sum_mul]
  rw [hcast]
  calc
    (∑ q ∈ D, ∑ _χ ∈ taoLargePrimeAdaptiveExceptionalCharacters q Z R,
        t ^ (2 : ℕ)) ≤
      ∑ q ∈ D, ∑ χ ∈ taoLargePrimeAdaptiveExceptionalCharacters q Z R,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro χ hχ
      have hthreshold :=
        (mem_taoLargePrimeAdaptiveExceptionalCharacters.mp hχ).2
      have ht : t ≤ taoLargePrimeAdaptiveThreshold Z R := by
        exact le_max_right _ _
      have hnorm : t ≤ ‖taoNormalizedPrimeCharacterSum χ Z‖ :=
        ht.trans hthreshold
      nlinarith [norm_nonneg (taoNormalizedPrimeCharacterSum χ Z)]
    _ ≤ ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoLargePrimeAdaptiveExceptionalCharacters_subset q Z R)
        (fun _ _ _ => sq_nonneg _)

private theorem adaptive_rpow_inverse_sq {R : ℕ} (hR : 0 < R) :
    (((R : ℝ) ^ (-(1 / 100 : ℝ)))⁻¹) ^ (2 : ℕ) =
      (R : ℝ) ^ (1 / 50 : ℝ) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  rw [Real.rpow_neg hRreal.le, inv_inv]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hRreal.le]
  congr 1
  norm_num

/-- A bounded aggregate exceptional squared moment gives the exact
`R^(1/50)` conductor count at the adaptive threshold. -/
theorem card_taoLargePrimeAdaptiveExceptionalConductorsIn_cast_le_of_moment
    {D : Finset ℕ} {Z R : ℕ} {K : ℝ} (hR : 0 < R)
    (hmoment :
      ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) ≤ K) :
    ((taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card : ℝ) ≤
      K * (R : ℝ) ^ (1 / 50 : ℝ) := by
  have htpos : 0 < ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) := by
    positivity
  have hcardNat := card_taoLargePrimeAdaptiveExceptionalConductorsIn_le D Z R
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card : ℝ) ≤
        ((∑ q ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hmul :
      ((taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card : ℝ) *
          ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤ K := by
    calc
      ((taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card : ℝ) *
          ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤
        ((∑ q ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters q Z R).card : ℕ) : ℝ) *
            ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcardReal (sq_nonneg _)
      _ ≤ ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) :=
        sum_adaptiveCharacter_card_mul_sq_le D Z R
      _ ≤ K := hmoment
  calc
    ((taoLargePrimeAdaptiveExceptionalConductorsIn D Z R).card : ℝ) ≤
        K / (((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ)) :=
      (le_div_iff₀ htpos).2 hmul
    _ = K * (R : ℝ) ^ (1 / 50 : ℝ) := by
      rw [div_eq_mul_inv, ← inv_pow, adaptive_rpow_inverse_sq hR]

/-- Adaptive exceptional conductors at at least one of the 1000 ordinary
prime-tuple coordinates. -/
def taoLargePrimeAdaptiveExceptionalConductorsFor
    (D : Finset ℕ) (P : Fin 1001 → ℕ) (R : ℕ) : Finset ℕ :=
  (Finset.univ.erase (0 : Fin 1001)).biUnion fun j =>
    taoLargePrimeAdaptiveExceptionalConductorsIn D (P j) R

theorem card_taoLargePrimeAdaptiveExceptionalConductorsFor_le
    (D : Finset ℕ) (P : Fin 1001 → ℕ) (R : ℕ) :
    (taoLargePrimeAdaptiveExceptionalConductorsFor D P R).card ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (taoLargePrimeAdaptiveExceptionalConductorsIn D (P j) R).card := by
  exact Finset.card_biUnion_le

/-- Burgess-conditional adaptive endpoint count.  One constant works for a
moving conductor set admissible at every ordinary coordinate scale. -/
theorem exists_eventually_card_taoLargePrimeAdaptiveExceptionalConductorsFor_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (D : ℕ → Finset ℕ)
    (hD : ∀ᶠ x : ℕ in atTop, ∀ j : Fin 1001,
      IsAdmissibleTaoExceptionalConductorSet (D x) (P x j)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ((taoLargePrimeAdaptiveExceptionalConductorsFor
        (D x) (P x) (R x)).card : ℝ) ≤
          K * (R x : ℝ) ^ (1 / 50 : ℝ) := by
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
      hC hburgess
  let K : ℝ := 1000 * M
  have hK : 0 < K := by dsimp [K]; positivity
  have hcoord : ∀ j : Fin 1001, ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ D x, ∑ χ ∈ taoExceptionalPrimitiveCharacters q (P x j),
        ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ (2 : ℕ) ≤ M := by
    intro j
    filter_upwards [(hscale.tendsto_scale j).eventually hmoment, hD] with
      x hmomentX hDX
    exact hmomentX (D x) (hDX j)
  have hall : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ q ∈ D x, ∑ χ ∈ taoExceptionalPrimitiveCharacters q (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ (2 : ℕ) ≤ M := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hcoord j
  refine ⟨K, hK, ?_⟩
  filter_upwards [hall, hR.eventually_two_le] with x hmomentX hRtwo
  have hRpos : 0 < R x := by omega
  have hcard := card_taoLargePrimeAdaptiveExceptionalConductorsFor_le
    (D x) (P x) (R x)
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalConductorsFor
        (D x) (P x) (R x)).card : ℝ) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((taoLargePrimeAdaptiveExceptionalConductorsIn
            (D x) (P x j) (R x)).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((taoLargePrimeAdaptiveExceptionalConductorsFor
        (D x) (P x) (R x)).card : ℝ) ≤ _ := hcardReal
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        M * (R x : ℝ) ^ (1 / 50 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact card_taoLargePrimeAdaptiveExceptionalConductorsIn_cast_le_of_moment
        hRpos (hmomentX j hj)
    _ = K * (R x : ℝ) ^ (1 / 50 : ℝ) := by
      dsimp [K]
      simp
      ring

/-- Cofactors carrying an adaptively exceptional primitive character after
multiplication by the fixed common conductor factor. -/
def taoLargePrimeAdaptiveExceptionalCofactorsIn
    (q₁ : ℕ) (D : Finset ℕ) (Z S : ℕ) : Finset ℕ :=
  D.filter fun q₂ =>
    (taoLargePrimeAdaptiveExceptionalCharacters (q₁ * q₂) Z S).Nonempty

theorem taoLargePrimeAdaptiveExceptionalCofactorsIn_subset
    (q₁ : ℕ) (D : Finset ℕ) (Z S : ℕ) :
    taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S ⊆ D := by
  exact Finset.filter_subset _ _

theorem card_taoLargePrimeAdaptiveExceptionalCofactorsIn_le
    (q₁ : ℕ) (D : Finset ℕ) (Z S : ℕ) :
    (taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card ≤
      ∑ q₂ ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters (q₁ * q₂) Z S).card := by
  calc
    (taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card =
        ∑ q₂ ∈ taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S, 1 := by
      simp
    _ ≤ ∑ q₂ ∈ taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S,
        (taoLargePrimeAdaptiveExceptionalCharacters (q₁ * q₂) Z S).card := by
      apply Finset.sum_le_sum
      intro q₂ hq₂
      exact Finset.one_le_card.mpr (Finset.mem_filter.mp hq₂).2
    _ ≤ ∑ q₂ ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters (q₁ * q₂) Z S).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoLargePrimeAdaptiveExceptionalCofactorsIn_subset q₁ D Z S)
        (fun _ _ _ => Nat.zero_le _)

private theorem sum_adaptiveCofactorCharacter_card_mul_sq_le
    (q₁ : ℕ) (D : Finset ℕ) (Z S : ℕ) :
    ((∑ q₂ ∈ D,
        (taoLargePrimeAdaptiveExceptionalCharacters
          (q₁ * q₂) Z S).card : ℕ) : ℝ) *
        ((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤
      ∑ q₂ ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
  let t : ℝ := (S : ℝ) ^ (-(1 / 100 : ℝ))
  have htNonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hcast :
      ((∑ q₂ ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters
            (q₁ * q₂) Z S).card : ℕ) : ℝ) * t ^ (2 : ℕ) =
        ∑ q₂ ∈ D,
          ∑ _χ ∈ taoLargePrimeAdaptiveExceptionalCharacters
            (q₁ * q₂) Z S, t ^ (2 : ℕ) := by
    push_cast
    simp [Finset.sum_mul]
  rw [hcast]
  calc
    (∑ q₂ ∈ D, ∑ _χ ∈ taoLargePrimeAdaptiveExceptionalCharacters
        (q₁ * q₂) Z S, t ^ (2 : ℕ)) ≤
      ∑ q₂ ∈ D, ∑ χ ∈ taoLargePrimeAdaptiveExceptionalCharacters
        (q₁ * q₂) Z S,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro q₂ hq₂
      apply Finset.sum_le_sum
      intro χ hχ
      have hthreshold :=
        (mem_taoLargePrimeAdaptiveExceptionalCharacters.mp hχ).2
      have ht : t ≤ taoLargePrimeAdaptiveThreshold Z S :=
        le_max_right _ _
      have hnorm : t ≤ ‖taoNormalizedPrimeCharacterSum χ Z‖ :=
        ht.trans hthreshold
      nlinarith [norm_nonneg (taoNormalizedPrimeCharacterSum χ Z)]
    _ ≤ ∑ q₂ ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro q₂ hq₂
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoLargePrimeAdaptiveExceptionalCharacters_subset (q₁ * q₂) Z S)
        (fun _ _ _ => sq_nonneg _)

/-- A bounded common-factor exceptional squared moment gives the exact
`S^(1/50)` adaptive cofactor count. -/
theorem card_taoLargePrimeAdaptiveExceptionalCofactorsIn_cast_le_of_moment
    {q₁ : ℕ} {D : Finset ℕ} {Z S : ℕ} {K : ℝ} (hS : 0 < S)
    (hmoment :
      ∑ q₂ ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) ≤ K) :
    ((taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card : ℝ) ≤
      K * (S : ℝ) ^ (1 / 50 : ℝ) := by
  have htpos : 0 < ((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) := by
    positivity
  have hcardNat := card_taoLargePrimeAdaptiveExceptionalCofactorsIn_le
    q₁ D Z S
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card : ℝ) ≤
        ((∑ q₂ ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters
            (q₁ * q₂) Z S).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hmul :
      ((taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card : ℝ) *
          ((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤ K := by
    calc
      ((taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card : ℝ) *
          ((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) ≤
        ((∑ q₂ ∈ D,
          (taoLargePrimeAdaptiveExceptionalCharacters
            (q₁ * q₂) Z S).card : ℕ) : ℝ) *
            ((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcardReal (sq_nonneg _)
      _ ≤ ∑ q₂ ∈ D,
          ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
            ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) :=
        sum_adaptiveCofactorCharacter_card_mul_sq_le q₁ D Z S
      _ ≤ K := hmoment
  calc
    ((taoLargePrimeAdaptiveExceptionalCofactorsIn q₁ D Z S).card : ℝ) ≤
        K / (((S : ℝ) ^ (-(1 / 100 : ℝ))) ^ (2 : ℕ)) :=
      (le_div_iff₀ htpos).2 hmul
    _ = K * (S : ℝ) ^ (1 / 50 : ℝ) := by
      rw [div_eq_mul_inv, ← inv_pow, adaptive_rpow_inverse_sq hS]

/-- Adaptive common-factor partners at at least one ordinary coordinate
prime-sum scale. -/
def taoLargePrimeAdaptiveExceptionalPartnersFor
    (p lowerPrime upperPrime : ℕ) (P : Fin 1001 → ℕ) (S : ℕ) : Finset ℕ :=
  (Finset.univ.erase (0 : Fin 1001)).biUnion fun j =>
    taoLargePrimeAdaptiveExceptionalCofactorsIn p
      ((taoLargeAntiSievePrimeRange lowerPrime upperPrime).erase p)
      (P j) S

theorem card_taoLargePrimeAdaptiveExceptionalPartnersFor_le
    (p lowerPrime upperPrime : ℕ) (P : Fin 1001 → ℕ) (S : ℕ) :
    (taoLargePrimeAdaptiveExceptionalPartnersFor
      p lowerPrime upperPrime P S).card ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (taoLargePrimeAdaptiveExceptionalCofactorsIn p
          ((taoLargeAntiSievePrimeRange lowerPrime upperPrime).erase p)
          (P j) S).card := by
  exact Finset.card_biUnion_le

/-- Burgess-conditional adaptive partner count, uniform in the fixed prime
and ambient prime range. -/
theorem exists_eventually_card_taoLargePrimeAdaptiveExceptionalPartnersFor_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {S : ℕ → ℕ} (hS : TaoLargePrimeSourceBandSelector S) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∀ p lowerPrime upperPrime : ℕ,
        Nat.Prime p →
        (∀ j : Fin 1001, (upperPrime : ℝ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ))) →
        ((taoLargePrimeAdaptiveExceptionalPartnersFor
          p lowerPrime upperPrime (P x) (S x)).card : ℝ) ≤
            K * (S x : ℝ) ^ (1 / 50 : ℝ) := by
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
  filter_upwards [hall, hS.eventually_two_le] with x hmomentX hStwo
  intro p lowerPrime upperPrime hp hrange
  have hSpos : 0 < S x := by omega
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
    p lowerPrime upperPrime (P x) (S x)
  have hcardReal :
      ((taoLargePrimeAdaptiveExceptionalPartnersFor
        p lowerPrime upperPrime (P x) (S x)).card : ℝ) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((taoLargePrimeAdaptiveExceptionalCofactorsIn p D
            (P x j) (S x)).card : ℝ) := by
    exact_mod_cast hcard
  calc
    ((taoLargePrimeAdaptiveExceptionalPartnersFor
        p lowerPrime upperPrime (P x) (S x)).card : ℝ) ≤ _ := hcardReal
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001),
        M * (S x : ℝ) ^ (1 / 50 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply card_taoLargePrimeAdaptiveExceptionalCofactorsIn_cast_le_of_moment
        hSpos
      exact hmomentX j hj p D hp.pos hp.squarefree hDsq hDcop (hDrange j)
    _ = K * (S x : ℝ) ^ (1 / 50 : ℝ) := by
      dsimp [K]
      simp
      ring

end

end Tao2026

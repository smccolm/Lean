import Tao2026.SmoothNumberCEPSize

/-!
# Reciprocal prime mass in the CEP source bands

This file isolates the prime-distribution input on the exact source bands.
It proves the elementary cardinality-to-reciprocal-mass bridge and propagates
any verified bandwise lower bound through equations (3.11) and (3.10).
-/

open scoped BigOperators

namespace Tao2026

noncomputable section

open Finset

/-- Natural-prime form of an open--closed real interval. -/
noncomputable def cepNatOpenClosedPrimeBand (lower upper : ℝ) : Finset ℕ :=
  (⌊upper⌋₊).primesLE \ (⌊lower⌋₊).primesLE

theorem mem_cepNatOpenClosedPrimeBand_iff
    {lower upper : ℝ} (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) {p : ℕ} :
    p ∈ cepNatOpenClosedPrimeBand lower upper ↔
      p.Prime ∧ lower < (p : ℝ) ∧ (p : ℝ) ≤ upper := by
  constructor
  · intro hp
    have hp' := Finset.mem_sdiff.mp hp
    have hupper' := Nat.mem_primesLE.mp hp'.1
    have hlower' : ⌊lower⌋₊ < p := by
      by_contra hnot
      exact hp'.2 (Nat.mem_primesLE.mpr
        ⟨Nat.le_of_not_gt hnot, hupper'.2⟩)
    exact ⟨hupper'.2, (Nat.floor_lt hlower).mp hlower',
      (Nat.le_floor_iff hupper).mp hupper'.1⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff hupper).mpr hpUpper, hpPrime⟩, ?_⟩
    intro hpLow
    exact Nat.not_lt_of_ge (Nat.mem_primesLE.mp hpLow).1
      ((Nat.floor_lt hlower).mpr hpLower)

theorem card_cepNatOpenClosedPrimeBand
    {lower upper : ℝ} (hle : lower ≤ upper) :
    (cepNatOpenClosedPrimeBand lower upper).card =
      Nat.primeCounting ⌊upper⌋₊ - Nat.primeCounting ⌊lower⌋₊ := by
  have hfloor : ⌊lower⌋₊ ≤ ⌊upper⌋₊ := Nat.floor_mono hle
  have hsub : (⌊lower⌋₊).primesLE ⊆ (⌊upper⌋₊).primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans hfloor, (Nat.mem_primesLE.mp hp).2⟩
  rw [cepNatOpenClosedPrimeBand, Finset.card_sdiff_of_subset hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

theorem image_cepOpenClosedPrimeBand_eq_natBand
    {y : ℕ} {lower upper : ℝ} (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hy : ⌊upper⌋₊ ≤ y) :
    (cepOpenClosedPrimeBand y lower upper).image
        (fun p : TaoBoundedPrime y => (p : ℕ)) =
      cepNatOpenClosedPrimeBand lower upper := by
  ext p
  rw [mem_cepNatOpenClosedPrimeBand_iff hlower hupper]
  constructor
  · intro hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨Nat.prime_of_mem_primesLE q.2,
      (mem_cepOpenClosedPrimeBand_iff.mp hq).1,
      (mem_cepOpenClosedPrimeBand_iff.mp hq).2⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    have hpFloor : p ≤ ⌊upper⌋₊ := (Nat.le_floor_iff hupper).mpr hpUpper
    have hpY : p ∈ y.primesLE := Nat.mem_primesLE.mpr
      ⟨hpFloor.trans hy, hpPrime⟩
    rw [Finset.mem_image]
    exact ⟨⟨p, hpY⟩,
      mem_cepOpenClosedPrimeBand_iff.mpr ⟨hpLower, hpUpper⟩, rfl⟩

theorem card_cepOpenClosedPrimeBand_eq_primeCounting_sub
    {y : ℕ} {lower upper : ℝ} (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hle : lower ≤ upper) (hy : ⌊upper⌋₊ ≤ y) :
    (cepOpenClosedPrimeBand y lower upper).card =
      Nat.primeCounting ⌊upper⌋₊ - Nat.primeCounting ⌊lower⌋₊ := by
  rw [← card_cepNatOpenClosedPrimeBand hle,
    ← image_cepOpenClosedPrimeBand_eq_natBand hlower hupper hy]
  exact (Finset.card_image_iff.mpr (by
    intro (p : TaoBoundedPrime y) hp (q : TaoBoundedPrime y) hq hpq
    exact Subtype.ext hpq)).symm

/-- Exact prime-counting cardinality of a canonical source band. -/
theorem card_cepCanonicalSourcePrimeBands_eq_primeCounting_sub
    {x u : ℝ} (hx : 1 ≤ x) (hu : 1 < u) (j : ℕ) :
    (cepSourcePrimeBands x u (cepSourceSmoothCutoff x u) j).card =
      Nat.primeCounting
          ⌊cepSourceBandUpper x u (cepSourceBandCount u - 1 - j)⌋₊ -
        Nat.primeCounting
          ⌊cepSourceBandLower x u (cepSourceBandCount u - 1 - j)⌋₊ := by
  apply card_cepOpenClosedPrimeBand_eq_primeCounting_sub
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.rpow_nonneg (by linarith) _
  · exact cepSourceBandLower_le_upper hx hu _
  · exact floor_cepSourceBandUpper_le_smoothCutoff hx hu _

/-- A finite family of positive numbers bounded by `upper` has reciprocal
mass at least its cardinality divided by `upper`. -/
theorem card_div_upper_le_sum_inv_boundedPrime
    {y : ℕ} {P : Finset (TaoBoundedPrime y)} {upper : ℝ}
    (hP : ∀ p ∈ P, ((p : ℕ) : ℝ) ≤ upper) :
    (P.card : ℝ) / upper ≤ ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) := by
  calc
    (P.card : ℝ) / upper = ∑ _p ∈ P, upper⁻¹ := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by
          exact_mod_cast (Nat.prime_of_mem_primesLE p.2).pos)
          (hP p hp))

/-- Source-band specialization of the cardinality-to-reciprocal bridge. -/
theorem card_div_cepSourceBandUpper_le_primeMass
    {x u : ℝ} {y j : ℕ} :
    ((cepSourcePrimeBands x u y j).card : ℝ) /
        cepSourceBandUpper x u (cepSourceBandCount u - 1 - j) ≤
      ∑ p ∈ cepSourcePrimeBands x u y j, (((p : ℕ) : ℝ)⁻¹) := by
  apply card_div_upper_le_sum_inv_boundedPrime
  intro p hp
  exact (mem_cepSourcePrimeBand_iff.mp hp).2

/-- Main term in the source's reciprocal-prime estimate on band `j`, using
the zero-based indexing of this development. -/
def cepSourcePrimeMassMain (u : ℝ) (j : ℕ) : ℝ :=
  (1 / Real.log u ^ 3) *
    (1 + (cepSourceBandCount u - j : ℕ) / Real.log u ^ 3)

/-- Exact finite contract for the uniform error in the reciprocal-prime
estimate immediately after CEP equation (3.11). -/
def HasCEPSourcePrimeMassLower
    (x u : ℝ) (y : ℕ) (E : ℝ) : Prop :=
  ∀ j ∈ Finset.range (cepSourceBandCount u),
    cepSourcePrimeMassMain u j - E ≤
      ∑ p ∈ cepSourcePrimeBands x u y j, (((p : ℕ) : ℝ)⁻¹)

/-- A source-band prime-count lower bound at the upper endpoint implies the
corresponding reciprocal-mass contract. -/
theorem hasCEPSourcePrimeMassLower_of_card
    {x u E : ℝ} {y : ℕ} (hx : 0 < x)
    (hcard : ∀ j ∈ Finset.range (cepSourceBandCount u),
      (cepSourcePrimeMassMain u j - E) *
          cepSourceBandUpper x u (cepSourceBandCount u - 1 - j) ≤
        ((cepSourcePrimeBands x u y j).card : ℝ)) :
    HasCEPSourcePrimeMassLower x u y E := by
  intro j hj
  have hupper : 0 <
      cepSourceBandUpper x u (cepSourceBandCount u - 1 - j) :=
    Real.rpow_pos_of_pos hx _
  exact ((le_div_iff₀ hupper).2 (hcard j hj)).trans
    card_div_cepSourceBandUpper_le_primeMass

/-- The remaining shrinking-band PNT input in literal prime-counting form.
Once this endpoint difference is established, the exact reciprocal-mass
contract follows without any further analytic approximation. -/
theorem hasCEPSourcePrimeMassLower_of_primeCounting_sub
    {x u E : ℝ} (hx : 1 ≤ x) (hu : 1 < u)
    (hpi : ∀ j ∈ Finset.range (cepSourceBandCount u),
      (cepSourcePrimeMassMain u j - E) *
          cepSourceBandUpper x u (cepSourceBandCount u - 1 - j) ≤
        (Nat.primeCounting
            ⌊cepSourceBandUpper x u (cepSourceBandCount u - 1 - j)⌋₊ -
          Nat.primeCounting
            ⌊cepSourceBandLower x u (cepSourceBandCount u - 1 - j)⌋₊ : ℕ)) :
    HasCEPSourcePrimeMassLower x u (cepSourceSmoothCutoff x u) E := by
  apply hasCEPSourcePrimeMassLower_of_card (lt_of_lt_of_le zero_lt_one hx)
  intro j hj
  rw [card_cepCanonicalSourcePrimeBands_eq_primeCounting_sub hx hu j]
  exact_mod_cast hpi j hj

/-- A bandwise reciprocal-mass estimate propagates through the exact
collision-free source packet (3.11). -/
theorem cepSourcePrimeMassPacket_le_sum_inv
    {x u E : ℝ} {y : ℕ} (hx : 1 ≤ x) (hu : 1 < u)
    (hE0 : ∀ j ∈ Finset.range (cepSourceBandCount u),
      0 ≤ cepSourcePrimeMassMain u j - E)
    (hMass : HasCEPSourcePrimeMassLower x u y E) :
    ∏ j ∈ Finset.range (cepSourceBandCount u),
        (cepSourcePrimeMassMain u j - E) ^ cepSourceBandMultiplicity u j /
          (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      ∑ m ∈ cepSourcePacketProducts x u y, ((m : ℝ)⁻¹) := by
  calc
    ∏ j ∈ Finset.range (cepSourceBandCount u),
        (cepSourcePrimeMassMain u j - E) ^ cepSourceBandMultiplicity u j /
          (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      ∏ j ∈ Finset.range (cepSourceBandCount u),
        (∑ p ∈ cepSourcePrimeBands x u y j,
          (((p : ℕ) : ℝ)⁻¹)) ^ cepSourceBandMultiplicity u j /
            (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact div_nonneg (pow_nonneg (hE0 j hj) _)
          (by exact_mod_cast
            (Nat.zero_le (Nat.factorial (cepSourceBandMultiplicity u j))))
      · intro j hj
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (hE0 j hj) (hMass j hj)
            (cepSourceBandMultiplicity u j))
          (by exact_mod_cast
            (Nat.zero_le (Nat.factorial (cepSourceBandMultiplicity u j))))
    _ ≤ ∑ m ∈ cepSourcePacketProducts x u y, ((m : ℝ)⁻¹) :=
      cepSource_primePacketProduct_le_sum_inv hx hu

/-- The reciprocal-mass contract and a uniform cofactor density give the
source-specialized (3.10)--(3.11) lower bound with the analytic band main
terms displayed explicitly. -/
theorem density_mul_X_mul_cepSourcePrimeMassPacket_le_psiNat
    {X w y : ℕ} {x u D E : ℝ} (hD0 : 0 ≤ D)
    (hx : 1 ≤ x) (hu : 1 < u) (hwy : w ≤ y)
    (hw : (w : ℝ) ≤
      cepSourceBandLower x u (cepSourceBandCount u - 1))
    (hE0 : ∀ j ∈ Finset.range (cepSourceBandCount u),
      0 ≤ cepSourcePrimeMassMain u j - E)
    (hMass : HasCEPSourcePrimeMassLower x u y E)
    (hD : ∀ m ∈ cepSourcePacketProducts x u y,
      D * (X : ℝ) / (m : ℝ) ≤ (psiNat (X / m) w : ℝ)) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourcePrimeMassMain u j - E) ^ cepSourceBandMultiplicity u j /
            (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      (psiNat X y : ℝ) := by
  calc
    D * (X : ℝ) *
        ∏ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourcePrimeMassMain u j - E) ^ cepSourceBandMultiplicity u j /
            (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      D * (X : ℝ) *
        ∏ j ∈ Finset.range (cepSourceBandCount u),
          (∑ p ∈ cepSourcePrimeBands x u y j,
            (((p : ℕ) : ℝ)⁻¹)) ^ cepSourceBandMultiplicity u j /
              (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hD0 (Nat.cast_nonneg X))
      apply Finset.prod_le_prod
      · intro j hj
        exact div_nonneg (pow_nonneg (hE0 j hj) _)
          (by exact_mod_cast
            (Nat.zero_le (Nat.factorial (cepSourceBandMultiplicity u j))))
      · intro j hj
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (hE0 j hj) (hMass j hj)
            (cepSourceBandMultiplicity u j))
          (by exact_mod_cast
            (Nat.zero_le (Nat.factorial (cepSourceBandMultiplicity u j))))
    _ ≤ (psiNat X y : ℝ) :=
      density_mul_X_mul_cepSourcePrimePacketProduct_le_psiNat
        hD0 hx hu hwy hw hD

/-- Canonical-cutoff form of the source (3.10)--(3.11) bridge.  The exact
lowest-band floor supplies the cofactor cutoff, so both order side conditions
of the generic recurrence disappear. -/
theorem density_mul_X_mul_cepCanonicalPrimeMassPacket_le_psiNat
    {X : ℕ} {x u D E : ℝ} (hD0 : 0 ≤ D)
    (hx : 1 ≤ x) (hu : 1 < u)
    (hE0 : ∀ j ∈ Finset.range (cepSourceBandCount u),
      0 ≤ cepSourcePrimeMassMain u j - E)
    (hMass : HasCEPSourcePrimeMassLower x u
      (cepSourceSmoothCutoff x u) E)
    (hD : ∀ m ∈ cepSourcePacketProducts x u
        (cepSourceSmoothCutoff x u),
      D * (X : ℝ) / (m : ℝ) ≤
        (psiNat (X / m) (cepSourceCofactorCutoff x u) : ℝ)) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourcePrimeMassMain u j - E) ^
              cepSourceBandMultiplicity u j /
            (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      (psiNat X (cepSourceSmoothCutoff x u) : ℝ) := by
  exact density_mul_X_mul_cepSourcePrimeMassPacket_le_psiNat hD0 hx hu
    (cepSourceCofactorCutoff_le_smoothCutoff hx hu)
    (cast_cepSourceCofactorCutoff_le_lower (le_trans (by norm_num) hx))
    hE0 hMass hD

/-- Literal prime-counting version of the canonical source packet.  After
this theorem, the only band input is the lower bound for the displayed
difference of `Nat.primeCounting` at the two floored source endpoints. -/
theorem density_mul_X_mul_cepCanonicalPrimeCountingPacket_le_psiNat
    {X : ℕ} {x u D E : ℝ} (hD0 : 0 ≤ D)
    (hx : 1 ≤ x) (hu : 1 < u)
    (hE0 : ∀ j ∈ Finset.range (cepSourceBandCount u),
      0 ≤ cepSourcePrimeMassMain u j - E)
    (hpi : ∀ j ∈ Finset.range (cepSourceBandCount u),
      (cepSourcePrimeMassMain u j - E) *
          cepSourceBandUpper x u (cepSourceBandCount u - 1 - j) ≤
        (Nat.primeCounting
            ⌊cepSourceBandUpper x u
              (cepSourceBandCount u - 1 - j)⌋₊ -
          Nat.primeCounting
            ⌊cepSourceBandLower x u
              (cepSourceBandCount u - 1 - j)⌋₊ : ℕ))
    (hD : ∀ m ∈ cepSourcePacketProducts x u
        (cepSourceSmoothCutoff x u),
      D * (X : ℝ) / (m : ℝ) ≤
        (psiNat (X / m) (cepSourceCofactorCutoff x u) : ℝ)) :
    D * (X : ℝ) *
        ∏ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourcePrimeMassMain u j - E) ^
              cepSourceBandMultiplicity u j /
            (Nat.factorial (cepSourceBandMultiplicity u j) : ℝ) ≤
      (psiNat X (cepSourceSmoothCutoff x u) : ℝ) := by
  apply density_mul_X_mul_cepCanonicalPrimeMassPacket_le_psiNat
    hD0 hx hu hE0
  · exact hasCEPSourcePrimeMassLower_of_primeCounting_sub hx hu hpi
  · exact hD

end

end Tao2026

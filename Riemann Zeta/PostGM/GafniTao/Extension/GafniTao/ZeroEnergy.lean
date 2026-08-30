import GafniTao.Asymptotics

/-!
# Multiplicity-weighted zero density and additive energy

The finite zero set stores distinct complex zeros.  Every count below restores
the source multiset convention by multiplying analytic vanishing orders.
-/

open scoped BigOperators

namespace GafniTao

/-- One occurrence of a zeta zero in the source multiset: a distinct zero
together with an index below its analytic multiplicity. -/
abbrev ZeroOccurrence (sigma T : ℝ) :=
  Σ rho : {z : ℂ // z ∈ zeroSet sigma T}, Fin (zeroMultiplicity rho)

/-- Forget the multiplicity index of a zero occurrence. -/
def ZeroOccurrence.value {sigma T : ℝ} (rho : ZeroOccurrence sigma T) : ℂ :=
  rho.1

/-- The occurrence type has exactly the analytic-multiplicity-weighted zero
count as its cardinality. -/
theorem card_zeroOccurrence (sigma T : ℝ) :
    Fintype.card (ZeroOccurrence sigma T) = zeroCount sigma T := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [zeroCount_eq_weighted_sum]
  exact Finset.sum_attach _ _

/-- The source epsilon-density predicate for the actual symmetric zero count.
The coefficient `a` is normalized so that the power is `a * (1-sigma)`. -/
def ZeroDensityEnvelope (sigma a : ℝ) : Prop :=
  EpsilonExponentBound
    (fun T => (zeroCount sigma T : ℝ))
    (a * (1 - sigma))

/-- The actual least ordinary zero-density exponent `A(sigma)`. -/
noncomputable def zeroDensityExponent (sigma : ℝ) : EReal :=
  sInf {x | ∃ a : ℝ, ZeroDensityEnvelope sigma a ∧ x = (a : EReal)}

theorem zeroDensityExponent_le {sigma a : ℝ}
    (ha : ZeroDensityEnvelope sigma a) :
    zeroDensityExponent sigma ≤ (a : EReal) := by
  apply sInf_le
  exact ⟨a, ha, rfl⟩

/-- The actual frozen Guth--Maynard theorem, normalized as the Gafni--Tao
ordinary density envelope.  This is a consumer of the frozen public theorem,
not a restatement as a hypothesis. -/
theorem guthMaynard_zeroDensityEnvelope {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    ZeroDensityEnvelope sigma (15 / (3 + 5 * sigma)) := by
  have h := frozen_guthMaynard_zero_density sigma hsigmaLower hsigmaUpper
  unfold ZeroDensityEnvelope EpsilonExponentBound
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The frozen Guth--Maynard estimate gives the corresponding upper bound for
the genuine least density exponent. -/
theorem zeroDensityExponent_le_guthMaynard {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    zeroDensityExponent sigma ≤ ((15 / (3 + 5 * sigma) : ℝ) : EReal) :=
  zeroDensityExponent_le
    (guthMaynard_zeroDensityEnvelope hsigmaLower hsigmaUpper)

/-- The uniform `30/13` envelope used in the Gafni--Tao examples.  The lower
range consumes the frozen publication-facing Ingham theorem; the upper range
consumes `guthMaynardZeroDensity_published_native` through
`frozen_guthMaynard_zero_density`. -/
theorem frozen_uniform_thirty_thirteenths_zeroDensityEnvelope {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    ZeroDensityEnvelope sigma (30 / 13) := by
  unfold ZeroDensityEnvelope EpsilonExponentBound
  by_cases hsigmaLow : sigma ≤ 7 / 10
  · have hIngham :=
      RiemannZeta.GuthMaynard.inghamZeroDensity_published_native
        sigma hsigmaLower hsigmaUpper
    apply RiemannZeta.GuthMaynard.EpsilonPowerBound_mono _ _ _ hIngham
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hden : 0 < 2 - sigma := by linarith
    have hcoef : 3 / (2 - sigma) ≤ (30 / 13 : ℝ) := by
      rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 13)]
      nlinarith
    calc
      3 * (1 - sigma) / (2 - sigma) =
          (3 / (2 - sigma)) * (1 - sigma) := by ring
      _ ≤ (30 / 13) * (1 - sigma) :=
        mul_le_mul_of_nonneg_right hcoef (by linarith)
  · have hGM :=
      frozen_guthMaynard_zero_density sigma hsigmaLower hsigmaUpper
    apply RiemannZeta.GuthMaynard.EpsilonPowerBound_mono _ _ _ hGM
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hden : 0 < 3 + 5 * sigma := by linarith
    have hcoef : 15 / (3 + 5 * sigma) ≤ (30 / 13 : ℝ) := by
      rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 13)]
      nlinarith
    calc
      15 * (1 - sigma) / (3 + 5 * sigma) =
          (15 / (3 + 5 * sigma)) * (1 - sigma) := by ring
      _ ≤ (30 / 13) * (1 - sigma) :=
        mul_le_mul_of_nonneg_right hcoef (by linarith)

theorem zeroDensityExponent_le_thirty_thirteenths {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    zeroDensityExponent sigma ≤ ((30 / 13 : ℝ) : EReal) :=
  zeroDensityExponent_le
    (frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
      hsigmaLower hsigmaUpper)

/-- Exact threshold arithmetic for the all-interval endpoint. -/
theorem seventeen_thirtieths_eq_uniform_all_threshold :
    (17 / 30 : ℝ) = 1 - 1 / (30 / 13 : ℝ) := by
  norm_num

/-- Exact threshold arithmetic for the almost-all endpoint. -/
theorem two_fifteenths_eq_uniform_almost_all_threshold :
    (2 / 15 : ℝ) = 1 - 2 / (30 / 13 : ℝ) := by
  norm_num

/-- All ordered quadruples of distinct zero representatives.  Multiplicity is
not encoded by repetition here; it is carried by `zeroQuadrupleWeight`. -/
noncomputable def zeroQuadruples (sigma T : ℝ) :
    Finset ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (zeroSet sigma T ×ˢ zeroSet sigma T) ×ˢ
    (zeroSet sigma T ×ˢ zeroSet sigma T)

/-- The exact tolerance-one relation
`|gamma1+gamma2-gamma3-gamma4| ≤ 1`. -/
def IsResonantZeroQuadruple (q : (ℂ × ℂ) × (ℂ × ℂ)) : Prop :=
  |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| ≤ 1

/-- Product analytic multiplicity of an ordered zero quadruple. -/
noncomputable def zeroQuadrupleWeight
    (q : (ℂ × ℂ) × (ℂ × ℂ)) : ℕ :=
  zeroMultiplicity q.1.1 * zeroMultiplicity q.1.2 *
  zeroMultiplicity q.2.1 * zeroMultiplicity q.2.2

/-- The finite set of tolerance-one zero quadruples. -/
noncomputable def resonantZeroQuadruples (sigma T : ℝ) :
    Finset ((ℂ × ℂ) × (ℂ × ℂ)) := by
  classical
  exact (zeroQuadruples sigma T).filter IsResonantZeroQuadruple

/-- The exact Gafni--Tao four-zero additive-energy count `N*(sigma,T)`. -/
noncomputable def zeroAdditiveEnergyCount (sigma T : ℝ) : ℕ :=
  ∑ q ∈ resonantZeroQuadruples sigma T, zeroQuadrupleWeight q

/-- A resonant distinct-zero quadruple together with one of its product-
multiplicity copies.  This sigma type is the canonical finite multiset model:
the fiber over `q` has exactly `zeroQuadrupleWeight q` elements. -/
abbrev ResonantZeroOccurrenceQuadruple (sigma T : ℝ) :=
  Σ q : {q : ((ℂ × ℂ) × (ℂ × ℂ)) //
      q ∈ resonantZeroQuadruples sigma T},
    Fin (zeroQuadrupleWeight q)

/-- The same count performed literally on the replicated multiset fibers. -/
noncomputable def zeroAdditiveEnergyOccurrenceCount (sigma T : ℝ) : ℕ := by
  classical
  exact Fintype.card (ResonantZeroOccurrenceQuadruple sigma T)

/-- Weighted distinct representatives and literal multiset replication give
the same `N*(sigma,T)`. -/
theorem zeroAdditiveEnergyOccurrenceCount_eq
    (sigma T : ℝ) :
    zeroAdditiveEnergyOccurrenceCount sigma T =
      zeroAdditiveEnergyCount sigma T := by
  classical
  rw [zeroAdditiveEnergyOccurrenceCount, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [zeroAdditiveEnergyCount, Finset.sum_coe_sort_eq_attach,
    Finset.sum_attach]

theorem mem_zeroQuadruples {sigma T : ℝ}
    {q : (ℂ × ℂ) × (ℂ × ℂ)} :
    q ∈ zeroQuadruples sigma T ↔
      q.1.1 ∈ zeroSet sigma T ∧ q.1.2 ∈ zeroSet sigma T ∧
      q.2.1 ∈ zeroSet sigma T ∧ q.2.2 ∈ zeroSet sigma T := by
  simp [zeroQuadruples, and_assoc]

theorem mem_resonantZeroQuadruples {sigma T : ℝ}
    {q : (ℂ × ℂ) × (ℂ × ℂ)} :
    q ∈ resonantZeroQuadruples sigma T ↔
      q.1.1 ∈ zeroSet sigma T ∧ q.1.2 ∈ zeroSet sigma T ∧
      q.2.1 ∈ zeroSet sigma T ∧ q.2.2 ∈ zeroSet sigma T ∧
      |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| ≤ 1 := by
  classical
  simp only [resonantZeroQuadruples, Finset.mem_filter, mem_zeroQuadruples,
    IsResonantZeroQuadruple]
  aesop

theorem zeroAdditiveEnergyCount_nonneg (sigma T : ℝ) :
    0 ≤ zeroAdditiveEnergyCount sigma T := Nat.zero_le _

/-- The source epsilon-density predicate for `N*`. -/
def ZeroAdditiveEnergyEnvelope (sigma a : ℝ) : Prop :=
  EpsilonExponentBound
    (fun T => (zeroAdditiveEnergyCount sigma T : ℝ))
    (a * (1 - sigma))

/-- The actual least additive-energy exponent `A*(sigma)`. -/
noncomputable def zeroAdditiveEnergyExponent (sigma : ℝ) : EReal :=
  sInf {x | ∃ a : ℝ, ZeroAdditiveEnergyEnvelope sigma a ∧ x = (a : EReal)}

theorem zeroAdditiveEnergyExponent_le {sigma a : ℝ}
    (ha : ZeroAdditiveEnergyEnvelope sigma a) :
    zeroAdditiveEnergyExponent sigma ≤ (a : EReal) := by
  apply sInf_le
  exact ⟨a, ha, rfl⟩

end GafniTao

import GafniTao.FordLPartition

/-!
# Ford Lemma 3.3: the `(k-1)`-coordinate mean

Deleting a marked diagonal coordinate from a solution of (3.2) leaves the
zero-frequency problem with `k-1` copies of Ford's nonnegative function
`I(α)`.  This file defines that literal finite problem and identifies both its
mean and the original `L_s` mean with their finite counts.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordLReducedPolynomialTuple (k P p r : ℕ) :=
  Fin (k - 1) → FordLCongruentCoordinate P p r

def fordLReducedPolynomialMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (u : FordLReducedPolynomialTuple k P p r) : Fin k → ℤ :=
  fordFamilyMoment (fordLCoordinateMoment Ψ) u

def fordLReducedTotalMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ)
    (v : FordLReducedPolynomialTuple k P p r × FordLPowerPair s Q) :
    Fin k → ℤ :=
  fordLReducedPolynomialMoment Ψ v.1 +
    fordLPowerPairMoment k Q p q s v.2

abbrev FordLReducedSolution
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) :=
  FordCharacterZero
    (fordLReducedTotalMoment (P := P) (p := p) (r := r) Ψ s Q q)

def fordLReducedCount
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) : ℕ :=
  Nat.card (FordLReducedSolution (P := P) (p := p) (r := r) Ψ s Q q)

theorem fordLReducedPolynomialTuple_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLReducedPolynomialMoment (P := P) (p := p) (r := r) Ψ) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) := by
  exact fordCharacterSum_familyMoment_eq_pow_card
    (fordLCoordinateMoment (P := P) (p := p) (r := r) Ψ) α
    |>.trans (by simp [fordLCoordinateWeylSum])

theorem fordLReducedTotal_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLReducedTotalMoment (P := P) (p := p) (r := r) Ψ s Q q) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
        (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) := by
  unfold fordLReducedTotalMoment fordCharacterSum
  rw [Fintype.sum_prod_type]
  simp_rw [UnitAddTorus.mFourier_add]
  rw [← Finset.sum_mul_sum]
  change fordCharacterSum
      (fordLReducedPolynomialMoment (P := P) (p := p) (r := r) Ψ) α *
    fordCharacterSum (fordLPowerPairMoment k Q p q s) α = _
  rw [fordLReducedPolynomialTuple_characterSum,
    fordLPowerPair_characterSum]

theorem fordLReduced_character_mean_eq_count
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k =
      (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℂ) := by
  unfold fordLReducedCount
  rw [← ford_character_sum_mean_eq_zero_count
    (fordLReducedTotalMoment (P := P) (p := p) (r := r) Ψ s Q q)]
  apply integral_congr_ae
  filter_upwards [] with α
  exact (fordLReducedTotal_characterSum (P := P) (p := p) (r := r)
    Ψ s Q q α).symm

theorem continuous_fordPolynomialResidueWeylSum
    {k d T P m : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ZMod m) :
    Continuous (fordPolynomialResidueWeylSum (P := P) Ψ c) := by
  unfold fordPolynomialResidueWeylSum
  fun_prop

theorem continuous_fordLCoordinateEnergy
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) :
    Continuous (fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ) := by
  unfold fordLCoordinateEnergy
  exact continuous_finsetSum _ fun c _ ↦
    (continuous_fordPolynomialResidueWeylSum Ψ c).norm.pow 2

theorem integrable_fordL_energy_integrand
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q n : ℕ) :
    Integrable (fun α : UnitAddTorus (Fin k) ↦
      fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ n *
        ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  exact ((continuous_fordLCoordinateEnergy Ψ).pow n |>.mul
    ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s)))
    |>.continuousOn.integrableOn_compact isCompact_univ

theorem fordL_real_mean_eq_count
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ k *
          ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
        ∂fordTorusMeasure k =
      (fordLCount Ψ s P Q p q r : ℝ) := by
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          ((fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ k *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) : ℂ)
          ∂fordTorusMeasure k) =
        ((∫ α : UnitAddTorus (Fin k),
          fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ k *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
          ∂fordTorusMeasure k : ℝ) : ℂ) := integral_ofReal
  rw [← hcast]
  calc
    _ = ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ k *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k := by
      apply integral_congr_ae
      filter_upwards [] with α
      rw [fordLCoordinateWeylSum_eq_energy]
      norm_num
    _ = (fordLCount Ψ s P Q p q r : ℂ) :=
      fordL_character_mean_eq_count (P := P) (p := p) (r := r) Ψ s Q q
    _ = _ := by norm_num

theorem fordLReduced_real_mean_eq_count
    {k d T P p r : ℕ} [NeZero (p ^ r)]
    (Ψ : FordIntegerPolynomialSystem k d T) (s Q q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
          ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
        ∂fordTorusMeasure k =
      (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℝ) := by
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          ((fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) : ℂ)
          ∂fordTorusMeasure k) =
        ((∫ α : UnitAddTorus (Fin k),
          fordLCoordinateEnergy (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
          ∂fordTorusMeasure k : ℝ) : ℂ) := integral_ofReal
  rw [← hcast]
  calc
    _ = ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ (k - 1) *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k := by
      apply integral_congr_ae
      filter_upwards [] with α
      rw [fordLCoordinateWeylSum_eq_energy]
      norm_num
    _ = (fordLReducedCount (P := P) (p := p) (r := r) Ψ s Q q : ℂ) :=
      fordLReduced_character_mean_eq_count
        (P := P) (p := p) (r := r) Ψ s Q q
    _ = _ := by norm_num

#print axioms fordLReduced_character_mean_eq_count
#print axioms continuous_fordLCoordinateEnergy
#print axioms fordL_real_mean_eq_count
#print axioms fordLReduced_real_mean_eq_count

end

end GafniTao

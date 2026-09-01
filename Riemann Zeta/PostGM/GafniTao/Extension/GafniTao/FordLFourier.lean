import GafniTao.FordZeroFourier

/-!
# Ford Lemma 3.3: exact Fourier model for `L_s`

The congruence `z_i ≡ w_i (mod p^r)` is built into each polynomial
coordinate.  The resulting single-coordinate character sum is Ford's
`I(α)`; its `k`th power times the power-pair character sum represents the
literal finite `L_s` count.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordLCongruentCoordinate (P p r : ℕ) :=
  {zw : Fin P × Fin P //
    Nat.ModEq (p ^ r) ((zw.1 : ℕ) + 1) ((zw.2 : ℕ) + 1)}

abbrev FordLPolynomialTuple (k P p r : ℕ) :=
  Fin k → FordLCongruentCoordinate P p r

abbrev FordLPowerPair (s Q : ℕ) := FordBox s Q × FordBox s Q

def fordLCoordinateMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (zw : FordLCongruentCoordinate P p r) : Fin k → ℤ :=
  fun j => (Ψ.poly j).eval ((((zw.1.1 : ℕ) + 1 : ℕ) : ℤ)) -
    (Ψ.poly j).eval ((((zw.1.2 : ℕ) + 1 : ℕ) : ℤ))

def fordLPolynomialTupleMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (u : FordLPolynomialTuple k P p r) : Fin k → ℤ :=
  fordFamilyMoment (fordLCoordinateMoment Ψ) u

def fordLPowerPairMoment (k Q p q s : ℕ)
    (xy : FordLPowerPair s Q) : Fin k → ℤ :=
  fordS3BoxMoment (k := k) (p * q) xy.1 -
    fordS3BoxMoment (k := k) (p * q) xy.2

def fordLTotalMoment
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ)
    (v : FordLPolynomialTuple k P p r × FordLPowerPair s Q) :
    Fin k → ℤ :=
  fordLPolynomialTupleMoment Ψ v.1 +
    fordLPowerPairMoment k Q p q s v.2

abbrev FordLSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :=
  {v : FordLVariables k s P Q // FordLEquation Ψ p q r v}

def fordLSolutionEquivCharacterZero
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    FordLSolution Ψ s P Q p q r ≃
      FordCharacterZero (fordLTotalMoment Ψ s Q q :
        (FordLPolynomialTuple k P p r × FordLPowerPair s Q) →
          Fin k → ℤ) where
  toFun v := ⟨(fun i => ⟨(v.1.1.1 i, v.1.1.2 i), v.2.1 i⟩,
      (v.1.2.1, v.1.2.2)), by
    funext j
    have h := v.2.2 j
    unfold fordLTotalMoment fordLPolynomialTupleMoment fordLPowerPairMoment
      fordFamilyMoment fordLCoordinateMoment fordS3BoxMoment at ⊢
    unfold fordPolynomialDifference fordPowerDifference at h
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
      Pi.zero_apply, fordBoxValue, Finset.sum_sub_distrib] at h ⊢
    push_cast at h ⊢
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination h⟩
  invFun v := ⟨((fun i => v.1.1 i |>.1.1,
      fun i => v.1.1 i |>.1.2), v.1.2), by
    refine ⟨?_, ?_⟩
    · intro i
      exact (v.1.1 i).2
    · intro j
      have h := congrFun v.2 j
      unfold fordLTotalMoment fordLPolynomialTupleMoment fordLPowerPairMoment
        fordFamilyMoment fordLCoordinateMoment fordS3BoxMoment at h
      unfold fordPolynomialDifference fordPowerDifference
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
        Pi.zero_apply, fordBoxValue, Finset.sum_sub_distrib] at h ⊢
      push_cast at h ⊢
      rw [← Finset.mul_sum, ← Finset.mul_sum] at h
      linear_combination h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fordLCount_eq_characterZero
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLCount Ψ s P Q p q r =
      Nat.card (FordCharacterZero (fordLTotalMoment Ψ s Q q :
        (FordLPolynomialTuple k P p r × FordLPowerPair s Q) →
          Fin k → ℤ)) := by
  unfold fordLCount
  calc
    Fintype.card {v : FordLVariables k s P Q // FordLEquation Ψ p q r v} =
        Nat.card (FordLSolution Ψ s P Q p q r) :=
      Nat.card_eq_fintype_card.symm
    _ = _ := Nat.card_congr (fordLSolutionEquivCharacterZero Ψ s P Q p q r)

def fordLCoordinateWeylSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) : ℂ :=
  fordCharacterSum (fordLCoordinateMoment (P := P) (p := p) (r := r) Ψ) α

theorem fordLPolynomialTuple_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLPolynomialTupleMoment (P := P) (p := p) (r := r) Ψ) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ k := by
  exact fordCharacterSum_familyMoment_eq_pow_card
    (fordLCoordinateMoment (P := P) (p := p) (r := r) Ψ) α
    |>.trans (by simp [fordLCoordinateWeylSum])

theorem fordLPowerPair_characterSum
    (k Q p q s : ℕ) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum (fordLPowerPairMoment k Q p q s) α =
      (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) := by
  unfold fordLPowerPairMoment fordCharacterSum
  rw [Fintype.sum_prod_type]
  simp_rw [sub_eq_add_neg, UnitAddTorus.mFourier_add,
    UnitAddTorus.mFourier_neg]
  rw [← Finset.sum_mul_sum]
  rw [← map_sum]
  change fordCharacterSum
      (fordS3BoxMoment (k := k) (p * q) : FordBox s Q → Fin k → ℤ) α *
    conj (fordCharacterSum
      (fordS3BoxMoment (k := k) (p * q) : FordBox s Q → Fin k → ℤ) α) = _
  simp_rw [fordPowerBoxCharacterSum_eq_pow]
  rw [Complex.mul_conj', norm_pow]
  norm_num [← pow_mul]
  rw [Nat.mul_comm s 2]

theorem fordLTotal_characterSum
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLTotalMoment (P := P) (p := p) (r := r) Ψ s Q q) α =
      fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ k *
        (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) := by
  unfold fordLTotalMoment fordCharacterSum
  rw [Fintype.sum_prod_type]
  simp_rw [UnitAddTorus.mFourier_add]
  rw [← Finset.sum_mul_sum]
  change fordCharacterSum
      (fordLPolynomialTupleMoment (P := P) (p := p) (r := r) Ψ) α *
    fordCharacterSum (fordLPowerPairMoment k Q p q s) α = _
  rw [fordLPolynomialTuple_characterSum,
    fordLPowerPair_characterSum]

theorem fordL_character_mean_eq_count
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s Q q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordLCoordinateWeylSum (P := P) (p := p) (r := r) Ψ α ^ k *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k =
      (fordLCount Ψ s P Q p q r : ℂ) := by
  rw [fordLCount_eq_characterZero]
  rw [← ford_character_sum_mean_eq_zero_count
    (fordLTotalMoment (P := P) (p := p) (r := r) Ψ s Q q)]
  apply integral_congr_ae
  filter_upwards [] with α
  exact (fordLTotal_characterSum (P := P) (p := p) (r := r)
    Ψ s Q q α).symm

#print axioms fordLSolutionEquivCharacterZero
#print axioms fordLCount_eq_characterZero
#print axioms fordLPolynomialTuple_characterSum
#print axioms fordLPowerPair_characterSum
#print axioms fordL_character_mean_eq_count

end

end GafniTao

import GafniTao.FordKRepeatedFactor

/-!
# Ford Lemma 3.2: fixed-pair collision integral

The repeated polynomial family is paired with the power family and compared
with the unrestricted right-hand family.  Fourier orthogonality then gives
the exact fixed-pair count and its source integrand majorant.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

def fordKRepeatedCombinedMoment
    {k d T P s Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k)
    (u : (Fin P × FordAwayBox (P := P) ij) × FordBox s Q) : Fin k → ℤ :=
  fordRepeatedPolynomialMoment Ψ ij u.1 + fordS3BoxMoment q u.2

def fordKFullCombinedMoment
    {k d T P s Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (u : FordBox k P × FordBox s Q) : Fin k → ℤ :=
  fordPolynomialMoment Ψ u.1 + fordS3BoxMoment q u.2

def fordKLeftRepeatToCross
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) :
    FordKLeftRepeatAt Ψ s P Q q ij →
      FordCrossCharacterCollision
        (fordKRepeatedCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ ij)
        (fordKFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ) := by
  intro u
  let zsub : FordRepeatedPolynomialBoxAt P ij := ⟨u.1.1.1.1, u.2⟩
  let ar := (fordRepeatedBoxParamEquiv ij).symm zsub
  refine ⟨((ar, u.1.1.2.1), (u.1.1.1.2, u.1.1.2.2)), ?_⟩
  have hc : fordPolynomialMoment Ψ u.1.1.1.1 +
        fordS3BoxMoment q u.1.1.2.1 =
      fordPolynomialMoment Ψ u.1.1.1.2 +
        fordS3BoxMoment q u.1.1.2.2 :=
    ((fordKCollisionEquiv Ψ) u.1).2
  have hz : fordAssembleRepeatedBox ij ar.1 ar.2 = u.1.1.1.1 := by
    exact congrArg Subtype.val ((fordRepeatedBoxParamEquiv ij).apply_symm_apply zsub)
  change fordRepeatedPolynomialMoment Ψ ij ar +
      fordS3BoxMoment q u.1.1.2.1 =
    fordPolynomialMoment Ψ u.1.1.1.2 +
      fordS3BoxMoment q u.1.1.2.2
  rw [← fordPolynomialMoment_assemble_eq]
  rw [hz]
  exact hc

theorem fordKLeftRepeatToCross_injective
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) :
    Function.Injective (fordKLeftRepeatToCross Ψ ij :
      FordKLeftRepeatAt Ψ s P Q q ij → _) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  have hval := congrArg (fun w ↦
    (fordAssembleRepeatedBox ij w.1.1.1.1 w.1.1.1.2,
      w.1.1.2, w.1.2.1, w.1.2.2)) huv
  dsimp only [fordKLeftRepeatToCross] at hval
  have hu : fordAssembleRepeatedBox ij
      ((fordRepeatedBoxParamEquiv ij).symm
        (⟨u.1.1.1.1, u.2⟩ : FordRepeatedPolynomialBoxAt P ij)).1
      ((fordRepeatedBoxParamEquiv ij).symm
        (⟨u.1.1.1.1, u.2⟩ : FordRepeatedPolynomialBoxAt P ij)).2 =
      u.1.1.1.1 := by
    exact congrArg Subtype.val ((fordRepeatedBoxParamEquiv ij).apply_symm_apply
      (⟨u.1.1.1.1, u.2⟩ : FordRepeatedPolynomialBoxAt P ij))
  have hv : fordAssembleRepeatedBox ij
      ((fordRepeatedBoxParamEquiv ij).symm
        (⟨v.1.1.1.1, v.2⟩ : FordRepeatedPolynomialBoxAt P ij)).1
      ((fordRepeatedBoxParamEquiv ij).symm
        (⟨v.1.1.1.1, v.2⟩ : FordRepeatedPolynomialBoxAt P ij)).2 =
      v.1.1.1.1 := by
    exact congrArg Subtype.val ((fordRepeatedBoxParamEquiv ij).apply_symm_apply
      (⟨v.1.1.1.1, v.2⟩ : FordRepeatedPolynomialBoxAt P ij))
  rw [hu, hv] at hval
  exact congrArg (fun t ↦ ((t.1, t.2.2.1), (t.2.1, t.2.2.2))) hval

theorem fordKRepeatedCombinedCharacterSum_eq
    {k d T P s Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) (a : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordKRepeatedCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ ij) a =
      fordPolynomialDoubleWeylSum (P := P) Ψ a *
        fordPolynomialFullWeylSum (P := P) Ψ a ^ (k - 2) *
          fordPowerFullWeylSum k Q q a ^ s := by
  classical
  unfold fordCharacterSum fordKRepeatedCombinedMoment
  simp_rw [UnitAddTorus.mFourier_add]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change fordCharacterSum
      (fordRepeatedPolynomialMoment (P := P) Ψ ij :
        (Fin P × FordAwayBox (P := P) ij) → Fin k → ℤ) a *
      fordCharacterSum
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) a = _
  rw [fordRepeatedPolynomialCharacterSum_eq,
    fordPowerBoxCharacterSum_eq_pow]

theorem fordKFullCombinedCharacterSum_eq
    {k d T P s Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordKFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ) a =
      fordPolynomialFullWeylSum (P := P) Ψ a ^ k *
        fordPowerFullWeylSum k Q q a ^ s := by
  classical
  unfold fordCharacterSum fordKFullCombinedMoment
  simp_rw [UnitAddTorus.mFourier_add]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change fordCharacterSum (fordPolynomialMoment (P := P) Ψ) a *
      fordCharacterSum
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) a = _
  rw [fordPolynomialBoxCharacterSum_eq_pow,
    fordPowerBoxCharacterSum_eq_pow]

def fordKRepeatedIntegral
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) : ℝ :=
  ∫ a : UnitAddTorus (Fin k),
    ‖fordPolynomialFullWeylSum (P := P) Ψ a‖ ^ (2 * k - 2) *
      ‖fordPolynomialDoubleWeylSum (P := P) Ψ a‖ *
        ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s)
    ∂fordTorusMeasure k

theorem integrable_fordKRepeated_integrand
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :
    Integrable (fun a : UnitAddTorus (Fin k) ↦
      ‖fordPolynomialFullWeylSum (P := P) Ψ a‖ ^ (2 * k - 2) *
        ‖fordPolynomialDoubleWeylSum (P := P) Ψ a‖ *
          ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  unfold fordPolynomialDoubleWeylSum fordCharacterSum
  exact (((continuous_fordPolynomialFullWeylSum Ψ).norm.pow (2 * k - 2)).mul
    ((continuous_finsetSum _ fun _ _ ↦ by fun_prop).norm)).mul
      ((continuous_fordPowerFullWeylSum k Q q).norm.pow (2 * s)) |>.continuousOn

theorem fordK_left_repeat_card_le_integral
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) :
    (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ) ≤
      fordKRepeatedIntegral Ψ s P Q q := by
  let M := fordKRepeatedCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ ij
  let N := fordKFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ
  have hcard : Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) ≤
      Nat.card (FordCrossCharacterCollision M N) :=
    Nat.card_le_card_of_injective _ (fordKLeftRepeatToCross_injective Ψ ij)
  have hmean := ford_cross_character_mean_eq M N
  let H : UnitAddTorus (Fin k) → ℂ := fun a ↦
    fordCharacterSum M a * conj (fordCharacterSum N a)
  have hcontH : Continuous H := by
    dsimp [H, M, N]
    unfold fordCharacterSum fordKRepeatedCombinedMoment fordKFullCombinedMoment
    fun_prop
  have hintH : Integrable (fun a ↦ ‖H a‖) (fordTorusMeasure k) := by
    rw [← integrableOn_univ]
    exact hcontH.norm.continuousOn.integrableOn_compact isCompact_univ
  have hpoint : ∀ a : UnitAddTorus (Fin k),
      ‖H a‖ ≤
        ‖fordPolynomialFullWeylSum (P := P) Ψ a‖ ^ (2 * k - 2) *
          ‖fordPolynomialDoubleWeylSum (P := P) Ψ a‖ *
            ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s) := by
    intro a
    dsimp [H, M, N]
    rw [fordKRepeatedCombinedCharacterSum_eq,
      fordKFullCombinedCharacterSum_eq]
    simp only [norm_mul, RCLike.norm_conj, norm_pow]
    have hk : 2 ≤ k := by omega
    rw [show 2 * k - 2 = (k - 2) + k by omega,
      pow_add, show 2 * s = s + s by omega, pow_add]
    ring_nf
    exact le_rfl
  calc
    (Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) : ℝ) ≤
        (Nat.card (FordCrossCharacterCollision M N) : ℝ) := by
      exact_mod_cast hcard
    _ = ‖∫ a, H a ∂fordTorusMeasure k‖ := by rw [hmean]; simp
    _ ≤ ∫ a, ‖H a‖ ∂fordTorusMeasure k := norm_integral_le_integral_norm H
    _ ≤ fordKRepeatedIntegral Ψ s P Q q := by
      unfold fordKRepeatedIntegral
      exact integral_mono hintH (integrable_fordKRepeated_integrand Ψ s P Q q) hpoint

theorem fordPolynomialDoubleWeylSum_eq_doubleSystem
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : UnitAddTorus (Fin k)) :
    fordPolynomialDoubleWeylSum (P := P) Ψ a =
      fordPolynomialFullWeylSum (P := P)
        (fordDoubleIntegerPolynomialSystem Ψ) a := by
  unfold fordPolynomialDoubleWeylSum fordPolynomialFullWeylSum fordCharacterSum
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun V ↦ UnitAddTorus.mFourier V a)
  funext j
  simp [fordPolynomialSingleMoment, fordDoubleIntegerPolynomialSystem_eval]

#print axioms fordK_left_repeat_card_le_integral
#print axioms fordPolynomialDoubleWeylSum_eq_doubleSystem

end

end GafniTao

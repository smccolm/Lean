import GafniTao.FordBoundaryWeyl

/-!
# Ford Lemma 3.2: a fixed boundary coordinate

For one pinned coordinate on the first half of the residue collision, the
literal collision type is identified with an asymmetric character collision.
This makes its cardinality an exact torus integral and exposes the factor
whose norm is bounded by the odd residue moment.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordS4ResidueLeftBoundaryAt
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) (i : Fin s) :=
  {u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4ResidueMoment (k := k) q c :
        FordS4ResidueTuple s Q p c → Fin k → ℤ) //
    fordResidueIsBoundary c (u.1.1.2 i)}

def fordLeftBoundaryCombinedMoment
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s)
    (x : FordS3PolynomialBox k d P p hdk ×
      FordBoundaryResidueTupleAt (Q := Q) c i) :
    Fin k → ℤ :=
  fordS4PolynomialMoment Ψ hdk x.1 +
    fordS4ResidueMoment (k := k) q c x.2.1

def fordFullCombinedMoment
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p)
    (x : FordS3PolynomialBox k d P p hdk × FordS4ResidueTuple s Q p c) :
    Fin k → ℤ :=
  fordS4PolynomialMoment Ψ hdk x.1 +
    fordS4ResidueMoment (k := k) q c x.2

def fordLeftBoundaryCrossEquiv
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) :
    FordCrossCharacterCollision
      (fordLeftBoundaryCombinedMoment (P := P) (Q := Q) (q := q) Ψ hdk c i)
      (fordFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ hdk c) ≃
    FordS4ResidueLeftBoundaryAt (P := P) Ψ hdk s Q q c i where
  toFun x :=
    ⟨⟨((x.1.1.1, x.1.1.2.1), (x.1.2.1, x.1.2.2)), x.2⟩, x.1.1.2.2⟩
  invFun x :=
    ⟨((x.1.1.1.1, ⟨x.1.1.1.2, x.2⟩), (x.1.1.2.1, x.1.1.2.2)), x.1.2⟩
  left_inv x := by rfl
  right_inv x := by rfl

theorem fordLeftBoundaryCharacterSum_eq
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordLeftBoundaryCombinedMoment (P := P) (Q := Q) (q := q) Ψ hdk c i) α =
      fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α *
        fordBoundaryTupleWeylSum k Q q p c i α := by
  classical
  unfold fordCharacterSum fordLeftBoundaryCombinedMoment
  simp_rw [UnitAddTorus.mFourier_add]
  rw [Fintype.sum_prod_type]
  unfold fordPolynomialWeylSum fordBoundaryTupleWeylSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fordS4PolynomialMoment]
  rw [Finset.mul_sum]

theorem fordFullCombinedCharacterSum_eq
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (α : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q) Ψ hdk c) α =
      fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α *
        fordResidueWeylSum k Q q p c α ^ s := by
  classical
  unfold fordCharacterSum fordFullCombinedMoment
  simp_rw [UnitAddTorus.mFourier_add]
  rw [Fintype.sum_prod_type]
  unfold fordPolynomialWeylSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fordS4PolynomialMoment]
  rw [fordResidueWeylSum_pow]
  unfold fordCharacterSum
  rw [Finset.mul_sum]

theorem ford_left_boundary_cross_mean_eq
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) :
    ∫ α : UnitAddTorus (Fin k),
        fordCharacterSum
            (fordLeftBoundaryCombinedMoment (P := P) (Q := Q) (q := q) Ψ hdk c i) α *
          conj (fordCharacterSum
            (fordFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q)
              Ψ hdk c) α)
        ∂fordTorusMeasure k =
      ((Nat.card (FordS4ResidueLeftBoundaryAt (P := P)
        Ψ hdk s Q q c i) : ℝ) : ℂ) := by
  rw [ford_cross_character_mean_eq]
  rw [Nat.card_congr (fordLeftBoundaryCrossEquiv (P := P) (Q := Q) (q := q)
    Ψ hdk c i)]

def fordS4OddIntegral
    {k d T P p : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) : ℝ :=
  ∫ α : UnitAddTorus (Fin k),
    ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
      ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1)
    ∂fordTorusMeasure k

theorem integrable_fordS4Odd_integrand
    {k d T P p : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :
    Integrable (fun α : UnitAddTorus (Fin k) ↦
      ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
        ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  exact ((continuous_fordPolynomialWeylSum Ψ hdk).norm.pow 2).mul
    ((continuous_fordResidueWeylSum k Q q p c).norm.pow (2 * s - 1)) |>.continuousOn

theorem ford_left_boundary_card_le_odd_integral
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (i : Fin s) (hs : 1 ≤ s) :
    (Nat.card (FordS4ResidueLeftBoundaryAt (P := P)
        Ψ hdk s Q q c i) : ℝ) ≤
      fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
  let H : UnitAddTorus (Fin k) → ℂ := fun α ↦
    fordCharacterSum
        (fordLeftBoundaryCombinedMoment (P := P) (Q := Q) (q := q)
          Ψ hdk c i) α *
      conj (fordCharacterSum
        (fordFullCombinedMoment (P := P) (s := s) (Q := Q) (q := q)
          Ψ hdk c) α)
  have hmean := ford_left_boundary_cross_mean_eq
    (P := P) (Q := Q) (q := q) Ψ hdk c i
  have hcontH : Continuous H := by
    dsimp [H]
    unfold fordCharacterSum fordLeftBoundaryCombinedMoment
      fordFullCombinedMoment
    fun_prop
  have hintH : Integrable (fun α ↦ ‖H α‖) (fordTorusMeasure k) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    exact hcontH.norm.continuousOn
  have hpoint : ∀ α : UnitAddTorus (Fin k),
      ‖H α‖ ≤
        ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
          ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1) := by
    intro α
    dsimp [H]
    rw [fordLeftBoundaryCharacterSum_eq, fordFullCombinedCharacterSum_eq]
    rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul, norm_pow]
    have hb := norm_fordBoundaryTupleWeylSum_le k Q q p c i α
    have hmul := mul_le_mul_of_nonneg_right hb
      (pow_nonneg (norm_nonneg (fordResidueWeylSum k Q q p c α)) s)
    rw [← pow_add] at hmul
    have hexp : s - 1 + s = 2 * s - 1 := by omega
    rw [hexp] at hmul
    calc
      ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ *
          ‖fordBoundaryTupleWeylSum k Q q p c i α‖ *
          (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ *
            ‖fordResidueWeylSum k Q q p c α‖ ^ s) =
          ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
            (‖fordBoundaryTupleWeylSum k Q q p c i α‖ *
              ‖fordResidueWeylSum k Q q p c α‖ ^ s) := by ring
      _ ≤ ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
          ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1) :=
        mul_le_mul_of_nonneg_left hmul (sq_nonneg _)
  calc
    (Nat.card (FordS4ResidueLeftBoundaryAt (P := P)
        Ψ hdk s Q q c i) : ℝ) =
        ‖∫ α, H α ∂fordTorusMeasure k‖ := by
      rw [hmean]
      simp
    _ ≤ ∫ α, ‖H α‖ ∂fordTorusMeasure k :=
      norm_integral_le_integral_norm H
    _ ≤ fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
      unfold fordS4OddIntegral
      exact integral_mono hintH (integrable_fordS4Odd_integrand Ψ hdk s Q q c) hpoint

#print axioms ford_left_boundary_cross_mean_eq
#print axioms ford_left_boundary_card_le_odd_integral

end

end GafniTao

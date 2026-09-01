import GafniTao.FordEquation34Count

/-!
# Ford equation (3.4): the residue-partitioned `S_3` count

The pre-AM--GM integral is converted to a sum of explicit finite collision
counts.  The dependent tuple type records both the power-sum residue fibre
`B_s(v)` and the actual integers in `[1,Q]` occupying its residue classes.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordS3ResidueTuple
    (d s Q p : ℕ) (hds : d ≤ s) (v : Fin d → ZMod p) :=
  Σ c : FordBResidueClass p d s v,
    ∀ i : Fin s, FordResidueInterval Q p (fordBJoin hds c.1 i)

def fordS3ResidueMoment
    {k d s Q p : ℕ} (hds : d ≤ s) (q : ℕ)
    (v : Fin d → ZMod p) (x : FordS3ResidueTuple d s Q p hds v) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s,
    ((q ^ ((j : ℕ) + 1) *
      ((x.2 i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)

def fordS3ResidueCollisionCount
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (hds : d ≤ s) (v : Fin d → ZMod p) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS3ResidueMoment (k := k) hds q v :
      FordS3ResidueTuple d s Q p hds v → Fin k → ℤ))

def fordS3ResidueCollisionSum
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (hds : d ≤ s) : ℕ :=
  ∑ v : Fin d → ZMod p,
    fordS3ResidueCollisionCount (P := P) Ψ hdk s Q q hds v

theorem fordS3ResidueMoment_eq_sum
    {k d s Q p : ℕ} (hds : d ≤ s) (q : ℕ)
    (v : Fin d → ZMod p) (x : FordS3ResidueTuple d s Q p hds v) :
    fordS3ResidueMoment (k := k) hds q v x =
      ∑ i : Fin s, fun j : Fin k =>
        ((q ^ ((j : ℕ) + 1) *
          ((x.2 i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
  ext j
  simp [fordS3ResidueMoment]

theorem fordS3ResidueTuple_prod_character
    {k d s Q p : ℕ} (hds : d ≤ s) (q : ℕ)
    (v : Fin d → ZMod p) (x : FordS3ResidueTuple d s Q p hds v)
    (α : UnitAddTorus (Fin k)) :
    ∏ i : Fin s,
        UnitAddTorus.mFourier
          (fun j : Fin k =>
            ((q ^ ((j : ℕ) + 1) *
              ((x.2 i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) α =
      UnitAddTorus.mFourier
        (fordS3ResidueMoment (k := k) hds q v x) α := by
  rw [fordS3ResidueMoment_eq_sum]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        UnitAddTorus.mFourier_add]
      exact congrArg (fun z =>
        UnitAddTorus.mFourier
          (fun j : Fin k =>
            ((q ^ ((j : ℕ) + 1) *
              ((x.2 i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) α * z) ih

theorem fordResidueFiberProduct_eq_characterSum
    {k d s Q q p : ℕ} [NeZero p] (hds : d ≤ s)
    (v : Fin d → ZMod p) (α : UnitAddTorus (Fin k)) :
    fordResidueFiberProduct hds
        (fun c => fordResidueWeylSum k Q q p c α) v =
      fordCharacterSum
        (fordS3ResidueMoment (k := k) hds q v :
          FordS3ResidueTuple d s Q p hds v → Fin k → ℤ) α := by
  unfold fordResidueFiberProduct fordResidueWeylSum fordCharacterSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact fordS3ResidueTuple_prod_character hds q v ⟨c, x⟩ α

theorem integrable_fordS3_collision_integrand
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (v : Fin d → ZMod p) :
    Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordCharacterSum
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk) α‖ ^ 2 *
      ‖fordCharacterSum
        (fordS3ResidueMoment (k := k) hds q v :
          FordS3ResidueTuple d s Q p hds v → Fin k → ℤ) α‖ ^ 2)
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  apply Continuous.continuousOn
  unfold fordCharacterSum
  fun_prop

/-- The exact counting interpretation of the pre-AM--GM `S_3` majorant. -/
theorem fordS3ResidueMajorant_eq_collisionSum
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) :
    fordS3ResidueMajorant (P := P) (p := p) Ψ hdk s Q q hds =
      (fordS3ResidueCollisionSum (P := P) (p := p)
        Ψ hdk s Q q hds : ℝ) := by
  unfold fordS3ResidueMajorant fordS3ResidueCollisionSum
  simp_rw [fordPolynomialWeylSum_eq_characterSum,
    fordResidueFiberProduct_eq_characterSum]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun v _ => integrable_fordS3_collision_integrand
      (P := P) Ψ hdk hds v)]
  push_cast
  apply Finset.sum_congr rfl
  intro v hv
  exact ford_character_collision_mean_eq
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS3ResidueMoment (k := k) hds q v :
      FordS3ResidueTuple d s Q p hds v → Fin k → ℤ)

#print axioms fordS3ResidueMajorant_eq_collisionSum

end

end GafniTao

import GafniTao.FordEquation34Fourier
import GafniTao.FordFourierCollision

/-!
# Ford equation (3.4): the `S_4(c,p)` collision count

The Fourier integral in equation (3.4) is identified here with an explicit
finite solution type.  Its first variables are the nonsingular polynomial
box and its second variables are literal integers in `[1,Q]`, all lying in
the fixed residue class `c (mod p)`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordS4ResidueTuple (s Q p : ℕ) (c : ZMod p) :=
  Fin s → FordResidueInterval Q p c

def fordS4ResidueMoment {k s Q p : ℕ} (q : ℕ) (c : ZMod p)
    (x : FordS4ResidueTuple s Q p c) : Fin k → ℤ :=
  fun j => ∑ i : Fin s,
    ((q ^ ((j : ℕ) + 1) *
      ((x i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)

def fordS4PolynomialMoment
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (z : FordS3PolynomialBox k d P p hdk) : Fin k → ℤ :=
  fordPolynomialMoment Ψ z.1

/-- The literal finite collision count represented by Ford's `S_4(c,p)`.
The defining equality is the complete degree-by-degree equation, with both
ordered halves and the fixed residue class retained in the variable type. -/
def fordS4Count
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) (c : ZMod p) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS4ResidueMoment (k := k) q c :
      FordS4ResidueTuple s Q p c → Fin k → ℤ))

theorem fordS4ResidueMoment_eq_sum
    {k s Q p : ℕ} (q : ℕ) (c : ZMod p)
    (x : FordS4ResidueTuple s Q p c) :
    fordS4ResidueMoment (k := k) q c x =
      ∑ i : Fin s, fun j : Fin k =>
        ((q ^ ((j : ℕ) + 1) *
          ((x i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
  ext j
  simp [fordS4ResidueMoment]

theorem fordS4Residue_prod_character
    {k s Q p : ℕ} (q : ℕ) (c : ZMod p)
    (x : FordS4ResidueTuple s Q p c)
    (α : UnitAddTorus (Fin k)) :
    ∏ i : Fin s,
        UnitAddTorus.mFourier
          (fun j : Fin k =>
            ((q ^ ((j : ℕ) + 1) *
              ((x i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) α =
      UnitAddTorus.mFourier (fordS4ResidueMoment (k := k) q c x) α := by
  rw [fordS4ResidueMoment_eq_sum]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        UnitAddTorus.mFourier_add]
      exact congrArg (fun z =>
        UnitAddTorus.mFourier
          (fun j : Fin k =>
            ((q ^ ((j : ℕ) + 1) *
              ((x i).1.1 + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) α * z) ih

theorem fordResidueWeylSum_pow
    (s k Q q p : ℕ) (c : ZMod p) (α : UnitAddTorus (Fin k)) :
    fordResidueWeylSum k Q q p c α ^ s =
      fordCharacterSum
        (fordS4ResidueMoment (k := k) q c :
          FordS4ResidueTuple s Q p c → Fin k → ℤ) α := by
  unfold fordResidueWeylSum fordCharacterSum
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact fordS4Residue_prod_character q c x α

theorem fordPolynomialWeylSum_eq_characterSum
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (α : UnitAddTorus (Fin k)) :
    fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α =
      fordCharacterSum
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk) α := rfl

/-- The exact Fourier-orthogonality bridge for Ford's `S_4(c,p)`. -/
theorem fordS4Fourier_eq_count
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) (c : ZMod p) :
    fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c =
      (fordS4Count (P := P) Ψ hdk s Q q c : ℝ) := by
  unfold fordS4Fourier fordS4Count
  let M := fordS4PolynomialMoment (P := P) (p := p) Ψ hdk
  let N : FordS4ResidueTuple s Q p c → Fin k → ℤ :=
    fordS4ResidueMoment (k := k) q c
  have hmean := ford_character_collision_mean_eq M N
  rw [← hmean]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with α
  rw [fordPolynomialWeylSum_eq_characterSum]
  rw [← fordResidueWeylSum_pow s k Q q p c α]
  simp only [M, norm_pow]
  rw [← pow_mul]
  congr 2
  omega

#print axioms fordS4Fourier_eq_count

end

end GafniTao

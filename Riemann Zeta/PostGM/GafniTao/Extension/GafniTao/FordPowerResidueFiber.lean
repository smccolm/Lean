import GafniTao.FordNewtonCongruence

/-!
# Ford Lemma 3.2: the residue power-sum fibre

This file formalizes the quantitative Newton step in Ford's proof of (3.4).
The first `d` coordinates and the remaining `s-d` coordinates are displayed
separately, exactly as in the paper's argument that first fixes
`c_{d+1},...,c_s`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def FordBCondition (p d s : ℕ) (v : Fin d → ZMod p)
    (c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p)) : Prop :=
  ∀ j : Fin d,
    fordPowerSum c.1 ((j : ℕ) + 1) +
      fordPowerSum c.2 ((j : ℕ) + 1) = v j

def FordBResidueClass (p d s : ℕ) (v : Fin d → ZMod p) :=
  {c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p) //
    FordBCondition p d s v c}

def FordBHeadFiber (p d s : ℕ) (v : Fin d → ZMod p)
    (tail : Fin (s - d) → ZMod p) :=
  {head : Fin d → ZMod p // FordBCondition p d s v (head, tail)}

theorem fordB_head_powerSums_eq
    {p d s : ℕ} {v : Fin d → ZMod p}
    {tail : Fin (s - d) → ZMod p}
    (c c' : FordBHeadFiber p d s v tail) :
    ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c.1 r = fordPowerSum c'.1 r := by
  intro r hr1 hrd
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_one.mpr hr1
  have hjd : j < d := by omega
  let i : Fin d := ⟨j, hjd⟩
  have hc := c.2 i
  have hc' := c'.2 i
  change fordPowerSum c.1 (j + 1) + fordPowerSum tail (j + 1) = v i at hc
  change fordPowerSum c'.1 (j + 1) + fordPowerSum tail (j + 1) = v i at hc'
  rw [hj]
  exact add_right_cancel (hc.trans hc'.symm)

theorem fordB_headFiber_card_le_factorial
    {p d s : ℕ} (hp : Nat.Prime p) (hdp : d < p)
    (v : Fin d → ZMod p) (tail : Fin (s - d) → ZMod p) :
    Nat.card (FordBHeadFiber p d s v tail) ≤ Nat.factorial d := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hne : Nonempty (FordBHeadFiber p d s v tail)
  · let c₀ : FordBHeadFiber p d s v tail := Classical.choice hne
    let embed : FordBHeadFiber p d s v tail → FordPowerSumFiber p d c₀.1 :=
      fun c => ⟨c.1, fordB_head_powerSums_eq c c₀⟩
    have hinj : Function.Injective embed := by
      intro c c' h
      apply Subtype.ext
      exact congrArg (fun x : FordPowerSumFiber p d c₀.1 => x.1) h
    letI : Finite (FordPowerSumFiber p d c₀.1) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact (Nat.card_le_card_of_injective embed hinj).trans
      (ford_powerSumFiber_card_le_factorial hp hdp c₀.1)
  · haveI : IsEmpty (FordBHeadFiber p d s v tail) := not_nonempty_iff.mp hne
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    exact Nat.zero_le _

def fordBResidueClassEquivSigma
    (p d s : ℕ) (v : Fin d → ZMod p) :
    FordBResidueClass p d s v ≃
      Σ tail : Fin (s - d) → ZMod p, FordBHeadFiber p d s v tail where
  toFun c := ⟨c.1.2, ⟨c.1.1, c.2⟩⟩
  invFun c := ⟨(c.2.1, c.1), c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Ford's source bound `|B_s(w)| ≤ d! p^(s-d)`. -/
theorem fordBResidueClass_card_le
    {p d s : ℕ} (hp : Nat.Prime p) (hdp : d < p)
    (v : Fin d → ZMod p) :
    Nat.card (FordBResidueClass p d s v) ≤
      Nat.factorial d * p ^ (s - d) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let tails := Fin (s - d) → ZMod p
  letI : Fintype tails := Fintype.ofFinite _
  letI (tail : tails) : Finite (FordBHeadFiber p d s v tail) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard : Nat.card (FordBResidueClass p d s v) =
      ∑ tail : tails, Nat.card (FordBHeadFiber p d s v tail) := by
    rw [Nat.card_congr (fordBResidueClassEquivSigma p d s v), Nat.card_sigma]
  have htails : Fintype.card tails = p ^ (s - d) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hcard]
  calc
    (∑ tail : tails, Nat.card (FordBHeadFiber p d s v tail)) ≤
        ∑ _tail : tails, Nat.factorial d :=
      Finset.sum_le_sum fun tail _ => fordB_headFiber_card_le_factorial hp hdp v tail
    _ = Nat.factorial d * p ^ (s - d) := by
      rw [sum_const, card_univ]
      change Fintype.card tails * Nat.factorial d =
        Nat.factorial d * p ^ (s - d)
      rw [htails, Nat.mul_comm]

#print axioms fordB_head_powerSums_eq
#print axioms fordB_headFiber_card_le_factorial
#print axioms fordBResidueClass_card_le

end

end GafniTao

import GafniTao.FordEquation34S3Count

/-!
# Ford equation (3.4): the literal source `S_3(p)` count

This file connects the unrestricted integer variables in Ford's `S_3(p)`
to the residue-fibre collision sum.  The first `d` equations of a system of
type `(d,T)` contain no polynomial contribution; positivity of `q` therefore
forces the two integer tuples to have the same first `d` power sums.  This is
the missing source-to-Fourier entry bridge for equation (3.4).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordS3BoxMoment {k s Q : ℕ} (q : ℕ) (x : FordBox s Q) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s,
    ((q ^ ((j : ℕ) + 1) *
      fordBoxValue x i ^ ((j : ℕ) + 1) : ℕ) : ℤ)

/-- The literal finite solution count denoted `S_3(p)` in Ford's proof. -/
def fordS3Count
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) : ℕ :=
  Nat.card (FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ))

def fordBoxSplitResidue {d s Q p : ℕ} (hds : d ≤ s)
    (x : FordBox s Q) :
    (Fin d → ZMod p) × (Fin (s - d) → ZMod p) :=
  (fordBJoinEquiv hds).symm
    (fun i => (fordBoxValue x i : ZMod p))

def fordBoxBSignature {d s Q p : ℕ} (hds : d ≤ s)
    (x : FordBox s Q) : Fin d → ZMod p :=
  fordBSignature p d s (fordBoxSplitResidue (p := p) hds x)

theorem fordBJoin_boxSplitResidue {d s Q p : ℕ} (hds : d ≤ s)
    (x : FordBox s Q) :
    fordBJoin hds (fordBoxSplitResidue (p := p) hds x) =
      fun i => (fordBoxValue x i : ZMod p) := by
  exact (fordBJoinEquiv hds).apply_symm_apply _

theorem fordPowerSum_BJoin {d s p : ℕ} (hds : d ≤ s)
    (c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p)) (J : ℕ) :
    fordPowerSum c.1 J + fordPowerSum c.2 J =
      ∑ i : Fin s, (fordBJoin hds c i) ^ J := by
  unfold fordPowerSum fordBJoin
  calc
    (∑ i : Fin d, c.1 i ^ J) + ∑ i : Fin (s - d), c.2 i ^ J =
        ∑ i : Fin d ⊕ Fin (s - d), (Sum.elim c.1 c.2 i) ^ J := by
      rw [Fintype.sum_sum_type]
      simp
    _ = _ := by
      let e : Fin d ⊕ Fin (s - d) ≃ Fin s :=
        finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hds))
      simpa [e, fordBJoin] using Equiv.sum_comp e
        (fun i : Fin s => (fordBJoin hds c i) ^ J)

def fordBoxToS3ResidueTuple {d s Q p : ℕ} (hds : d ≤ s)
    (v : Fin d → ZMod p) (x : FordBox s Q)
    (hx : fordBoxBSignature (p := p) hds x = v) :
    FordS3ResidueTuple d s Q p hds v := by
  let c₀ := fordBoxSplitResidue (p := p) hds x
  let c : FordBResidueClass p d s v :=
    ⟨c₀, fun j => congrFun hx j⟩
  refine ⟨c, fun i => ⟨x i, ?_⟩⟩
  change (fordBoxValue x i : ZMod p) = fordBJoin hds c₀ i
  exact (congrFun (fordBJoin_boxSplitResidue (p := p) hds x) i).symm

@[simp] theorem fordBoxToS3ResidueTuple_value
    {d s Q p : ℕ} (hds : d ≤ s) (v : Fin d → ZMod p)
    (x : FordBox s Q) (hx : fordBoxBSignature (p := p) hds x = v)
    (i : Fin s) :
    ((fordBoxToS3ResidueTuple hds v x hx).2 i).1 = x i := rfl

theorem fordS3ResidueMoment_box
    {k d s Q p : ℕ} (hds : d ≤ s) (q : ℕ)
    (v : Fin d → ZMod p) (x : FordBox s Q)
    (hx : fordBoxBSignature (p := p) hds x = v) :
    fordS3ResidueMoment (k := k) hds q v
        (fordBoxToS3ResidueTuple hds v x hx) =
      fordS3BoxMoment (k := k) q x := by
  ext j
  simp [fordS3ResidueMoment, fordS3BoxMoment]

theorem fordBoxBSignature_eq_of_collision
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (hq : 0 < q)
    (z w : FordS3PolynomialBox k d P p hdk) (x y : FordBox s Q)
    (hcollision :
      fordS4PolynomialMoment (P := P) (p := p) Ψ hdk z +
          fordS3BoxMoment (k := k) q x =
        fordS4PolynomialMoment (P := P) (p := p) Ψ hdk w +
          fordS3BoxMoment (k := k) q y) :
    fordBoxBSignature (p := p) hds x =
      fordBoxBSignature (p := p) hds y := by
  funext j
  have hjk : (j : ℕ) < k := lt_of_lt_of_le j.isLt hdk
  let J : Fin k := ⟨j, hjk⟩
  have hJ := congrFun hcollision J
  have hJle : (J : ℕ) + 1 ≤ d := by
    dsimp [J]
    omega
  have hzero := Ψ.zero_below J hJle
  have hz : fordS4PolynomialMoment (P := P) (p := p) Ψ hdk z J = 0 := by
    simp [fordS4PolynomialMoment, fordPolynomialMoment,
      fordPolynomialSumInt, hzero]
  have hw : fordS4PolynomialMoment (P := P) (p := p) Ψ hdk w J = 0 := by
    simp [fordS4PolynomialMoment, fordPolynomialMoment,
      fordPolynomialSumInt, hzero]
  change fordS4PolynomialMoment (P := P) (p := p) Ψ hdk z J +
      fordS3BoxMoment (k := k) q x J =
    fordS4PolynomialMoment (P := P) (p := p) Ψ hdk w J +
      fordS3BoxMoment (k := k) q y J at hJ
  rw [hz, hw, zero_add, zero_add] at hJ
  have hqpow : (q : ℤ) ^ ((j : ℕ) + 1) ≠ 0 := by
    exact pow_ne_zero _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hq))
  have hpowers :
      ∑ i : Fin s, (fordBoxValue x i : ℤ) ^ ((j : ℕ) + 1) =
        ∑ i : Fin s, (fordBoxValue y i : ℤ) ^ ((j : ℕ) + 1) := by
    apply mul_left_cancel₀ hqpow
    rw [show fordS3BoxMoment (k := k) q x J =
        (q : ℤ) ^ ((j : ℕ) + 1) *
          ∑ i : Fin s, (fordBoxValue x i : ℤ) ^ ((j : ℕ) + 1) by
      simp [fordS3BoxMoment, Finset.mul_sum, J]] at hJ
    rw [show fordS3BoxMoment (k := k) q y J =
        (q : ℤ) ^ ((j : ℕ) + 1) *
          ∑ i : Fin s, (fordBoxValue y i : ℤ) ^ ((j : ℕ) + 1) by
      simp [fordS3BoxMoment, Finset.mul_sum, J]] at hJ
    exact hJ
  unfold fordBoxBSignature fordBSignature
  rw [fordPowerSum_BJoin hds, fordPowerSum_BJoin hds]
  rw [fordBJoin_boxSplitResidue, fordBJoin_boxSplitResidue]
  have hpowersMod := congrArg (Int.castRingHom (ZMod p)) hpowers
  simpa using hpowersMod

def fordS3ResidueTupleToBox
    {d s Q p : ℕ} {hds : d ≤ s} {v : Fin d → ZMod p}
    (x : FordS3ResidueTuple d s Q p hds v) : FordBox s Q :=
  fun i => (x.2 i).1

@[simp] theorem fordS3ResidueTupleToBox_value
    {d s Q p : ℕ} {hds : d ≤ s} {v : Fin d → ZMod p}
    (x : FordS3ResidueTuple d s Q p hds v) (i : Fin s) :
    fordS3ResidueTupleToBox x i = (x.2 i).1 := rfl

theorem fordS3BoxMoment_residueTuple
    {k d s Q p : ℕ} (hds : d ≤ s) (q : ℕ)
    (v : Fin d → ZMod p) (x : FordS3ResidueTuple d s Q p hds v) :
    fordS3BoxMoment (k := k) q (fordS3ResidueTupleToBox x) =
      fordS3ResidueMoment (k := k) hds q v x := by
  ext j
  simp [fordS3BoxMoment, fordS3ResidueMoment,
    fordS3ResidueTupleToBox]

def fordS3CollisionToResidue
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (hq : 0 < q)
    (u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)) :
    Σ v : Fin d → ZMod p,
      FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
        (fordS3ResidueMoment (k := k) hds q v :
          FordS3ResidueTuple d s Q p hds v → Fin k → ℤ) := by
  let z := u.1.1.1
  let x := u.1.1.2
  let w := u.1.2.1
  let y := u.1.2.2
  let v := fordBoxBSignature (p := p) hds x
  have hy : fordBoxBSignature (p := p) hds y = v :=
    (fordBoxBSignature_eq_of_collision Ψ hdk hds hq z w x y u.2).symm
  let xr := fordBoxToS3ResidueTuple hds v x rfl
  let yr := fordBoxToS3ResidueTuple hds v y hy
  refine ⟨v, ⟨((z, xr), (w, yr)), ?_⟩⟩
  change fordS4PolynomialMoment (P := P) (p := p) Ψ hdk z +
      fordS3ResidueMoment (k := k) hds q v xr =
    fordS4PolynomialMoment (P := P) (p := p) Ψ hdk w +
      fordS3ResidueMoment (k := k) hds q v yr
  rw [fordS3ResidueMoment_box, fordS3ResidueMoment_box]
  exact u.2

def fordResidueCollisionToS3
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s)
    (u : Σ v : Fin d → ZMod p,
      FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
        (fordS3ResidueMoment (k := k) hds q v :
          FordS3ResidueTuple d s Q p hds v → Fin k → ℤ)) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) := by
  refine ⟨((u.2.1.1.1, fordS3ResidueTupleToBox u.2.1.1.2),
      (u.2.1.2.1, fordS3ResidueTupleToBox u.2.1.2.2)), ?_⟩
  change fordS4PolynomialMoment (P := P) (p := p) Ψ hdk u.2.1.1.1 +
      fordS3BoxMoment (k := k) q (fordS3ResidueTupleToBox u.2.1.1.2) =
    fordS4PolynomialMoment (P := P) (p := p) Ψ hdk u.2.1.2.1 +
      fordS3BoxMoment (k := k) q (fordS3ResidueTupleToBox u.2.1.2.2)
  rw [fordS3BoxMoment_residueTuple, fordS3BoxMoment_residueTuple]
  exact u.2.2

theorem fordResidueCollisionToS3_leftInverse
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (hq : 0 < q) :
    Function.LeftInverse
      (fordResidueCollisionToS3 (P := P) (p := p) (Q := Q) Ψ hdk hds)
      (fordS3CollisionToResidue (P := P) (p := p) (Q := Q)
        Ψ hdk hds hq) := by
  intro u
  apply Subtype.ext
  rfl

/-- The paper's source `S_3(p)` solutions inject into the complete
residue-fibre collision sum that precedes equation (3.4). -/
theorem fordS3Count_le_residueCollisionSum
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (hq : 0 < q) :
    fordS3Count (P := P) (p := p) Ψ hdk s Q q ≤
      fordS3ResidueCollisionSum (P := P) (p := p)
        Ψ hdk s Q q hds := by
  let source := FordCharacterCollision
    (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
    (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)
  let target := Σ v : Fin d → ZMod p,
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS3ResidueMoment (k := k) hds q v :
        FordS3ResidueTuple d s Q p hds v → Fin k → ℤ)
  have hinj : Function.Injective
      (fordS3CollisionToResidue (P := P) (p := p) Ψ hdk hds hq) :=
    (fordResidueCollisionToS3_leftInverse
      (P := P) (p := p) (Q := Q) Ψ hdk hds hq).injective
  change Nat.card source ≤ _
  calc
    Nat.card source ≤ Nat.card target :=
      Nat.card_le_card_of_injective _ hinj
    _ = ∑ v : Fin d → ZMod p,
        Nat.card (FordCharacterCollision
          (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
          (fordS3ResidueMoment (k := k) hds q v :
            FordS3ResidueTuple d s Q p hds v → Fin k → ℤ)) := by
      rw [Nat.card_sigma]
    _ = _ := rfl

#print axioms fordS3Count_le_residueCollisionSum

theorem fordS3Count_cast_le_residueMajorant
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hds : d ≤ s) (hq : 0 < q) :
    (fordS3Count (P := P) (p := p) Ψ hdk s Q q : ℝ) ≤
      fordS3ResidueMajorant (P := P) (p := p) Ψ hdk s Q q hds := by
  rw [fordS3ResidueMajorant_eq_collisionSum]
  exact_mod_cast fordS3Count_le_residueCollisionSum Ψ hdk hds hq

/-- Ford equation (3.4) for the literal source `S_3(p)` and `S_4(c,p)`
counts, with the exact coefficient `d! p^(2s-d)`. -/
theorem ford_equation_3_4_source
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (hs : 0 < s) (hds : d ≤ s) (hq : 0 < q)
    (hp : Nat.Prime p) (hdp : d < p) :
    ∃ c : ZMod p,
      (fordS3Count (P := P) (p := p) Ψ hdk s Q q : ℝ) ≤
        (Nat.factorial d : ℝ) * (p : ℝ) ^ (2 * s - d) *
          fordS4Count (P := P) Ψ hdk s Q q c := by
  obtain ⟨c, hc⟩ := ford_equation_3_4 Ψ hdk hs hds hp hdp
  refine ⟨c, (fordS3Count_cast_le_residueMajorant Ψ hdk hds hq).trans ?_⟩
  rw [fordS4Fourier_eq_count] at hc
  exact hc

#print axioms ford_equation_3_4_source

end

end GafniTao

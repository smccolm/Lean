import GafniTao.FordEquation37Source
import GafniTao.FordPrimeSelection

/-!
# Ford equation (3.3): the nonsingular source class

This file constructs the literal distinct-coordinate class of equation (3.1),
selects an avoiding prime for each such solution, and embeds the class into
the disjoint union of the source `S₃(p)` collision types.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordKSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :=
  {v : FordKVariables k s P Q // FordKEquation Ψ q v}

abbrev FordKDistinctSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :=
  {u : FordKSolution Ψ s P Q q //
    FordTuplePairwiseDistinct u.1.1.1 ∧
      FordTuplePairwiseDistinct u.1.1.2}

def fordHeadBox {k d P : ℕ} (hdk : d ≤ k) (z : FordBox k P) :
    FordBox (k - d) P :=
  fun i ↦ z (fordHeadIndex hdk i)

theorem fordHeadBox_pairwiseDistinct
    {k d P : ℕ} (hdk : d ≤ k) (z : FordBox k P)
    (hz : FordTuplePairwiseDistinct z) :
    FordTuplePairwiseDistinct (fordHeadBox hdk z) := by
  intro i j hij
  have hhead : fordHeadIndex hdk i = fordHeadIndex hdk j := hz hij
  have hsum : (Sum.inl i : Fin (k - d) ⊕ Fin d) = Sum.inl j :=
    (fordSplitFinEquiv hdk).injective hhead
  exact Sum.inl_injective hsum

theorem ford_prime_dvd_vandermonde_of_residue_collision
    {n P p : ℕ} (z : FordBox n P) {i j : Fin n}
    (hij : i ≠ j)
    (hres : (fordBoxValue z i : ZMod p) =
      (fordBoxValue z j : ZMod p)) :
    p ∣ fordVandermondeNatAbs z := by
  have hmod : Nat.ModEq p (fordBoxValue z i) (fordBoxValue z j) :=
    (ZMod.natCast_eq_natCast_iff _ _ p).mp hres
  have hdInt : (p : ℤ) ∣
      (fordBoxValue z j : ℤ) - (fordBoxValue z i : ℤ) :=
    Nat.modEq_iff_dvd.mp hmod
  have hdAbs : p ∣ Int.natAbs
      ((fordBoxValue z j : ℤ) - (fordBoxValue z i : ℤ)) := by
    have h := Int.natAbs_dvd_natAbs.mpr hdInt
    simpa using h
  unfold fordVandermondeNatAbs
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hinner :
        Int.natAbs ((fordBoxValue z j : ℤ) -
            (fordBoxValue z i : ℤ)) ∣
          ∏ b ∈ Finset.Ioi i,
            Int.natAbs ((fordBoxValue z b : ℤ) -
              (fordBoxValue z i : ℤ)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_Ioi.mpr hijlt)
    exact hdAbs.trans (hinner.trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  · have hmod' : Nat.ModEq p (fordBoxValue z j) (fordBoxValue z i) :=
      hmod.symm
    have hdInt' : (p : ℤ) ∣
        (fordBoxValue z i : ℤ) - (fordBoxValue z j : ℤ) :=
      Nat.modEq_iff_dvd.mp hmod'
    have hdAbs' : p ∣ Int.natAbs
        ((fordBoxValue z i : ℤ) - (fordBoxValue z j : ℤ)) := by
      have h := Int.natAbs_dvd_natAbs.mpr hdInt'
      simpa using h
    have hinner :
        Int.natAbs ((fordBoxValue z i : ℤ) -
            (fordBoxValue z j : ℤ)) ∣
          ∏ b ∈ Finset.Ioi j,
            Int.natAbs ((fordBoxValue z b : ℤ) -
              (fordBoxValue z j : ℤ)) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_Ioi.mpr hjilt)
    exact hdAbs'.trans (hinner.trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))

theorem ford_head_residue_injective_of_not_dvd_vandermonde
    {n P p : ℕ} (z : FordBox n P)
    (hp : ¬p ∣ fordVandermondeNatAbs z) :
    Function.Injective (fun i : Fin n ↦ (fordBoxValue z i : ZMod p)) := by
  intro i j hij
  by_contra hne
  exact hp (ford_prime_dvd_vandermonde_of_residue_collision z hne hij)

theorem ford_not_dvd_left_vandermonde_of_not_dvd_avoidance
    {k d T P p : ℕ} (z w : FordBox (k - d) P)
    (h : ¬p ∣ fordJacobianAvoidanceNat (T := T) z w) :
    ¬p ∣ fordVandermondeNatAbs z := by
  intro hz
  rcases hz with ⟨a, ha⟩
  apply h
  refine ⟨T * a * fordVandermondeNatAbs w, ?_⟩
  unfold fordJacobianAvoidanceNat
  rw [ha]
  ring

theorem ford_not_dvd_right_vandermonde_of_not_dvd_avoidance
    {k d T P p : ℕ} (z w : FordBox (k - d) P)
    (h : ¬p ∣ fordJacobianAvoidanceNat (T := T) z w) :
    ¬p ∣ fordVandermondeNatAbs w := by
  intro hw
  rcases hw with ⟨a, ha⟩
  apply h
  refine ⟨T * fordVandermondeNatAbs z * a, ?_⟩
  unfold fordJacobianAvoidanceNat
  rw [ha]
  ring

def fordKDistinctToS3At
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (u : FordKDistinctSolution Ψ s P Q q)
    (havoid : ¬p ∣ fordJacobianAvoidanceNat (T := T)
      (fordHeadBox hdk u.1.1.1.1) (fordHeadBox hdk u.1.1.1.2)) :
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) := by
  let z := u.1.1.1.1
  let w := u.1.1.1.2
  let x := u.1.1.2.1
  let y := u.1.1.2.2
  have hzAvoid : ¬p ∣ fordVandermondeNatAbs (fordHeadBox hdk z) :=
    ford_not_dvd_left_vandermonde_of_not_dvd_avoidance
      (fordHeadBox hdk z) (fordHeadBox hdk w) havoid
  have hwAvoid : ¬p ∣ fordVandermondeNatAbs (fordHeadBox hdk w) :=
    ford_not_dvd_right_vandermonde_of_not_dvd_avoidance
      (fordHeadBox hdk z) (fordHeadBox hdk w) havoid
  have hzResidue : Function.Injective (fun i : Fin (k - d) ↦
      (fordBoxValue z (fordHeadIndex hdk i) : ZMod p)) := by
    simpa [fordHeadBox] using
      ford_head_residue_injective_of_not_dvd_vandermonde
        (fordHeadBox hdk z) hzAvoid
  have hwResidue : Function.Injective (fun i : Fin (k - d) ↦
      (fordBoxValue w (fordHeadIndex hdk i) : ZMod p)) := by
    simpa [fordHeadBox] using
      ford_head_residue_injective_of_not_dvd_vandermonde
        (fordHeadBox hdk w) hwAvoid
  let z' : FordS3PolynomialBox k d P p hdk := ⟨z, hzResidue⟩
  let w' : FordS3PolynomialBox k d P p hdk := ⟨w, hwResidue⟩
  refine ⟨((z', x), (w', y)), ?_⟩
  funext j
  have hj := u.1.2 j
  have hxMoment : fordS3BoxMoment (k := k) q x j =
      (q : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerSumInt x ((j : ℕ) + 1) := by
    simp [fordS3BoxMoment, fordPowerSumInt, Finset.mul_sum]
  have hyMoment : fordS3BoxMoment (k := k) q y j =
      (q : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerSumInt y ((j : ℕ) + 1) := by
    simp [fordS3BoxMoment, fordPowerSumInt, Finset.mul_sum]
  change fordS4PolynomialMoment Ψ hdk z' j + fordS3BoxMoment q x j =
    fordS4PolynomialMoment Ψ hdk w' j + fordS3BoxMoment q y j
  rw [hxMoment, hyMoment]
  change fordPolynomialSumInt Ψ z j +
      (q : ℤ) ^ ((j : ℕ) + 1) * fordPowerSumInt x ((j : ℕ) + 1) =
    fordPolynomialSumInt Ψ w j +
      (q : ℤ) ^ ((j : ℕ) + 1) * fordPowerSumInt y ((j : ℕ) + 1)
  rw [← sub_eq_zero]
  unfold fordPolynomialDifference fordPowerDifference at hj
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hj
  change fordPolynomialSumInt Ψ z j +
      (q : ℤ) ^ ((j : ℕ) + 1) * fordPowerSumInt x ((j : ℕ) + 1) -
    (fordPolynomialSumInt Ψ w j +
      (q : ℤ) ^ ((j : ℕ) + 1) * fordPowerSumInt y ((j : ℕ) + 1)) = 0
  dsimp [z, w, x, y] at hj ⊢
  unfold fordPolynomialSumInt fordPowerSumInt
  simp only [fordBoxValue, Nat.cast_add, Nat.cast_one] at hj ⊢
  linear_combination hj

theorem fordKDistinctToS3At_injective
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (chooseAvoid : ∀ u : FordKDistinctSolution Ψ s P Q q,
      ¬p ∣ fordJacobianAvoidanceNat (T := T)
        (fordHeadBox hdk u.1.1.1.1) (fordHeadBox hdk u.1.1.1.2)) :
    Function.Injective (fun u ↦ fordKDistinctToS3At Ψ hdk u (chooseAvoid u)) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  have hval := congrArg (fun t ↦
    ((t.1.1.1.1, t.1.2.1.1), (t.1.1.2, t.1.2.2))) huv
  dsimp only [fordKDistinctToS3At] at hval
  simpa only [Prod.eta] using hval

theorem exists_fordAvoidingPrime
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) :
    ∃ p : {p : ℕ // p ∈ S},
      ¬(p : ℕ) ∣ fordJacobianAvoidanceNat (T := T)
        (fordHeadBox hdk u.1.1.1.1) (fordHeadBox hdk u.1.1.1.2) := by
  have hz : FordTuplePairwiseDistinct
      (fordHeadBox hdk u.1.1.1.1) :=
    fordHeadBox_pairwiseDistinct hdk _ u.2.1
  have hw : FordTuplePairwiseDistinct
      (fordHeadBox hdk u.1.1.1.2) :=
    fordHeadBox_pairwiseDistinct hdk _ u.2.2
  obtain ⟨p, hpS, hp⟩ := exists_ford_prime_avoiding_jacobian
    hprime hsource hTpos hT
    (fordHeadBox hdk u.1.1.1.1) (fordHeadBox hdk u.1.1.1.2) hz hw
  exact ⟨⟨p, hpS⟩, hp⟩

noncomputable def fordAvoidingPrime
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) : {p : ℕ // p ∈ S} :=
  Classical.choose
    (exists_fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u)

theorem fordAvoidingPrime_property
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) :
    ¬(fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u : ℕ) ∣
      fordJacobianAvoidanceNat (T := T)
        (fordHeadBox hdk u.1.1.1.1) (fordHeadBox hdk u.1.1.1.2) := by
  exact Classical.choose_spec
    (exists_fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u)

noncomputable def fordKDistinctToPrimeS3
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) :
    Σ p : {p : ℕ // p ∈ S},
      FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p.1) Ψ hdk)
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) := by
  let p := fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u
  exact ⟨p, fordKDistinctToS3At Ψ hdk u
    (fordAvoidingPrime_property S Ψ hdk hprime hsource hTpos hT u)⟩

theorem fordKDistinctToPrimeS3_injective
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d) :
    Function.Injective
      (fordKDistinctToPrimeS3 (s := s) (Q := Q) (q := q)
        S Ψ hdk hprime hsource hTpos hT) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  have hval := congrArg (fun t ↦
    ((t.2.val.1.1.val, t.2.val.2.1.val),
      (t.2.val.1.2, t.2.val.2.2))) huv
  dsimp only [fordKDistinctToPrimeS3, fordKDistinctToS3At] at hval
  simpa only [Prod.eta] using hval

theorem ford_distinct_count_le_sum_S3
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d) :
    Nat.card (FordKDistinctSolution Ψ s P Q q) ≤
      ∑ p ∈ S, fordS3Count (P := P) (p := p) Ψ hdk s Q q := by
  let target := Σ p : {p : ℕ // p ∈ S},
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p.1) Ψ hdk)
      (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)
  have hinj := fordKDistinctToPrimeS3_injective
    (s := s) (Q := Q) (q := q) S Ψ hdk hprime hsource hTpos hT
  calc
    Nat.card (FordKDistinctSolution Ψ s P Q q) ≤ Nat.card target :=
      Nat.card_le_card_of_injective _ hinj
    _ = ∑ p : {p : ℕ // p ∈ S},
        Nat.card (FordCharacterCollision
          (fordS4PolynomialMoment (P := P) (p := p.1) Ψ hdk)
          (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)) := by
      rw [Nat.card_sigma]
    _ = ∑ p ∈ S, fordS3Count (P := P) (p := p) Ψ hdk s Q q := by
      change (∑ p : {p : ℕ // p ∈ S},
        fordS3Count (P := P) (p := p.1) Ψ hdk s Q q) = _
      conv_rhs => rw [← Finset.sum_attach]
      simp

theorem ford_equation_3_3_distinct
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hS : S.Nonempty) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d) :
    ∃ p ∈ S,
      Nat.card (FordKDistinctSolution Ψ s P Q q) ≤
        S.card * fordS3Count (P := P) (p := p) Ψ hdk s Q q := by
  obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image S
    (fun p ↦ fordS3Count (P := P) (p := p) Ψ hdk s Q q) hS
  refine ⟨p, hpS, (ford_distinct_count_le_sum_S3
    S Ψ hdk hprime hsource hTpos hT).trans ?_⟩
  simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul S
    (fun a ↦ fordS3Count (P := P) (p := a) Ψ hdk s Q q)
    (fordS3Count (P := P) (p := p) Ψ hdk s Q q)
    (fun a ha ↦ hpmax a ha)

#print axioms ford_equation_3_3_distinct

#print axioms ford_prime_dvd_vandermonde_of_residue_collision
#print axioms ford_head_residue_injective_of_not_dvd_vandermonde
#print axioms fordKDistinctToS3At

end

end GafniTao

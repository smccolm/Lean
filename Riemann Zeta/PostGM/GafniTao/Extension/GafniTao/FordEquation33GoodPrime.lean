import GafniTao.FordKContradiction

/-!
# Ford equation (3.3): retain the good-prime witness

The original finite `S₃` sum forgets that the avoiding prime does not divide
the type parameter `T`.  Equation (3.7) needs precisely that fact.  This file
keeps it in the sigma index and only then performs the maximum selection.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordGoodPrime (S : Finset ℕ) (T : ℕ) :=
  {p : ℕ // p ∈ S ∧ ¬p ∣ T}

instance fordGoodPrimeFinite (S : Finset ℕ) (T : ℕ) :
    Finite (FordGoodPrime S T) :=
  Finite.of_injective
    (fun p : FordGoodPrime S T ↦ (⟨p.1, p.2.1⟩ : {n : ℕ // n ∈ S}))
    (by
      intro p q h
      apply Subtype.ext
      change p.1 = q.1
      simpa using congrArg Subtype.val h)

noncomputable instance fordGoodPrimeFintype (S : Finset ℕ) (T : ℕ) :
    Fintype (FordGoodPrime S T) := Fintype.ofFinite _

theorem fordAvoidingPrime_not_dvd_T
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) :
    ¬(fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u : ℕ) ∣ T := by
  intro hpT
  apply fordAvoidingPrime_property S Ψ hdk hprime hsource hTpos hT u
  unfold fordJacobianAvoidanceNat
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpT _) _

def fordKDistinctToGoodPrimeS3
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (u : FordKDistinctSolution Ψ s P Q q) :
    Σ p : FordGoodPrime S T,
      FordCharacterCollision
        (fordS4PolynomialMoment (P := P) (p := p.1) Ψ hdk)
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) := by
  let p := fordAvoidingPrime S Ψ hdk hprime hsource hTpos hT u
  let pg : FordGoodPrime S T :=
    ⟨p.1, p.2, fordAvoidingPrime_not_dvd_T S Ψ hdk hprime hsource hTpos hT u⟩
  exact ⟨pg, fordKDistinctToS3At Ψ hdk u
    (fordAvoidingPrime_property S Ψ hdk hprime hsource hTpos hT u)⟩

theorem fordKDistinctToGoodPrimeS3_injective
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d) :
    Function.Injective
      (fordKDistinctToGoodPrimeS3 (s := s) (Q := Q) (q := q)
        S Ψ hdk hprime hsource hTpos hT) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  have hval := congrArg (fun t ↦
    ((t.2.val.1.1.val, t.2.val.2.1.val),
      (t.2.val.1.2, t.2.val.2.2))) huv
  dsimp only [fordKDistinctToGoodPrimeS3, fordKDistinctToS3At] at hval
  simpa only [Prod.eta] using hval

theorem card_fordGoodPrime_le (S : Finset ℕ) (T : ℕ) :
    Nat.card (FordGoodPrime S T) ≤ S.card := by
  let e : FordGoodPrime S T → {p : ℕ // p ∈ S} := fun p ↦ ⟨p.1, p.2.1⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    change p.1 = q.1
    simpa [e] using congrArg Subtype.val h
  calc
    Nat.card (FordGoodPrime S T) ≤ Nat.card {p : ℕ // p ∈ S} :=
      Nat.card_le_card_of_injective e he
    _ = S.card := by simp [Nat.card_eq_fintype_card]

theorem ford_equation_3_3_distinct_good_prime
    {k d T P s Q q : ℕ} (S : Finset ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hD : 0 < Nat.card (FordKDistinctSolution Ψ s P Q q))
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hTpos : 0 < T) (hT : T ≤ P ^ d) :
    ∃ p ∈ S, ¬p ∣ T ∧
      Nat.card (FordKDistinctSolution Ψ s P Q q) ≤
        S.card * fordS3Count (P := P) (p := p) Ψ hdk s Q q := by
  let Good := FordGoodPrime S T
  let target := Σ p : Good,
    FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p.1) Ψ hdk)
      (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)
  have hinj := fordKDistinctToGoodPrimeS3_injective
    (s := s) (Q := Q) (q := q) S Ψ hdk hprime hsource hTpos hT
  have hGood : Nonempty Good := by
    have hDtype : Nonempty (FordKDistinctSolution Ψ s P Q q) :=
      Finite.card_pos_iff.mp hD
    exact ⟨(fordKDistinctToGoodPrimeS3 S Ψ hdk hprime hsource hTpos hT
      (Classical.choice hDtype)).1⟩
  letI : Nonempty Good := hGood
  obtain ⟨p, hpUniv, hpmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset Good)
    (fun a ↦ fordS3Count (P := P) (p := a.1) Ψ hdk s Q q)
    Finset.univ_nonempty
  refine ⟨p.1, p.2.1, p.2.2, ?_⟩
  calc
    Nat.card (FordKDistinctSolution Ψ s P Q q) ≤ Nat.card target :=
      Nat.card_le_card_of_injective _ hinj
    _ = ∑ a : Good, fordS3Count (P := P) (p := a.1) Ψ hdk s Q q := by
      rw [Nat.card_sigma]
      rfl
    _ ≤ Nat.card Good * fordS3Count (P := P) (p := p.1) Ψ hdk s Q q := by
      simpa [Nat.card_eq_fintype_card, nsmul_eq_mul] using
        Finset.sum_le_card_nsmul (Finset.univ : Finset Good)
          (fun a ↦ fordS3Count (P := P) (p := a.1) Ψ hdk s Q q)
          (fordS3Count (P := P) (p := p.1) Ψ hdk s Q q)
          (fun a _ ↦ hpmax a (Finset.mem_univ a))
    _ ≤ S.card * fordS3Count (P := P) (p := p.1) Ψ hdk s Q q := by
      exact Nat.mul_le_mul_right _ (card_fordGoodPrime_le S T)

#print axioms ford_equation_3_3_distinct_good_prime

end

end GafniTao

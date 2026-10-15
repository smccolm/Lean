/-
The intermediate-field argument adapts the final step of
anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_NumberField_exists_isCyclic_finrank_eq.lean.
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0.
The prescribed-degree cyclotomic construction below instead reuses native
primes-congruent-to-one and original primitive-root-stage results.
-/
import Dubon2026.OriginalCyclotomicPrimeStage
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Auxiliary cyclic number-field extensions of a prescribed degree

The auxiliary full-order-class transfer in DUB-17 needs a genuine cyclic
extension of prescribed degree. The pinned primes-congruent-to-one theorem,
the original primitive-root stage, and finite Galois correspondence construct
it directly. No local-degree specification or additional reciprocity theorem
is needed for this field-existence input.
-/

namespace Dubon2026
noncomputable section

/-- A degree divisor of an original finite cyclic Galois extension is realized by an actual intermediate field. -/
theorem originalCyclic_exists_intermediate_degree
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic Gal(L/K)] (n : ℕ) (hn : 0 < n)
    (hd : n ∣ Module.finrank K L) :
    ∃ F : IntermediateField K L, IsGalois K F ∧ IsCyclic Gal(F/K) ∧ Module.finrank K F = n := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(L/K))
  have hgn : n ∣ orderOf g := by rwa [hg, IsGalois.card_aut_eq_finrank]
  let H : Subgroup Gal(L/K) := Subgroup.zpowers (g ^ n)
  have hc : Nat.card H = Nat.card Gal(L/K) / n := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hn.ne' hgn, hg]
  have hi : H.index = n := by
    have hm := H.card_mul_index
    rw [hc] at hm
    have hnG : n ∣ Nat.card Gal(L/K) := hg ▸ hgn
    have hq : 0 < Nat.card Gal(L/K) / n := Nat.div_pos (Nat.le_of_dvd Nat.card_pos hnG) hn
    apply Nat.eq_of_mul_eq_mul_left hq
    exact hm.trans (Nat.div_mul_cancel hnG).symm
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  letI : H.Normal := inferInstance
  letI : IsCyclic (Gal(L/K) ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  let F := IntermediateField.fixedField H
  letI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  have hcyc : IsCyclic Gal(F/K) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (IsGalois.normalAutEquivQuotient H).surjective
  refine ⟨F, inferInstance, hcyc, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank K F,
    ← Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv,
    ← Subgroup.index_eq_card, hi]

/-- Every positive degree is realized by a constructed cyclic Galois number-field extension. -/
theorem originalNumberField_exists_cyclic_degree
    (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = n := by
  classical
  let d := Module.finrank ℚ K
  have hd : 0 < d := Module.finrank_pos
  obtain ⟨p, hp, hp2, hpmod⟩ := Nat.exists_prime_gt_modEq_one (k := n * d) 2 (mul_ne_zero hn.ne' hd.ne')
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  let F := originalPrimitiveRootStage K (AlgebraicClosure K) hμ
  letI : NumberField F := NumberField.of_module_finite K F
  let ν : F := originalPrimitiveRootStageRoot K (AlgebraicClosure K) hμ
  have hν : IsPrimitiveRoot ν p := originalPrimitiveRootStageRoot_isPrimitive K (AlgebraicClosure K) hμ
  have hcyc : IsCyclic Gal(F/K) := isCyclic_of_injective (hν.autToPow K) (hν.autToPow_injective K)
  letI := hcyc
  let C := originalPrimitiveRootStage ℚ F hν
  have hCcyc : @IsCyclotomicExtension {p} ℚ C _ _ C.algebra' :=
    originalPrimitiveRootStage_isCyclotomic ℚ F hν
  have hrat : (C.algebra' : Algebra ℚ C) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  letI : IsCyclotomicExtension {p} ℚ C := hrat ▸ hCcyc
  have hC : Module.finrank ℚ C = p - 1 := by
    rw [IsCyclotomicExtension.finrank (n := p) C (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.totient_prime hp]
  have hdiv : p - 1 ∣ Module.finrank ℚ F := by
    rw [← hC, ← Module.finrank_mul_finrank ℚ C F]
    exact dvd_mul_right _ _
  have hnd : n * d ∣ p - 1 := (Nat.modEq_iff_dvd' (show 1 ≤ p by omega)).mp hpmod.symm
  have hnF : n ∣ Module.finrank K F := by
    have h := hnd.trans hdiv
    rw [← Module.finrank_mul_finrank ℚ K F] at h
    rw [mul_comm n d] at h
    exact Nat.dvd_of_mul_dvd_mul_left hd h
  obtain ⟨L, hgal, hcyclic, hdegree⟩ := originalCyclic_exists_intermediate_degree K F n hn hnF
  letI : NumberField L := NumberField.of_module_finite K L
  exact ⟨L, inferInstance, inferInstance, inferInstance, hgal, hcyclic, hdegree⟩

end
end Dubon2026

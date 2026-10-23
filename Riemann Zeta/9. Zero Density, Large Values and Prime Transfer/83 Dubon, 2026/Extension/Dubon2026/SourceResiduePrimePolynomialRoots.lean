import Dubon2026.SourcePrimeResidueRelations
import Dubon2026.SourcePrimeConjugateRoots
import Mathlib.Algebra.Polynomial.Splits

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree. The specialized integral relation has exactly the
distinguished root j(q^(p²)) and the p twists of j(q). Both relation directions
come from the existing integral polynomial; existing simple-pole injectivity
proves distinctness in every characteristic. Root cardinality supplies splitting
without a second modular-polynomial construction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem residue_prime_polynomial_roots
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (P : Polynomial (Polynomial ℤ)) (hm : P.Monic) (hd : P.natDegree = p + 1)
    (hf : (relationAtSeed P (qExpand K p (jqModC K))).eval
      (qExpand K (p * p) (jqModC K)) = 0)
    (hr : (relationAtSeed P (qExpand K p (jqModC K))).eval (jqModC K) = 0) :
    (relationAtSeed P (qExpand K p (jqModC K))).roots =
      TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) := by
  classical
  let Q := relationAtSeed P (qExpand K p (jqModC K))
  have hQm : Q.Monic := hm.map _
  have hQd : Q.natDegree = p + 1 := (hm.natDegree_map _).trans hd
  have hζp := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hroot (b : ℕ) : Q.eval (TS K 1 (ζ ^ b)) = 0 := by
    have hpow : (ζ ^ b) ^ p = 1 := by
      rw [← pow_mul, Nat.mul_comm b p, pow_mul, hζp, one_pow]
    have h := congrArg (qTwist (ζ ^ b)) hr
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map,
      relationAtSeed_map, qTwist_qExpand_of_pow_eq_one p (ζ ^ b) hpow] at h
    simpa only [TS, qExpand_one_apply] using h
  have hle : (TS K (p * p) 1 ::ₘ
      (Multiset.range p).map (fun b => TS K 1 (ζ ^ b))) ≤ Q.roots := by
    rw [Multiset.le_iff_subset (roots_phiProd_conj_nodup p ζ hζ)]
    intro x hx
    rw [Polynomial.mem_roots hQm.ne_zero]
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · simpa only [Polynomial.IsRoot, TS, qTwist_one_apply] using hf
    · obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
      exact hroot b
  apply (Multiset.eq_of_le_of_card_le hle _).symm
  simpa only [Multiset.card_cons, Multiset.card_map, Multiset.card_range, hQd]
    using Polynomial.card_roots' Q

theorem residue_prime_polynomial_splits
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (P : Polynomial (Polynomial ℤ)) (hm : P.Monic) (hd : P.natDegree = p + 1)
    (hf : (relationAtSeed P (qExpand K p (jqModC K))).eval
      (qExpand K (p * p) (jqModC K)) = 0)
    (hr : (relationAtSeed P (qExpand K p (jqModC K))).eval (jqModC K) = 0) :
    (relationAtSeed P (qExpand K p (jqModC K))).Splits := by
  rw [Polynomial.splits_iff_card_roots, residue_prime_polynomial_roots K p ζ hζ P hm hd hf hr,
    Multiset.card_cons, Multiset.card_map, Multiset.card_range]
  exact ((hm.natDegree_map _).trans hd).symm

end
end Dubon2026.SourceFunctionField

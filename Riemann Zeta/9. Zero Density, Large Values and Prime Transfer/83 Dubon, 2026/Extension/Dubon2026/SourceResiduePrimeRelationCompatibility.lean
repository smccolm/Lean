import Dubon2026.SourceResidueTwistedPrimeRelations

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> lower conjugate induction. Retain a single actual integral
prime polynomial with both adjacent identities and the full twisted root
list. Injective q-expansion recovers the forward identity from its distinguished
root; the zero twist supplies the reverse identity. The full/reduced minimal
polynomial steps therefore consume the same proved polynomial. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux

theorem exists_residue_prime_compatible_relations
    (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      (∀ (d : ℕ) [NeZero d],
        (relationAtSeed P (qExpand K d (jqModC K))).eval (qExpand K (d * p) (jqModC K)) = 0 ∧
        (relationAtSeed P (qExpand K (d * p) (jqModC K))).eval (qExpand K d (jqModC K)) = 0) ∧
      ∀ (e : ℕ) [NeZero e] (u : Kˣ),
        (relationAtSeed P (TS K (e * p) (u ^ p))).roots =
          TS K (e * (p * p)) (u ^ (p * p)) ::ₘ
            (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) ∧
        (relationAtSeed P (TS K (e * p) (u ^ p))).Splits ∧
        (relationAtSeed P (TS K (e * p) (u ^ p))).roots.Nodup := by
  obtain ⟨P, hm, hd, htw⟩ := exists_residue_prime_twisted_relations K p ζ hζ
  refine ⟨P, hm, hd, ?_, htw⟩
  intro d _
  have hs : qExpand K p (qExpand K d (jqModC K)) = TS K (d * p) 1 := by
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (Nat.mul_comm p d) _
  have hx : qExpand K p (qExpand K (d * p) (jqModC K)) = TS K (d * (p * p)) 1 := by
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by ring) _
  constructor
  · apply (qExpand K p).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map, hs, hx]
    have h := (residue_prime_root_iff_of_root_list p d ζ 1 P hm (htw d 1).1
      (TS K (d * (p * p)) 1)).mpr (Or.inl (by rw [one_pow]))
    simpa only [one_pow] using h
  · have h := (residue_prime_root_iff_of_root_list p d ζ 1 P hm (htw d 1).1
      (TS K d 1)).mpr (Or.inr ⟨0, hp.out.pos, by rw [pow_zero, one_mul]⟩)
    simpa only [one_pow, TS, qTwist_one_apply] using h

end
end Dubon2026.SourceFunctionField

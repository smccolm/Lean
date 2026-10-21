import Dubon2026.SourcePrimeBidirectionalRelation
import Dubon2026.SourceAllDivisorMonicRelations

/-! DUB-17/18 -> numerical modular genus -> composite-level j-map degree
-> prime-power extension steps. Both adjacent roots follow from the same
proved prime conjugate product. The reverse root is derived without a
polynomial-symmetry assumption. This supplies the known linear factor that
must be removed before proving the degree-p prime-power step.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem relationAtSeed_reverse_substitution_eval {n : ℕ} [NeZero n]
    (P : Polynomial (Polynomial ℤ))
    (hP : P.eval₂ ((qExpand ℚ n).comp evalAtJ) jq = 0)
    (a : ℕ) [NeZero a] :
    (relationAtSeed P (qExpand ℚ (a * n) jq)).eval (qExpand ℚ a jq) = 0 := by
  have hbase : (relationAtSeed P (qExpand ℚ n jq)).eval jq = 0 := by
    rw [relationAtSeed, Polynomial.eval_map]
    convert hP using 2
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtJ_X]
  have h := congrArg (qExpand ℚ a) hbase
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map,
    relationAtSeed_map, qExpand_qExpand] at h
  exact h

theorem qExpand_jq_injective {a b : ℕ} [NeZero a] [NeZero b]
    (h : qExpand ℚ a jq = qExpand ℚ b jq) : a = b := by
  have h' : PrimeDegreeAux.TS ℚ a 1 = PrimeDegreeAux.TS ℚ b 1 := by
    simpa only [PrimeDegreeAux.TS, qTwist_one_apply, jqModC_rat] using h
  exact (PrimeDegreeAux.TS_injective h').1

theorem exists_prime_adjacent_relations (p : ℕ) [Fact p.Prime] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = p + 1 ∧
      ∀ (a : ℕ) [NeZero a],
        (relationAtSeed P (qExpand ℚ a jq)).eval (qExpand ℚ (a * p) jq) = 0 ∧
        (relationAtSeed P (qExpand ℚ (a * p) jq)).eval (qExpand ℚ a jq) = 0 := by
  obtain ⟨P, hPm, hdeg, hf, hr⟩ := exists_prime_bidirectional_relation p
  exact ⟨P, hPm, hdeg, fun a _ =>
    ⟨relationAtSeed_substitution_eval P hf a,
      relationAtSeed_reverse_substitution_eval P hr a⟩⟩

end
end Dubon2026.SourceFunctionField

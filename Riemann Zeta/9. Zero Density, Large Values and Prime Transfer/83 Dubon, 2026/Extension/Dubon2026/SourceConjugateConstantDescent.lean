import Dubon2026.SourceOriginalGenerationInduction

/-! DUB-17/18 -> numerical modular genus -> composite degree -> prime
nonmembership over a coprime base level. If a reduced polynomial has the
same value at more distinct conjugates than its degree, native polynomial
root counting forces that value into the base coefficient field. This is
the final descent step of the coprime nonmembership contradiction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem polynomial_value_mem_range_of_eval_eq_const
    {F L : Type*} [Field F] [Field L] (ι : F →+* L)
    (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card)
    (hval : ∀ y ∈ s, g.eval₂ ι y = x) : x ∈ ι.range := by
  classical
  let Q := g.map ι - C x
  have hQdeg : Q.natDegree ≤ g.natDegree := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q s _ (hQdeg.trans_lt hcard)
    intro y hy
    change (g.map ι - C x).eval y = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map, hval y hy, sub_self]
  have hconst : g.map ι = C x := sub_eq_zero.mp hQ0
  refine ⟨g.coeff 0, ?_⟩
  have h := congrArg (fun P : Polynomial L => P.coeff 0) hconst
  simpa only [Polynomial.coeff_map, Polynomial.coeff_C_zero] using h

end
end Dubon2026.SourceFunctionField

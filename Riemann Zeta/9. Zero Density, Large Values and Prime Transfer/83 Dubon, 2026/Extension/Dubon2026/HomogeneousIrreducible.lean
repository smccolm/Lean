import Dubon2026.FiniteWeightLadder
import Dubon2026.HomogeneousRaisingBasis

/-! # Irreducibility of the original finite homogeneous Lie representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every nonzero subspace invariant under the original three compact infinitesimals is the entire homogeneous polynomial space. -/
theorem homogeneousSl2_submodule_eq_top (n : ℕ)
    (p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ n)) (hn : p ≠ ⊥)
    (hpH : ∀ w ∈ p, homogeneousSl2Action n compactSl2H w ∈ p)
    (hpE : ∀ w ∈ p, homogeneousSl2Action n compactSl2E w ∈ p)
    (hpF : ∀ w ∈ p, homogeneousSl2Action n compactSl2F w ∈ p) : p = ⊤ := by
  apply finiteWeightLadder_submodule_eq_top n
    (homogeneousSl2Action n compactSl2H) (homogeneousSl2Action n compactSl2E)
    (homogeneousSl2Action n compactSl2F) (homogeneousRaisingJet n)
    (fun r => -(n : ℂ) + 2 * r) (fun r => ((r : ℂ) + 1) * ((n : ℂ) - r))
    ?_ ?_ (homogeneousRaisingJet_weight n) ?_ (homogeneousRaisingJet_lower n) ?_ p hn hpH hpE hpF
  · have hb : (fun r : Fin (n + 1) => homogeneousRaisingJet n r.val) = homogeneousRaisingBasis n :=
      funext (fun r => (homogeneousRaisingBasis_apply n r).symm)
    rw [hb]
    exact (homogeneousRaisingBasis n).span_eq
  · intro r s he
    have h : (r : ℂ) = s := by linear_combination he / 2
    exact_mod_cast h
  · intro r
    change (homogeneousSl2Action n compactSl2E)
      (((homogeneousSl2Action n compactSl2E) ^ r) (homogeneousCompactGenerator n)) =
      ((homogeneousSl2Action n compactSl2E) ^ (r + 1)) (homogeneousCompactGenerator n)
    rw [pow_succ', Module.End.mul_apply]
  · intro r hr
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero r)
      (sub_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hr))

end
end Dubon2026

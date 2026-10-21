import Dubon2026.SourceLevelProjectiveCosets
import Dubon2026.SourceLevelProjectivePrimePower
import Dubon2026.SourceLevelProjectiveCRT
import Dubon2026.SourceLevelPsi
import Mathlib.Data.Nat.Factorization.Induction

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> matching period dimension bounds -> original level index and genus numerics.
Selected from anthropics/fermats-last-theorem (Apache-2.0), commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the solutions
S_ModularCurve_card_projectiveLine_zmod, S_ModularCurve_dedekindPsi_prime_pow
and S_ModularCurve_dedekindPsi_mul_of_coprime. Only the necessary finite-ring
and arithmetic-function proofs are retained; the unrelated modular-polynomial
and function-field developments in the source files are omitted.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section
open Finset Nat Finset.Nat

theorem card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) :
    Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      rw [card_projectiveLine_prime_pow p n hp hn.ne', dedekindPsi_prime_pow p n hp hn.ne']
  | zero => exact absurd rfl hN
  | one =>
      rw [dedekindPsi_one]
      have hrep : ∀ q : ProjectiveLine (ZMod 1),
          q = ⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isCoprime_one_left⟩⟧ := by
        intro q
        obtain ⟨v, rfl⟩ := Quotient.exists_rep q
        exact Quotient.sound ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hrep a).trans (hrep b).symm⟩,
        ⟨⟦⟨((1 : ZMod 1), (0 : ZMod 1)), isCoprime_one_left⟩⟧⟩⟩
  | coprime a b ha hb hab iha ihb =>
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      rw [card_projectiveLine_mul a b hab, iha (by omega), ihb (by omega),
        dedekindPsi_mul_of_coprime a b hab]

/-- The original Gamma0 index has exactly its arithmetic squarefree-divisor value. -/
theorem gamma0_index (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N := by
  rw [gamma0_index_projective, card_projectiveLine_zmod N (NeZero.ne N)]

end
end Dubon2026.SourceLevelProjective

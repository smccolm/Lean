import Dubon2026.SourceAffineFunctionRepresentation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Actual diagonal units identify the exceptional invariant character.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the Eisenstein exception when a flag eigenclass vanishes ->
the exact divisibility of its original lower-diagonal exponent.
The CRT and Bezout construction is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). Native CRT and cyclic prime-field
units are reused; the witnesses are actual determinant-one integral matrices.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups
variable (p Q : ℕ) [Fact p.Prime] [NeZero Q]

/-- Every prime-field unit occurs as the lower diagonal of an actual Gamma0 matrix. -/
theorem sourceAffine_exists_diagonal_unit (u₀ : (ZMod p)ˣ) : ∃ γ : Gamma0 Q, sourceAffineD p Q γ = u₀ := by
  have hp : p.Prime := Fact.out
  set M₀ := ordCompl[p] Q with hM₀
  have hco : p.Coprime M₀ := Nat.coprime_ordCompl hp (NeZero.ne Q)
  set d₀ : ℕ := (u₀ : ZMod p).val with hd₀
  obtain ⟨d, hdp, hdM₀⟩ := Nat.chineseRemainder hco d₀ 1

  have hd_cast : (d : ZMod p) = (u₀ : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdp, hd₀, ZMod.natCast_zmod_val]
  have hdp' : Nat.Coprime d p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr h
    rw [hd_cast] at this
    exact u₀.ne_zero this
  have hdM₀' : Nat.Coprime d M₀ := by
    rw [Nat.Coprime, hdM₀.gcd_eq, Nat.gcd_one_left]
  have hdM : Nat.Coprime d Q := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self Q p]
    exact (hdp'.pow_right _).mul_right hdM₀'

  have hbez : ((d : ℤ)) * Int.gcdA d Q + (Q : ℤ) * Int.gcdB d Q = 1 := by
    have h := Int.gcd_eq_gcd_ab (d : ℤ) (Q : ℤ)
    rw [Int.gcd_natCast_natCast, hdM, Nat.cast_one] at h
    exact h.symm
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![Int.gcdA d Q, -Int.gcdB d Q; (Q : ℤ), (d : ℤ)] with hA
  have hdet : A.det = 1 := by
    rw [hA, Matrix.det_fin_two_of]
    linear_combination hbez
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [Gamma0_mem]
    show (((Q : ℤ)) : ZMod Q) = 0
    simp
  · show (((d : ℤ)) : ZMod p) = _
    rw [Int.cast_natCast, hd_cast]



/-- A power trivial on all actual Gamma0 lower diagonals is divisible by p minus one. -/
theorem sourceAffine_diagonal_exponent_dvd (n : ℕ) (h : ∀ γ : Gamma0 Q, (sourceAffineD p Q γ) ^ n = 1) : (p - 1) ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨γ, hγ⟩ := sourceAffine_exists_diagonal_unit p Q g
  have hgn : g ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hγ, h γ, Units.val_one]
  rw [← horder]
  exact orderOf_dvd_of_pow_eq_one hgn

end
end Dubon2026

import Dubon2026.SourceWeightTwoDegeneracyAdjoint

/-! DUB-17/18 -> close the actual parabolic branch -> a primitive
lower-level eigensystem. Failure of genuine newness provides an actual
old generator with nonzero Petersson pairing. Its proved adjoint gives
a nonzero lower-level form preserving every prescribed original good
prime. The level strictly decreases and continues to divide the original. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

theorem sourceWeightTwoEigen_not_new_descends
    {Q N : ℕ} [NeZero Q] [NeZero N] (hNQ : N ∣ Q)
    (θ : sourceBinaryHeckePrime Q → ℂ)
    (f : CuspForm (Gamma0 N) 2)
    (he : ∀ ell, cuspHeckeLinear N 2 ell.val f = θ ell • f)
    (hn : f ∉ cuspNewspace N 2) :
    ∃ M : ℕ, ∃ hM : NeZero M,
      letI := hM
      M < N ∧ M ∣ N ∧
        ∃ g : CuspForm (Gamma0 M) 2, g ≠ 0 ∧
          ∀ ell, cuspHeckeLinear M 2 ell.val g = θ ell • g := by
  classical
  have hnot : ¬∀ v, IsCuspOldGenerator v → cuspPetersson f v = 0 :=
    fun h => hn ((mem_cuspNewspace_iff_generators f).mpr h)
  push Not at hnot
  obtain ⟨v, hv, hfv⟩ := hnot
  obtain ⟨M, hMN, d, hd, u, rfl⟩ := hv
  letI : NeZero (M : ℕ) := ⟨M.pos.ne'⟩
  letI : NeZero (d : ℕ) := ⟨d.pos.ne'⟩
  obtain ⟨g, hg⟩ := sourceWeightTwoDegeneracy_exists_adjoint d hd f
  have hgne : g ≠ 0 := by
    intro hz
    have hh := hg u
    rw [hz, cuspPetersson_zero_left] at hh
    exact hfv hh.symm
  refine ⟨M, inferInstance, hMN, (dvd_mul_left (M : ℕ) (d : ℕ)).trans hd, g, hgne, ?_⟩
  intro ell
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  exact sourceWeightTwoDegeneracy_adjoint_eigen d hd ell.property.1
    (ell.property.2.of_dvd_right hNQ) (θ ell) f g hg (he ell)

theorem sourceWeightTwoEigen_exists_new_divisor
    (Q : ℕ) [NeZero Q] (θ : sourceBinaryHeckePrime Q → ℂ)
    (f : CuspForm (Gamma0 Q) 2) (hf : f ≠ 0)
    (he : ∀ ell, cuspHeckeLinear Q 2 ell.val f = θ ell • f) :
    ∃ M : ℕ, ∃ hM : NeZero M,
      letI := hM
      M ∣ Q ∧ ∃ g : CuspForm (Gamma0 M) 2,
        g ≠ 0 ∧ g ∈ cuspNewspace M 2 ∧
          ∀ ell, cuspHeckeLinear M 2 ell.val g = θ ell • g := by
  classical
  let P (M : ℕ) : Prop := ∃ hM : NeZero M,
    letI := hM
    M ∣ Q ∧ ∃ g : CuspForm (Gamma0 M) 2, g ≠ 0 ∧
      ∀ ell, cuspHeckeLinear M 2 ell.val g = θ ell • g
  have hex : ∃ M, P M := ⟨Q, inferInstance, dvd_rfl, f, hf, he⟩
  let M := Nat.find hex
  obtain ⟨hM, hMQ, g, hg, hge⟩ := Nat.find_spec hex
  letI := hM
  refine ⟨M, hM, hMQ, g, hg, ?_, hge⟩
  by_contra hn
  obtain ⟨L, hL, hLM, hLd, v, hv, hve⟩ :=
    sourceWeightTwoEigen_not_new_descends hMQ θ g hge hn
  have hP : P L := ⟨hL, hLd.trans hMQ, v, hv, hve⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hP)) hLM

end
end Dubon2026

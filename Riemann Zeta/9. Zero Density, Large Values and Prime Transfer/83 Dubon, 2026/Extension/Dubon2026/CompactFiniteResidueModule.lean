import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-! # Compact coefficient spans and actual finite residue representatives -/

namespace Dubon2026
noncomputable section

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space S] [ContinuousSMul R S]
  [IsNoetherianRing S]

/-- Finitely many actual residue representatives generate the original
module over a compact coefficient ring when the displayed original scalar
lies in a separating ideal. Compactness closes the span of the representatives;
nested actual congruence sets supply the exact original element. -/
theorem compactFiniteResidue_module_finite (I : Ideal S) [IsHausdorff I S]
    (π : R) (hπ : algebraMap R S π ∈ I)
    [Finite (S ⧸ Ideal.span {algebraMap R S π})] : Module.Finite R S := by
  classical
  let J : Ideal S := Ideal.span {algebraMap R S π}
  let rep : S ⧸ J → S := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hrep (q : S ⧸ J) : Ideal.Quotient.mk J (rep q) = q :=
    (Ideal.Quotient.mk_surjective q).choose_spec
  let C : Submodule R S := Submodule.span R (Set.range rep)
  have hC : C.FG := Submodule.fg_span (Set.finite_range rep)
  have hCc : IsCompact (C : Set S) := Submodule.isCompact_of_fg hC
  have first (x : S) : ∃ c ∈ C, ∃ y : S, x = c + π • y := by
    let c := rep (Ideal.Quotient.mk J x)
    have hc : c ∈ C := Submodule.subset_span ⟨_, rfl⟩
    have hdiff : x - c ∈ J := Ideal.Quotient.eq.mp (hrep _).symm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hdiff
    refine ⟨c, hc, y, ?_⟩
    rw [Algebra.smul_def]
    exact (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)
  have approx (n : ℕ) (x : S) : ∃ c ∈ C, ∃ y : S, x = c + π ^ n • y := by
    induction n generalizing x with
    | zero => exact ⟨0, C.zero_mem, x, by simp⟩
    | succ n ih =>
        obtain ⟨c, hc, y, hy⟩ := first x
        obtain ⟨d, hd, z, hz⟩ := ih y
        refine ⟨c + π • d, C.add_mem hc (C.smul_mem π hd), z, ?_⟩
        rw [hy, hz, smul_add, pow_succ', mul_smul]
        abel
  have htop : C = ⊤ := by
    apply top_unique
    intro x _
    let F : ℕ → Set S := fun n => {c | c ∈ C ∧ x - c ∈ I ^ n}
    have hclosed (n : ℕ) : IsClosed (F n) :=
      hCc.isClosed.inter ((IsNoetherianRing.isClosed_ideal (I ^ n)).preimage
        (continuous_const.sub continuous_id))
    have hnonempty (n : ℕ) : (F n).Nonempty := by
      obtain ⟨c, hc, y, hy⟩ := approx n x
      refine ⟨c, hc, ?_⟩
      have hp : algebraMap R S π ^ n ∈ I ^ n := Ideal.pow_mem_pow hπ n
      have hm := (I ^ n).mul_mem_right y hp
      simpa [hy, Algebra.smul_def, map_pow] using hm
    obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
      (fun n c hc => ⟨hc.1, Ideal.pow_le_pow_right n.le_succ hc.2⟩) hnonempty
      (hCc.of_isClosed_subset (hclosed 0) (fun _ h => h.1)) hclosed
    have hxc : x - c = 0 := by
      apply IsHausdorff.haus' (I := I) (x - c)
      intro n
      simpa [SModEq.sub_mem, Ideal.smul_eq_mul] using (Set.mem_iInter.mp hc n).2
    rw [sub_eq_zero.mp hxc]
    exact (Set.mem_iInter.mp hc 0).1
  exact Module.Finite.of_fg_top (htop ▸ hC)

end
end Dubon2026

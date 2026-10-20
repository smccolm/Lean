import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Fintype.Order

/-! # Finite subgroups of the original separated congruence system

For DUB-17's arithmetic small-level condition, the existing matrix
congruence results make every finite-depth reduction a residue-primary
group. A finite subgroup embeds in one sufficiently deep reduction;
this proves its primary order without postulating a pro-primary theorem.
-/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [Finite G]
variable {H : ℕ → Type*} [∀ n, Group (H n)]

/-- One actual reduction is faithful on a finite group separated by decreasing kernels. -/
theorem finiteSeparatedReduction_exists_injective (π : ∀ n, G →* H n)
    (hsep : ∀ x, (∀ n, π n x = 1) → x = 1)
    (hmono : Antitone fun n => (π n).ker) :
    ∃ n, Function.Injective (π n) := by
  classical
  letI := Fintype.ofFinite G
  have hdetect : ∀ x : G, ∃ n, π n x = 1 → x = 1 := by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, fun _ => hx⟩
    · obtain ⟨n, hn⟩ : ∃ n, π n x ≠ 1 := by
        by_contra! h
        exact hx (hsep x h)
      exact ⟨n, fun h => (hn h).elim⟩
  choose N hN using hdetect
  let b := Finset.univ.sup N
  refine ⟨b, (π b).ker_eq_bot_iff.mp ?_⟩
  apply le_antisymm _ bot_le
  intro x hx
  exact hN x (hmono (Finset.le_sup (f := N) (Finset.mem_univ x)) hx)

/-- A finite original subgroup with primary reduction images is itself primary. -/
theorem finiteSeparatedReduction_isPGroup (π : ∀ n, G →* H n)
    (hsep : ∀ x, (∀ n, π n x = 1) → x = 1)
    (hmono : Antitone fun n => (π n).ker) (p : ℕ)
    (hP : ∀ n, IsPGroup p (π n).range) : IsPGroup p G := by
  obtain ⟨n, hn⟩ := finiteSeparatedReduction_exists_injective π hsep hmono
  exact (hP n).of_injective (π n).rangeRestrict
    (fun x y h => hn (congrArg Subtype.val h))

end
end Dubon2026

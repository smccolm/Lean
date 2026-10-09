import Dubon2026.ProPClosedSubgroupCharacters

/-! # Finite original continuous prime-order characters give genuine topological generators -/

namespace Dubon2026

noncomputable section

/-- Finiteness of the actual original continuous prime-order characters gives finitely many genuine topological generators of the original pro-p group. -/
theorem proP_finitely_generated_of_finite_characters (p : ℕ) (hp : p.Prime)
    (G : ProfiniteGrp)
    (hP : ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup))
    [Finite (G →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let A := {f : G →ₜ* Multiplicative (ZMod p) // f ≠ 1}
  letI : Fintype A := Fintype.ofFinite A
  have hw : ∀ a : A, ∃ g : G, a.val g ≠ 1 := by
    intro a
    by_contra! hall
    apply a.property
    ext g
    exact hall g
  choose x hx using hw
  let S : Finset G := Finset.univ.image x
  refine ⟨S, ?_⟩
  by_contra hproper
  let K := (Subgroup.closure (S : Set G)).topologicalClosure
  obtain ⟨χ, hχ, hker⟩ := proP_closed_subgroup_character p hp G hP K
    (Subgroup.isClosed_topologicalClosure _) hproper
  have hne : χ ≠ 1 := by
    intro heq
    obtain ⟨y, hy⟩ := exists_ne (1 : Multiplicative (ZMod p))
    obtain ⟨g, hg⟩ := hχ y
    apply hy
    calc
      y = χ g := hg.symm
      _ = 1 := by rw [heq]; rfl
  let a : A := ⟨χ, hne⟩
  have hxK : x a ∈ K := by
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_closure
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  exact hx a (hker hxK)

end
end Dubon2026

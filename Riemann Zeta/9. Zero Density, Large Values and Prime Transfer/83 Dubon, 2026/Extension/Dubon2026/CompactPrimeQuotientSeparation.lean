import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.PGroup

/-! # Finite prime-power detection from actual compact quotient coordinates -/

namespace Dubon2026

noncomputable section
open Set

variable {G α : Type*} [Group G] [TopologicalSpace G]
  [CompactSpace G] {H : α → Type*} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, DiscreteTopology (H i)]

/-- A genuine open kernel containing the common original coordinate kernel already contains a finite coordinate intersection. -/
theorem compact_reduction_finite_kernel_detection
    (π : ∀ i, G →* H i) (hπ : ∀ i, Continuous (π i))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f)
    (hcommon : (⨅ i, (π i).ker) ≤ f.ker) :
    ∃ S : Finset α, ∀ g : G, (∀ i ∈ S, π i g = 1) → f g = 1 := by
  classical
  have hopen : IsOpen (f.ker : Set G) :=
    (isOpen_discrete ({1} : Set Q)).preimage hf
  have hcover : (f.ker : Set G)ᶜ ⊆ ⋃ i, ((π i).ker : Set G)ᶜ := by
    intro g hg
    by_contra hnot
    have hall : ∀ i, g ∈ (π i).ker := by
      simpa only [mem_iUnion, mem_compl_iff, not_exists, not_not] using hnot
    exact hg (hcommon (Subgroup.mem_iInf.mpr hall))
  obtain ⟨S, hS⟩ := hopen.isClosed_compl.isCompact.elim_finite_subcover
    (fun i => ((π i).ker : Set G)ᶜ)
    (fun i => ((isClosed_discrete ({1} : Set (H i))).preimage (hπ i)).isOpen_compl)
    hcover
  refine ⟨S, ?_⟩
  intro g hg
  by_contra hfg
  obtain ⟨i, hi, hgi⟩ := mem_iUnion₂.mp (hS hfg)
  exact hgi (hg i hi)

/-- Every original continuous discrete quotient detected by actual p-group coordinates is itself a p-group. -/
theorem compact_reduction_continuous_quotient_isPGroup
    (π : ∀ i, G →* H i) (hπ : ∀ i, Continuous (π i))
    (p : ℕ) (hP : ∀ i, IsPGroup p (H i))
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →* Q) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hcommon : (⨅ i, (π i).ker) ≤ f.ker) : IsPGroup p Q := by
  classical
  obtain ⟨S, hS⟩ := compact_reduction_finite_kernel_detection π hπ f hf hcommon
  intro q
  obtain ⟨g, rfl⟩ := hsurj q
  choose k hk using fun i => hP i (π i g)
  refine ⟨S.sup k, ?_⟩
  have hfg : f (g ^ (p ^ S.sup k)) = 1 := by
    apply hS
    intro i hi
    rw [map_pow]
    obtain ⟨t, ht⟩ := pow_dvd_pow p (Finset.le_sup hi : k i ≤ S.sup k)
    rw [ht, pow_mul, hk i, one_pow]
  simpa only [map_pow] using hfg

end
end Dubon2026

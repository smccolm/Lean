import Dubon2026.SourceMeromorphicFinitePoles

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Compactness and connectedness give an actual
finite effective pole divisor for every meromorphic function. Zero germs
are included, so the later denominator argument needs no nonvanishing premise.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M] [ConnectedSpace M]

theorem exists_effective_pole_bound (g : M → ℂ)
    (hg : ∀ v, MeromorphicAt (rd g v) (ctr v)) :
    ∃ E : M →₀ ℤ, (∀ v, 0 ≤ E v) ∧
      ∀ v, ((-E v : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (rd g v) (ctr v) := by
  classical
  rcases forall_order_eq_top_or g hg with htop | hfin
  · refine ⟨0, fun _ => le_rfl, fun v => ?_⟩
    rw [htop v]
    exact le_top
  have hordZ : ∀ v, ∃ m : ℤ, meromorphicOrderAt (rd g v) (ctr v) = m := fun v => by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hfin v)
    exact ⟨m, hm.symm⟩
  choose og hog using hordZ
  have hEfin : (Function.support fun v => max 0 (-og v)).Finite := by
    refine (finite_setOf_order_neg g hg hfin).subset fun v hv => ?_
    have h1 : max 0 (-og v) ≠ 0 := hv
    show meromorphicOrderAt (rd g v) (ctr v) < 0
    rw [hog v]
    have : og v < 0 := by omega
    exact_mod_cast this
  refine ⟨Finsupp.ofSupportFinite _ hEfin, fun v => le_max_left _ _, fun v => ?_⟩
  change ((-max 0 (-og v) : ℤ) : WithTop ℤ) ≤ _
  rw [hog v, WithTop.coe_le_coe]
  omega

end
end Dubon2026.SourceFunctionField.MeromorphicCompact

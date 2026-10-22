import Mathlib.Topology.Homotopy.Lifting

/-! DUB-17/18 -> original Abel-Jacobi -> actual analytic dissection.
Native covering lifts and open sections trivialize a covering over a simply
connected, locally path connected base. This supplies all ordinary square
sheets at once and avoids the external slit-plane power-map construction.
-/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [SimplyConnectedSpace X] [LocPathConnectedSpace X] {f : E → X}

theorem exists_simply_connected_trivialization (hf : IsCoveringMap f) (b : X) :
    ∃ H : E ≃ₜ X × (f ⁻¹' {b}), ∀ e, (H e).1 = f e := by
  classical
  let I := f ⁻¹' {b}
  haveI : DiscreteTopology I := (hf b).discreteTopology_fiber
  have hex : ∀ i : I, ∃ σ : C(X, E), σ b = i.1 ∧ f ∘ σ = id := by
    intro i
    exact (hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) b i.1 i.2).exists
  choose σ hσ using hex
  have hσval (i : I) (x : X) : f (σ i x) = x := congr_fun (hσ i).2 x
  have hopen (i : I) : IsOpenMap (σ i) := by
    apply (hf.isLocalHomeomorph.isOpenEmbedding_of_comp ?_ (σ i).continuous).isOpenMap
    rw [(hσ i).2]
    exact IsOpenEmbedding.id
  let F : X × I → E := fun q => σ q.2 q.1
  have hcont : Continuous F := continuous_prod_of_discrete_right.mpr fun i => (σ i).continuous
  have hFopen : IsOpenMap F := isOpenMap_prod_of_discrete_right.mpr hopen
  have hinj : Function.Injective F := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have hxy : x = y := (hσval i x).symm.trans ((congr_arg f h).trans (hσval j y))
    subst y
    have he : (σ i : X → E) = σ j := hf.eq_of_comp_eq (σ i).continuous (σ j).continuous
      ((hσ i).2.trans (hσ j).2.symm) x h
    have hij : i = j := Subtype.ext <| (hσ i).1.symm.trans ((congr_fun he b).trans (hσ j).1)
    subst j
    rfl
  have hsurj : Function.Surjective F := by
    intro e
    obtain ⟨τ, hτ, _⟩ := hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e) e rfl
    let i : I := ⟨τ b, congr_fun hτ.2 b⟩
    have he : (σ i : X → E) = τ := hf.eq_of_comp_eq (σ i).continuous τ.continuous
      ((hσ i).2.trans hτ.2.symm) b (hσ i).1
    exact ⟨(f e, i), (congr_fun he (f e)).trans hτ.1⟩
  let K : X × I ≃ₜ E := (Equiv.ofBijective F ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    hcont hFopen
  refine ⟨K.symm, fun e => ?_⟩
  have h := hσval (K.symm e).2 (K.symm e).1
  change f (K (K.symm e)) = (K.symm e).1 at h
  rw [K.apply_symm_apply] at h
  exact h.symm

end
end Dubon2026.SourceFunctionField.SheetCover

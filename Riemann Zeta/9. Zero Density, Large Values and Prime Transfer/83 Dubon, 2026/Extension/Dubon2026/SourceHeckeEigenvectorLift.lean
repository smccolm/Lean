import Dubon2026.SourceCommutingPrescribedEigenvector

/-! Prescribed eigenvalues through the coefficient-filtration exact sequence.
DUB-17/18 -> residual modular Galois association -> residual weight/level
reduction -> descent through the original binary polynomial coefficient flag.
When the image eigenclass vanishes in the next quotient, exactness puts it
in the preceding cohomology image; this lemma recovers a genuine nonzero
eigenvector there. No injectivity of the induced H1 map is assumed.

The invariant-preimage argument adapts ASF.step in
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd.lean
(Apache-2.0; retained LICENSE and NOTICE). It reuses the already proved
prescribed-eigenvector result and does not duplicate the external H1 quotient.
-/

namespace Dubon2026
noncomputable section

/-- A nonzero common eigenvector in the image of an equivariant linear map has
its prescribed eigenvalues realized by a nonzero source eigenvector, provided
the source is finite dimensional and its operators commute. -/
theorem sourceHeckeEigenvector_exists_in_source
    {F V W ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup W] [Module F W]
    (T : ι → Module.End F V) (U : ι → Module.End F W)
    (hT : ∀ i j, Commute (T i) (T j)) (f : V →ₗ[F] W)
    (hf : ∀ i, f.comp (T i) = (U i).comp f) (eigenvalues : ι → F)
    (x : W) (hx : x ≠ 0) (heig : ∀ i, U i x = eigenvalues i • x)
    (hrange : x ∈ LinearMap.range f) :
    ∃ y : V, y ≠ 0 ∧ ∀ i, T i y = eigenvalues i • y := by
  obtain ⟨y₀, hy₀⟩ := hrange
  have hmap (i : ι) (v : V) : f (T i v) = U i (f v) := LinearMap.congr_fun (hf i) v
  let M := (Submodule.span F {x}).comap f
  have hfx : ∀ m ∈ M, ∃ r : F, r • x = f m := fun m hm =>
    Submodule.mem_span_singleton.mp hm
  have hstab : ∀ i, ∀ m ∈ M, T i m ∈ M := by
    intro i m hm
    obtain ⟨r, hr⟩ := hfx m hm
    change f (T i m) ∈ Submodule.span F {x}
    rw [hmap, ← hr, map_smul, heig, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  let TM : ι → Module.End F M := fun i => (T i).restrict (hstab i)
  have hTM : ∀ i j, Commute (TM i) (TM j) := fun i j =>
    LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hT i j).eq m)
  let P := (LinearMap.ker f).comap M.subtype
  have hy₀M : y₀ ∈ M := by
    change f y₀ ∈ Submodule.span F {x}
    rw [hy₀]
    exact Submodule.mem_span_singleton_self x
  have hP : P ≠ ⊤ := by
    intro h
    have hv : (⟨y₀, hy₀M⟩ : M) ∈ P := by rw [h]; trivial
    change f y₀ = 0 at hv
    exact hx (hy₀.symm.trans hv)
  have hTP : ∀ i (m : M), TM i m - eigenvalues i • m ∈ P := by
    intro i m
    obtain ⟨r, hr⟩ := hfx m m.property
    change f (T i m - eigenvalues i • (m : V)) = 0
    rw [map_sub, map_smul, hmap, ← hr,
      map_smul, heig, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨y, hy, he⟩ :=
    sourceCommutingOperators_exists_prescribedEigenvector TM hTM eigenvalues P hP hTP
  exact ⟨y.val, fun h => hy (Subtype.ext h), fun i => congrArg Subtype.val (he i)⟩

end
end Dubon2026

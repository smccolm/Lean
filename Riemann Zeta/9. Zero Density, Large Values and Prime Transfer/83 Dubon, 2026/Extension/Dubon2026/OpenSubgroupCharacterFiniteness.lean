import Dubon2026.FixedResidualProPKernel
import Mathlib.Topology.Homeomorph.Lemmas

/-! Arithmetic character finiteness passes to every open subgroup with its
original topology. This is needed to derive finite residual presentations
over the finite base fields on DUB-17's CM deformation route. -/

namespace Dubon2026
noncomputable section

/-- Finiteness of the original continuous characters on every open ambient
subgroup also holds for each open subgroup of an original open subgroup. -/
theorem openSubgroup_continuousCharacters_finite
    (G : ProfiniteGrp) {T : Type*} [Group T] [TopologicalSpace T]
    (hchars : ∀ L : OpenSubgroup G, Finite (L →ₜ* T))
    (H : OpenSubgroup G) (K : OpenSubgroup H) : Finite (K →ₜ* T) := by
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  letI : CompactSpace K := isCompact_iff_compactSpace.mp K.isClosed.isCompact
  let L : OpenSubgroup G :=
    ⟨K.toSubgroup.map H.toSubgroup.subtype,
      H.isOpen.isOpenMap_subtype_val _ K.isOpen⟩
  let e : K ≃* L := K.toSubgroup.equivMapOfInjective H.toSubgroup.subtype Subtype.val_injective
  have he : Continuous e := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Continuous e.symm :=
    (show Continuous e.toEquiv from he).continuous_symm_of_equiv_compact_to_t2
  letI : Finite (L →ₜ* T) := hchars L
  let j : (K →ₜ* T) → (L →ₜ* T) := fun f => f.comp ⟨e.symm.toMonoidHom, hi⟩
  apply Finite.of_injective j
  intro f g h
  apply DFunLike.ext
  intro x
  have hx := congrArg (fun z : L →ₜ* T => z (e x)) h
  change f (e.symm (e x)) = g (e.symm (e x)) at hx
  simpa only [e.symm_apply_apply] using hx

end
end Dubon2026

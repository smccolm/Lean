/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted in part from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero.lean.
Changes: use the existing literal Dubon subgroup trace, assume only the
single subgroup's generator/cardinality, and derive its actual injectivity.
-/
import Dubon2026.OriginalCohomologyTraceNaturality
import Dubon2026.OriginalFiniteNormalizedQuotientSystem

/-! # Injectivity of the actual class H2 trace

The finite relation-extension argument must detect a subgroup obstruction
after its Shapiro transfer to the full finite group. Full order of the
original class, its actual restricted generator and the subgroup's exact
H2 cardinality imply injectivity of the existing trace map. The proof
uses the proved restriction/trace index identity; no new trace map or
injectivity premise is introduced.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- The literal H2 trace is injective when restriction of a full-order
class generates the subgroup H2 of its exact class-system cardinality. -/
theorem originalClassH2_trace_injective
    {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
    (u : groupCohomology C 2) (hu : addOrderOf u = Nat.card G)
    (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    (hc : Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Nat.card S)
    (hg : Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤) :
    Function.Injective (subgroupCohomologyTrace C S 2).hom := by
  let cor := (subgroupCohomologyTrace C S 2).hom
  let r := (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
  haveI : Finite (groupCohomology (Rep.res S.subtype C) 2) :=
    Nat.finite_of_card_ne_zero (hc.trans_ne (Nat.card_pos (α := S)).ne')
  have hidx : Nat.card S * S.index = Nat.card G := S.card_mul_index
  have hidx0 : S.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hidx
    exact (Nat.card_pos (α := G)).ne' hidx.symm
  have hkill (x : groupCohomology (Rep.res S.subtype C) 2) : (Nat.card S : ℤ) • x = 0 := by
    rw [← hc, natCast_zsmul]
    exact card_nsmul_eq_zero'
  apply (injective_iff_map_eq_zero cor).mpr
  intro z hz
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (show z ∈ Submodule.span ℤ {r u} by rw [hg]; exact Submodule.mem_top)
  have hk' : k • r u = z := by
    rw [← Int.cast_smul_eq_zsmul ℤ k (r u), Int.cast_id]
    exact hk
  rw [← hk'] at hz ⊢
  have ht : cor (k • r u) = k • (S.index • u) := by
    rw [map_zsmul]
    exact congrArg (fun x => k • x) (originalCohomology_trace_restriction_apply C S 2 u)
  rw [ht, ← natCast_zsmul, smul_smul, ← addOrderOf_dvd_iff_zsmul_eq_zero, hu, ← hidx] at hz
  push_cast at hz
  obtain ⟨m, rfl⟩ := (mul_dvd_mul_iff_right (by exact_mod_cast hidx0)).mp hz
  rw [mul_comm, ← smul_smul, hkill, zsmul_zero]

/-- Zero of the actual full-group H2 coefficient map forces zero of
its genuine subgroup map when the target has the original class data.
Trace naturality and its proved injectivity discharge the comparison. -/
theorem originalClassH2_zero_map_restricts
    {G : Type} [Group G] [Fintype G] (M C : Rep ℤ G)
    (u : groupCohomology C 2) (hu : addOrderOf u = Nat.card G)
    (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    (hc : Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Nat.card S)
    (hg : Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (f : M ⟶ C) (hf : (groupCohomology.functor ℤ G 2).map f = 0) :
    (groupCohomology.functor ℤ S 2).map ((Rep.resFunctor S.subtype).map f) = 0 := by
  ext x
  apply originalClassH2_trace_injective C u hu S hc hg
  have ht := originalCohomologyTrace_coefficient_naturality S f 2
  erw [hf, Limits.comp_zero] at ht
  have h := congrArg (fun t : groupCohomology (Rep.res S.subtype M) 2 ⟶
      groupCohomology C 2 => t.hom x)
    ht
  change (subgroupCohomologyTrace C S 2).hom
    (((groupCohomology.functor ℤ S 2).map ((Rep.resFunctor S.subtype).map f)).hom x) = 0 at h
  change (subgroupCohomologyTrace C S 2).hom
    (((groupCohomology.functor ℤ S 2).map ((Rep.resFunctor S.subtype).map f)).hom x) =
      (subgroupCohomologyTrace C S 2).hom 0
  rw [map_zero]
  exact h

open scoped NumberField

/-- Unpack the actual normalized quotient class system to obtain
injectivity of every original subgroup H2 trace. No trace-injectivity
or selected fundamental class is supplied. -/
theorem originalClassQuotient_subgroup_trace_injective
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L T hT)
    (S : Subgroup Gal(L/K)) [Fintype S] [Fintype (Gal(L/K) ⧸ S)] :
    Function.Injective (subgroupCohomologyTrace
      (originalIdeleClassesModOutsideRep K L T hT) S 2).hom := by
  obtain ⟨u, hu, _, hc, hg, _⟩ := hsys
  exact originalClassH2_trace_injective _ u
    (hu.trans (IsGalois.card_aut_eq_finrank K L).symm) S (hc S) (hg S)

end
end Dubon2026

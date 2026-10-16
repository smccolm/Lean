import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Dubon2026.FiniteGaloisH2BaseChangeComparison
import Dubon2026.OriginalFiniteGaloisImage

/-! # The actual finite-image map is surjective on original H2

Reuse the proved group-and-coefficient change isomorphism. This permits
the already normalized local fundamental class in the literal image to
be represented in the original finite completion itself, as needed for
DUB-17's full-order idele-class construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

/-- A literal original field embedding that is an algebra equivalence induces a surjection on actual finite continuous unit H2. -/
theorem finiteGaloisUnitBaseChangeH2_surjective_of_equiv
    (e : L ≃ₐ[K] M) (he : ∀ x : L, algebraMap L M x = e x) :
    Function.Surjective (finiteGaloisUnitBaseChangeH2 K K L M) := by
  have hg : (galoisBaseChangeRestriction K K L M : Gal(M/K) → Gal(L/K)) = e.autCongr.symm := by
    funext σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M).injective
    rw [galoisBaseChangeRestriction_commutes, he, he]
    change σ (e x) = e (e.symm (σ (e x)))
    exact (e.apply_symm_apply _).symm
  let g := MulEquiv.ofBijective (galoisBaseChangeRestriction K K L M)
    (hg ▸ e.autCongr.symm.bijective)
  let φ := galoisUnitBaseChangeInclusion K K L M
  have hφ : Function.Bijective φ.hom := by
    have hf : (φ.hom : Additive Lˣ → Additive Mˣ) =
        (Units.mapEquiv e.toMulEquiv).toAdditive := by
      funext u
      apply congrArg Additive.ofMul
      apply Units.ext
      exact he u.toMul.val
    rw [hf]
    exact (Units.mapEquiv e.toMulEquiv).toAdditive.bijective
  letI : Mono φ := (Rep.mono_iff_injective φ).mpr hφ.injective
  letI : Epi φ := (Rep.epi_iff_surjective φ).mpr hφ.surjective
  letI : IsIso φ := isIso_of_mono_of_epi φ
  letI : IsIso (groupCohomology.map (galoisBaseChangeRestriction K K L M) φ 2) :=
    @originalGroupChangeCohomology_isIso ℤ Gal(M/K) Gal(L/K) _ _ _
      (Rep.ofAlgebraAutOnUnits K L) (Rep.ofAlgebraAutOnUnits K M) g φ ‹IsIso φ› 2
  have hs := (ModuleCat.epi_iff_surjective
    (groupCohomology.map (galoisBaseChangeRestriction K K L M) φ 2)).mp inferInstance
  let eL := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  let eM := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K M)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := M))
  intro y
  obtain ⟨z, hz⟩ := hs (eM y)
  refine ⟨eL.symm z, eM.injective ?_⟩
  change continuousDiscreteH2Equiv _ _ (finiteGaloisUnitBaseChangeH2 K K L M (eL.symm z)) = _
  rw [continuousDiscreteH2Equiv_finiteGaloisBaseChange]
  change groupCohomology.map (galoisBaseChangeRestriction K K L M) φ 2 (eL (eL.symm z)) = eM y
  rw [eL.apply_symm_apply]
  exact hz

end
end Dubon2026

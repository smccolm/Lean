import Dubon2026.OriginalFullIdeleCohomologySequence
import Dubon2026.OriginalUnramifiedIdeleSupport
import Dubon2026.OriginalIdeleLocalUnitAssembly

/-! # Every original finite-Galois idele H2 class has finite stable support

The finitely many values of an actual cocycle have a common original
idele support. Its proved stable unramified enlargement lifts that same
cocycle to the original supported coefficient. This is the finite-support
entry into local H2 detection serving DUB-17's arithmetic invariant sum-zero.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The literal inclusion of the original supported-idele representation into full ideles. -/
def originalSupportedFullIdeleInclusion
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) :
    originalSupportedIdeleRep K L S hS ⟶ originalFullIdeleRep K L :=
  Rep.ofHom ⟨(numberFieldSupportedIdeles L S).subtype.toAdditive.toIntLinearMap,
    by intro σ; rfl⟩

/-- Every finite family of actual ideles belongs to one finite stable support with unramified complement. -/
theorem originalIdele_finiteFamily_supported [FiniteDimensional K L]
    {ι : Type} [Fintype ι] (a : ι → (AdeleRing (𝓞 L) L)ˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) ∧
      ∀ i, a i ∈ numberFieldSupportedIdeles L S := by
  have hf (i : ι) :
      {w | numberFieldIdeleFiniteComponent L w (a i) ∉ (w.adicCompletionIntegers L).units}.Finite :=
    Filter.eventually_cofinite.mp (originalIdele_finiteComponent_eventually_integerUnit L (a i))
  let T := Finset.univ.biUnion (fun i => (hf i).toFinset)
  obtain ⟨S, hTS, hS, _, hu⟩ := original_exists_unramified_galoisStable_idele_support K L T
  refine ⟨S, hS, hu, ?_⟩
  intro i
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro w hw
  by_contra hn
  apply hw
  apply hTS
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, (Set.Finite.mem_toFinset _).mpr hn⟩

/-- Every actual idele H2 class is the image of a class on a constructed finite stable support with unramified complement. -/
theorem originalIdeleH2_exists_supported_lift [FiniteDimensional K L]
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) ∧
      ∃ y : groupCohomology (originalSupportedIdeleRep K L S hS) 2,
        (groupCohomology.functor ℤ Gal(L/K) 2).map
          (originalSupportedFullIdeleInclusion K L S hS) y = x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    obtain ⟨S, hS, hu, hc⟩ := originalIdele_finiteFamily_supported K L (fun g => (c g).toMul)
    let d : groupCohomology.cocycles₂ (originalSupportedIdeleRep K L S hS) :=
      ⟨fun g => Additive.ofMul ⟨(c g).toMul, hc g⟩, by
        apply (groupCohomology.mem_cocycles₂_iff _).mpr
        intro g h k
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg Additive.toMul
          ((groupCohomology.mem_cocycles₂_iff _).mp c.property g h k)⟩
    refine ⟨S, hS, hu, groupCohomology.H2π _ d, ?_⟩
    change groupCohomology.map (MonoidHom.id Gal(L/K))
      (originalSupportedFullIdeleInclusion K L S hS) 2 (groupCohomology.H2π _ d) = _
    rw [groupCohomology.H2π_comp_map_apply]
    congr 1

end
end Dubon2026

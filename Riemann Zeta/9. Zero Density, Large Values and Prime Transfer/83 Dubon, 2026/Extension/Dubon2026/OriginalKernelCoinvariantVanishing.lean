import Dubon2026.OriginalCoefficientKernelSequence
import Dubon2026.OriginalHomologyFirstFromCoinvariants

/-! # The actual kernel's coinvariants from first homology

The genuine homology sequence makes the kernel's H0 map injective when
the original target H1 vanishes. An injective next coinvariant map
makes that same map zero. Pinned H0 identifies this with the literal
kernel coinvariants, completing the homological part of the mod-p
comparison on DUB-17's projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits

/-- A surjective original map, injective on coinvariants and with zero target first homology, has zero actual kernel coinvariants. -/
theorem originalCoefficientKernel_coinvariants_zero
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom)
    (hcoin : Function.Injective (Representation.Coinvariants.map A.ρ B.ρ f.hom))
    (hfirst : IsZero (groupHomology B 1))
    (x : originalCoefficientKernel f) :
    Representation.Coinvariants.mk (originalCoefficientKernel f).ρ x = 0 := by
  have hX := originalCoefficientKernel_shortExact f hf
  haveI : Mono ((groupHomology.functor k G 0).map (originalCoefficientKernelInclusion f)) :=
    (groupHomology.mapShortComplex₁_exact hX (i := 1) (j := 0) rfl).mono_g
      (hfirst.eq_zero_of_src _)
  haveI : Mono ((groupHomology.functor k G 0).map f) :=
    (ModuleCat.mono_iff_injective _).mpr
      (originalHomologyH0Map_injective_of_coinvariants f hcoin)
  have hz : (groupHomology.functor k G 0).map (originalCoefficientKernelInclusion f) = 0 :=
    (groupHomology.mapShortComplex₂_exact hX 0).mono_g_iff.mp
      (inferInstance : Mono ((groupHomology.functor k G 0).map f))
  have hzero := IsZero.of_mono_eq_zero _ hz
  have hc : IsZero ((Rep.coinvariantsFunctor k G).obj (originalCoefficientKernel f)) :=
    hzero.of_iso (groupHomology.H0Iso (originalCoefficientKernel f)).symm
  have he := hc.eq_of_src (𝟙 _) 0
  exact congrArg (fun j => j.hom (Representation.Coinvariants.mk
    (originalCoefficientKernel f).ρ x)) he

end
end Dubon2026

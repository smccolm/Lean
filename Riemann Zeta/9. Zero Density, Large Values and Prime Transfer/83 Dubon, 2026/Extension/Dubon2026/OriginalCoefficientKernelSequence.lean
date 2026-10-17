import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-! # The literal kernel sequence of an original coefficient map

The mod-p projectivity argument uses the genuine kernel of its explicit
coinduced comparison map. This retains that kernel and its exact
sequence rather than an assumed presentation, on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (f : A ⟶ B)

/-- The actual kernel with the action inherited from its original source. -/
abbrev originalCoefficientKernel : Rep k G :=
  A.subrepresentation (LinearMap.ker f.hom.toLinearMap) fun g x hx => by
    change f.hom x = 0 at hx
    change f.hom (A.ρ g x) = 0
    rw [Rep.hom_comm_apply, hx, map_zero]

/-- The literal original coefficient kernel included into its source. -/
def originalCoefficientKernelInclusion : originalCoefficientKernel f ⟶ A :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

/-- The actual kernel, source and target with the original coefficient map. -/
def originalCoefficientKernelShortComplex : ShortComplex (Rep k G) where
  X₁ := originalCoefficientKernel f
  X₂ := A
  X₃ := B
  f := originalCoefficientKernelInclusion f
  g := f
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.property))

/-- A surjective original coefficient map gives its literal kernel short exact sequence. -/
theorem originalCoefficientKernel_shortExact (hf : Function.Surjective f.hom) :
    (originalCoefficientKernelShortComplex f).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr hf }
  apply ((originalCoefficientKernelShortComplex f).exact_map_iff_of_faithful
    (forget₂ (Rep k G) (ModuleCat k))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact Submodule.range_subtype _

end
end Dubon2026

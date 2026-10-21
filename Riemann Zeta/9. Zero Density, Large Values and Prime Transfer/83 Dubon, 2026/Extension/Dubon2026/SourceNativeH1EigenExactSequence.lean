import Dubon2026.SourceHeckeEigenvectorLift
import Dubon2026.SourceIntegralCohomologyFinite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! Native H1 exactness for the required residual binary coefficient flag.
DUB-17/18 -> residual modular Galois association -> finite-characteristic
weight/level reduction -> eigenvalue descent through the actual coefficient
flag. The pinned Mathlib long exact sequence replaces the external custom
cocycle lifting argument. Finite coefficients and the already proved native
H1 finiteness theorem supply the finite-dimensional source needed for lifting
the prescribed eigenvalues.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Exactness on native H1 follows from exactness of the actual coefficient
representations through the pinned Mathlib long exact sequence. -/
theorem sourceNativeH1_range_eq_ker {F G : Type} [Field F] [Group G]
    (X : ShortComplex (Rep F G)) (hX : X.ShortExact) :
    LinearMap.range ((groupCohomology.functor F G 1).map X.f).hom =
      LinearMap.ker ((groupCohomology.functor F G 1).map X.g).hom :=
  (groupCohomology.mapShortComplex₂_exact hX 1).moduleCat_range_eq_ker

/-- A native H1 eigensystem survives in a quotient coefficient system or in
its preceding subrepresentation. Only coefficient exactness, actual operator
compatibility and commutativity are premises; H1 exactness, its source
finiteness and realization of the prescribed eigenvalues are derived. -/
theorem sourceNativeH1_eigen_exact_step {F G ι : Type} [Field F] [Group G]
    [Group.FG G] (X : ShortComplex (Rep F G)) (hX : X.ShortExact)
    [Module.Finite F X.X₁]
    (T₁ : ι → Module.End F (groupCohomology.H1 X.X₁))
    (T₂ : ι → Module.End F (groupCohomology.H1 X.X₂))
    (T₃ : ι → Module.End F (groupCohomology.H1 X.X₃))
    (hcomm : ∀ i j, Commute (T₁ i) (T₁ j))
    (hf : ∀ i, ((groupCohomology.functor F G 1).map X.f).hom.comp (T₁ i) =
      (T₂ i).comp ((groupCohomology.functor F G 1).map X.f).hom)
    (hg : ∀ i, ((groupCohomology.functor F G 1).map X.g).hom.comp (T₂ i) =
      (T₃ i).comp ((groupCohomology.functor F G 1).map X.g).hom)
    (eigenvalues : ι → F) (x : groupCohomology.H1 X.X₂) (hx : x ≠ 0)
    (heig : ∀ i, T₂ i x = eigenvalues i • x) :
    (∃ y : groupCohomology.H1 X.X₃, y ≠ 0 ∧ ∀ i, T₃ i y = eigenvalues i • y) ∨
      (∃ y : groupCohomology.H1 X.X₁, y ≠ 0 ∧ ∀ i, T₁ i y = eigenvalues i • y) := by
  let f := ((groupCohomology.functor F G 1).map X.f).hom
  let g := ((groupCohomology.functor F G 1).map X.g).hom
  by_cases hzero : g x = 0
  · right
    letI : Module.Finite F (groupCohomology.H1 X.X₁) := sourceH1Finite X.X₁
    apply sourceHeckeEigenvector_exists_in_source T₁ T₂ hcomm f hf eigenvalues x hx heig
    have hex : LinearMap.range f = LinearMap.ker g := sourceNativeH1_range_eq_ker X hX
    have hr : x ∈ LinearMap.range f :=
      hex.symm ▸ (show x ∈ LinearMap.ker g from hzero)
    exact hr
  · left
    refine ⟨g x, hzero, fun i => ?_⟩
    have h : g (T₂ i x) = T₃ i (g x) := LinearMap.congr_fun (hg i) x
    rw [← h, heig]
    exact g.map_smul _ _

end
end Dubon2026

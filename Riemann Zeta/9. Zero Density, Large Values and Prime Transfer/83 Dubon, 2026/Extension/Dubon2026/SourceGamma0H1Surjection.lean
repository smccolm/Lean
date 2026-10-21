import Dubon2026.SourceGamma0H2
import Dubon2026.SourceNativeH1EigenExactSequence

/-! Original Gamma0 H1 classes lift through actual coefficient surjections.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> lifting the actual character eigenclass into its finite
function representation. The original Gamma0 H2 vanishing and pinned
native long exact sequence discharge cohomological surjectivity.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits CongruenceSubgroup

/-- Every surjective morphism of original Gamma0 coefficient representations
induces a surjection on native H1 when six is invertible. H2 vanishing is
proved for the actual kernel representation. -/
theorem sourceGamma0H1_map_surjective {R : Type} [CommRing R] (Q : ℕ)
    (h6 : IsUnit (6 : R)) {A B : Rep R (Gamma0 Q)}
    (f : A ⟶ B) (hf : Function.Surjective f) :
    Function.Surjective ((groupCohomology.functor R (Gamma0 Q) 1).map f) := by
  let X : ShortComplex (Rep R (Gamma0 Q)) :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hX : X.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)
      mono_f := by dsimp [X]; infer_instance
      epi_g := (Rep.epi_iff_surjective f).mpr hf }
  have hex := groupCohomology.mapShortComplex₃_exact hX (i := 1) (j := 2) rfl
  letI : Subsingleton (groupCohomology X.X₁ 2) := sourceGamma0H2_subsingleton Q h6 X.X₁
  have hz : IsZero (groupCohomology X.X₁ 2) := ModuleCat.isZero_of_subsingleton _
  have hg : (groupCohomology.mapShortComplex₃ hX (i := 1) (j := 2) rfl).g = 0 :=
    hz.eq_of_tgt _ _
  have hepi : Epi ((groupCohomology.functor R (Gamma0 Q) 1).map f) := hex.epi_f hg
  exact (ModuleCat.epi_iff_surjective _).mp hepi

open Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- A prescribed nonzero original Gamma0 H1 eigensystem lifts through an
actual coefficient surjection when six is invertible. Finite coefficients
and full commuting Hecke actions suffice; no H1 surjectivity, H2 vanishing,
finite cohomology or nonzero source eigenclass is assumed. -/
theorem sourceGamma0H1_eigen_lift {F ι : Type} [Field F] (Q : ℕ) [NeZero Q]
    (h6 : (6 : F) ≠ 0) {A B : Rep F (Gamma0 Q)} [Module.Finite F A]
    (f : A ⟶ B) (hf : Function.Surjective f)
    (T : ι → Module.End F (groupCohomology.H1 A))
    (U : ι → Module.End F (groupCohomology.H1 B))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hmap : ∀ i, ((groupCohomology.functor F (Gamma0 Q) 1).map f).hom.comp (T i) =
      (U i).comp ((groupCohomology.functor F (Gamma0 Q) 1).map f).hom)
    (values : ι → F) (x : groupCohomology.H1 B) (hx : x ≠ 0)
    (heig : ∀ i, U i x = values i • x) :
    ∃ y : groupCohomology.H1 A, y ≠ 0 ∧ ∀ i, T i y = values i • y := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI : Module.Finite F (groupCohomology.H1 A) := sourceH1Finite A
  apply sourceHeckeEigenvector_exists_in_source T U hcomm
    ((groupCohomology.functor F (Gamma0 Q) 1).map f).hom hmap values x hx heig
  exact sourceGamma0H1_map_surjective Q (isUnit_iff_ne_zero.mpr h6) f hf x

end
end Dubon2026

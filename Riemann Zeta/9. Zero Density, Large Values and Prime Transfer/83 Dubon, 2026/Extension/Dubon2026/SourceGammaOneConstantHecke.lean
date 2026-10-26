import Dubon2026.SourceGammaOneHeckeSubgroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB-17/18 -> original all-weight adic association -> finite Gamma1
realization -> exact Hecke comparison. Construct the genuine diagonal
correspondence on constant-coefficient native Gamma1 H1 using the same
literal integral conjugation and finite coset trace. The coefficient map
is explicit; choosing identity gives the ordinary trivial-coefficient
correspondence. No transfer-intertwining claim is assumed or inferred. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private local instance gammaOneHeckeFinite (M n : ℕ) [NeZero n] :
    Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M n) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M n
  exact Fintype.ofFinite _

variable (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    (M n : ℕ) [NeZero n] (b : Module.End R V)

/-- The explicit constant coefficient map intertwines the genuine two
Gamma1 subgroup actions without an extra compatibility hypothesis. -/
def sourceGammaOneConstantHeckeMorphism :
    Rep.res (sourceGammaOneHeckeConjugation M n) (Rep.trivial R (Gamma1 M) V) ⟶
      Rep.res (sourceGammaOneHeckeUpper M n).subtype (Rep.trivial R (Gamma1 M) V) :=
  Rep.ofHom {
    toLinearMap := b
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      rfl }

/-- The full actual Gamma1 diagonal correspondence on native cocycles. -/
def sourceGammaOneConstantHeckeCocycles :
    Module.End R (groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) :=
  (sourceHeckeTraceCocycles (Rep.trivial R (Gamma1 M) V) (sourceGammaOneHeckeUpper M n)).comp
    (groupCohomology.mapCocycles₁ (sourceGammaOneHeckeConjugation M n)
      (sourceGammaOneConstantHeckeMorphism R V M n b)).hom

/-- The full actual Gamma1 diagonal correspondence on native H1. -/
def sourceGammaOneConstantHeckeH1 :
    Module.End R (groupCohomology.H1 (Rep.trivial R (Gamma1 M) V)) :=
  (sourceHeckeH1Trace (Rep.trivial R (Gamma1 M) V) (sourceGammaOneHeckeUpper M n)).comp
    (groupCohomology.map (sourceGammaOneHeckeConjugation M n)
      (sourceGammaOneConstantHeckeMorphism R V M n b) 1).hom

/-- The native H1 operator is represented by the same full traced cocycle. -/
theorem sourceGammaOneConstantHeckeH1_cocycle
    (c : groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) :
    sourceGammaOneConstantHeckeH1 R V M n b (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (sourceGammaOneConstantHeckeCocycles R V M n b c) := by
  change sourceHeckeH1Trace _ _
    ((groupCohomology.map _ _ 1) (groupCohomology.H1π _ c)) = _
  rw [groupCohomology.H1π_comp_map_apply, sourceHeckeH1Trace_cocycle]
  rfl

/-- Every term of the genuine Gamma1 correspondence is retained in its
literal finite coset formula, including the explicit coefficient action. -/
theorem sourceGammaOneConstantHeckeCocycles_apply
    (c : groupCohomology.cocycles₁ (Rep.trivial R (Gamma1 M) V)) (g : Gamma1 M) :
    sourceGammaOneConstantHeckeCocycles R V M n b c g =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M n,
        b (c (sourceGammaOneHeckeConjugation M n
          (cosetTransition (sourceGammaOneHeckeUpper M n) g q))) := rfl

end
end Dubon2026

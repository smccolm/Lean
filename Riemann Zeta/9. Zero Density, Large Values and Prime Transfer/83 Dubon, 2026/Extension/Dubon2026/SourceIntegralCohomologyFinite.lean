import Dubon2026.HomogeneousMonomialBasis
import Dubon2026.SourceModularCuspDivisors
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Schreier

/-! Finite integral cohomology for the original binary coefficient system.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> residual H1
eigensystem -> finite integral H1 module.

The finite-generator argument is adapted to native Mathlib cohomology from
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.lean,
section FiniteGen (Apache-2.0; retained source archive LICENSE and NOTICE).
The existing local monomial basis supplies coefficient finiteness directly.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem cocycle_zero_on_closure {R G : Type} [CommRing R] [Group G]
    (A : Rep R G) (c : groupCohomology.cocycles₁ A) (S : Set G)
    (hS : ∀ s ∈ S, c s = 0) (g : G) (hg : g ∈ Subgroup.closure S) : c g = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact groupCohomology.cocycles₁_map_one c
  | mul x y _ _ hx hy =>
    rw [(groupCohomology.mem_cocycles₁_iff c).mp c.property, hx, hy, map_zero, add_zero]
  | inv x _ hx =>
    have h := groupCohomology.cocycles₁_map_inv c x
    rw [hx, neg_zero] at h
    have h' := congrArg (A.ρ x⁻¹) h
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h'

/-- A native cocycle is determined by its values on finitely many group generators,
so finite coefficients over a Noetherian ring give a finite cocycle module. -/
theorem sourceCocyclesFinite {R G : Type} [CommRing R] [Group G]
    [IsNoetherianRing R] [Group.FG G] (A : Rep R G) [Module.Finite R A] :
    Module.Finite R (groupCohomology.cocycles₁ A) := by
  classical
  obtain ⟨S, hS⟩ := (inferInstance : Group.FG G).out
  let ev : groupCohomology.cocycles₁ A →ₗ[R] (S → A) :=
    { toFun := fun c s => c s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply groupCohomology.cocycles₁_ext
    intro g
    exact cocycle_zero_on_closure A c S
      (fun s hs => congrFun hc ⟨s, hs⟩) g (by rw [hS]; trivial)
  exact Module.Finite.of_injective ev hev

/-- Native first cohomology is a finite module under the same actual finiteness
hypotheses, by the surjective cocycle quotient map. -/
theorem sourceH1Finite {R G : Type} [CommRing R] [Group G]
    [IsNoetherianRing R] [Group.FG G] (A : Rep R G) [Module.Finite R A] :
    Module.Finite R (groupCohomology.H1 A) := by
  letI := sourceCocyclesFinite A
  exact Module.Finite.of_surjective (groupCohomology.H1π A).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- The original column-binary representation over any coefficient ring. -/
abbrev sourceBinaryCoefficientRep (R : Type) [CommRing R] (Q w : ℕ) :
    Rep R (Gamma0 Q) :=
  Rep.of ((homogeneousGLRepresentation w).comp ((mapGL R).comp (Gamma0 Q).subtype))

/-- The actual integral binary H1 at every source level is finite over Z.
Neither finite generation of Gamma0 nor cohomological finiteness is supplied. -/
theorem sourceIntegralBinaryH1Finite (Q w : ℕ) [NeZero Q] :
    Module.Finite ℤ (groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  exact @sourceH1Finite ℤ (Gamma0 Q) _ _ _ _ (sourceBinaryCoefficientRep ℤ Q w)
    (Module.Finite.of_basis (binaryHomogeneousMonomialBasis (R := ℤ) w))

end
end Dubon2026

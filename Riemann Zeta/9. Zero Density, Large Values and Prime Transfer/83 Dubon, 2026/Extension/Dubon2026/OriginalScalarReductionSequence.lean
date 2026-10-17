import Dubon2026.OriginalPGroupFirstHomology

/-! # The actual scalar-reduction sequence for integral coefficients

Reduction modulo a nonzero scalar of an integral torsion-free original
coefficient is a literal short exact sequence. It supplies the mod-p
homology input used to prove projectivity of the actual fundamental
free kernel on DUB-17's finite class/Ext duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (m : k)

/-- Actual scalar multiplication on the original integral coefficient. -/
def originalScalarMultiplication : A ⟶ A := m • 𝟙 A

/-- The actual scalar image in the original coefficient module. -/
abbrev originalScalarImage : Submodule k A :=
  LinearMap.range (originalScalarMultiplication A m).hom.toLinearMap

/-- Actual scalar multiplication agrees with the integral module operation. -/
theorem originalScalarMultiplication_apply (x : A) :
    (originalScalarMultiplication A m).hom x = m • x := by
  rw [originalScalarMultiplication, Rep.smul_hom]
  rfl

/-- The literal scalar-image quotient retains the original action. -/
def originalScalarReduction : Rep k G :=
  Rep.of (Representation.quotient A.ρ (originalScalarImage A m) fun g x hx => by
    obtain ⟨y, hy⟩ := hx
    change (originalScalarMultiplication A m).hom y = x at hy
    refine ⟨A.ρ g y, ?_⟩
    change (originalScalarMultiplication A m).hom (A.ρ g y) = A.ρ g x
    rw [Rep.hom_comm_apply, hy])

/-- The actual original coefficient projected to its scalar-image quotient. -/
def originalScalarReductionProjection : A ⟶ originalScalarReduction A m :=
  Rep.ofHom ⟨(originalScalarImage A m).mkQ, fun _ => rfl⟩

/-- The literal multiplication and reduction sequence. -/
def originalScalarReductionShortComplex : ShortComplex (Rep k G) where
  X₁ := A
  X₂ := A
  X₃ := originalScalarReduction A m
  f := originalScalarMultiplication A m
  g := originalScalarReductionProjection A m
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The actual scalar quotient sequence is short exact when the original coefficient is torsion free and the scalar is nonzero. -/
theorem originalScalarReduction_shortExact
    [IsDomain k] [Module.IsTorsionFree k A] (hm : m ≠ 0) :
    (originalScalarReductionShortComplex A m).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr ?_
    epi_g := (Rep.epi_iff_surjective _).mpr (originalScalarImage A m).mkQ_surjective }
  · apply ((originalScalarReductionShortComplex A m).exact_map_iff_of_faithful
      (forget₂ (Rep k G) (ModuleCat k))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  · intro x y hxy
    change (originalScalarMultiplication A m).hom x =
      (originalScalarMultiplication A m).hom y at hxy
    rw [originalScalarMultiplication_apply, originalScalarMultiplication_apply] at hxy
    exact smul_right_injective A hm hxy

/-- The actual scalar reduction is killed by that scalar. -/
theorem originalScalarReduction_annihilated (x : originalScalarReduction A m) : m • x = 0 := by
  obtain ⟨a, rfl⟩ := (originalScalarImage A m).mkQ_surjective x
  change (originalScalarImage A m).mkQ (m • a) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨a, originalScalarMultiplication_apply A m a⟩

end
end Dubon2026

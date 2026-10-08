import Dubon2026.CompactSl2Basis
import Dubon2026.AdelicEnvelopingCasimir

/-! # The original cusp generator as an actual compact lowest-weight vector -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem compact_weight_scalar {W : Type*} [AddCommGroup W] [Module ℂ W]
    (K : Module.End ℂ W) (v : W) (k : ℂ) (hK : K v = (k * Complex.I) • v) :
    ((-Complex.I) • K) v = k • v := by
  rw [LinearMap.smul_apply, hK, smul_smul]
  congr 1
  calc
    -Complex.I * (k * Complex.I) = k * (-(Complex.I * Complex.I)) := by ring
    _ = k := by simp

private theorem lowering_from_holomorphy {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A U K : Module.End ℂ W) (v : W) (k : ℂ)
    (hA : A v - Complex.I • U v = (k / 2) • v) (hK : K v = (k * Complex.I) • v) :
    (A - Complex.I • U + (Complex.I / 2) • K) v = 0 := by
  change A v - Complex.I • U v + (Complex.I / 2) • K v = 0
  rw [hA, hK, smul_smul, ← add_smul]
  have he : k / 2 + Complex.I / 2 * (k * Complex.I) = 0 := by
    calc
      k / 2 + Complex.I / 2 * (k * Complex.I) = k / 2 * (1 + Complex.I * Complex.I) := by ring
      _ = 0 := by simp
  rw [he, zero_smul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

local notation "A" => adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff
local notation "U" => adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff
local notation "K" => adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff

/-- The genuine complex matrix Lie action equips the actual adelic smooth subspace with its original Lie module structure. -/
instance adelicSmoothComplexLieRingModule : LieRingModule ComplexSl2 (adelicRealSmoothSubmodule f) :=
  LieRingModule.compLieHom _ (adelicComplexSl2Action f)

/-- The original Lie module action is complex-linear in both variables. -/
instance adelicSmoothComplexLieModule : LieModule ℂ ComplexSl2 (adelicRealSmoothSubmodule f) :=
  LieModule.compLieHom _ (adelicComplexSl2Action f)

/-- The original Lie bracket with a smooth vector is exactly the previously constructed Hilbert infinitesimal action. -/
theorem adelicSmoothComplexLie_apply (x : ComplexSl2) (v : adelicRealSmoothSubmodule f) :
    ⁅x, v⁆ = adelicComplexSl2Action f x v := rfl

/-- The original smooth generator retains its precise holomorphic identity. -/
theorem adelicSmoothGenerator_holomorphic :
    A (adelicSmoothGenerator f) - Complex.I • U (adelicSmoothGenerator f) =
      ((k : ℂ) / 2) • adelicSmoothGenerator f := by
  apply Subtype.ext
  exact adelicCyclicHilbertGenerator_holomorphic_identity f

/-- The original smooth generator retains its precise compact infinitesimal weight. -/
theorem adelicSmoothGenerator_compact_weight :
    K (adelicSmoothGenerator f) = ((k : ℂ) * Complex.I) • adelicSmoothGenerator f := by
  apply Subtype.ext
  exact adelicCyclicHilbertGenerator_compact_infinitesimal f

/-- The genuine compact matrix tangent acts by the original compact Hilbert derivative. -/
theorem adelicComplexSl2Action_compact_tangent :
    adelicComplexSl2Action f (complexSl2U - complexSl2F) = K := by
  simpa only [map_sub, adelicComplexSl2Action_U, adelicComplexSl2Action_F] using
    (adelicSmoothInfinitesimal_compact f).symm

/-- The original cusp generator has its exact compact Cartan weight in the actual matrix Lie module. -/
theorem adelicSmoothGenerator_compact_Cartan :
    ⁅compactSl2H, adelicSmoothGenerator f⁆ = (k : ℂ) • adelicSmoothGenerator f := by
  have he : adelicComplexSl2Action f compactSl2H = (-Complex.I) • K := by
    simp only [compactSl2H, map_smul, adelicComplexSl2Action_compact_tangent]
  exact (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) =>
    T (adelicSmoothGenerator f)) he).trans
    (compact_weight_scalar K (adelicSmoothGenerator f) (k : ℂ) (adelicSmoothGenerator_compact_weight f))

/-- The original lowering matrix annihilates the original smooth generator by its actual holomorphy. -/
theorem adelicSmoothGenerator_lowering_zero :
    ⁅compactSl2F, adelicSmoothGenerator f⁆ = 0 := by
  have he : adelicComplexSl2Action f compactSl2F = A - Complex.I • U + (Complex.I / 2) • K := by
    simpa only [LieHom.coe_toLinearMap, adelicComplexSl2Action_A, adelicComplexSl2Action_U,
      adelicComplexSl2Action_compact_tangent] using
      compactSl2F_holomorphic (adelicComplexSl2Action f).toLinearMap
  exact (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) =>
    T (adelicSmoothGenerator f)) he).trans
    (lowering_from_holomorphy A U K (adelicSmoothGenerator f) (k : ℂ)
      (adelicSmoothGenerator_holomorphic f) (adelicSmoothGenerator_compact_weight f))

/-- Every nonzero original cusp generator is a genuine primitive vector for the reversed actual compact sl2 triple. -/
theorem adelicSmoothGenerator_primitive (hf : f ≠ 0) :
    IsSl2Triple.HasPrimitiveVectorWith compactSl2Triple.symm (adelicSmoothGenerator f) (-(k : ℂ)) where
  ne_zero := by
    intro he
    exact adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val he)
  lie_h := (neg_lie compactSl2H (adelicSmoothGenerator f)).trans
    ((congrArg Neg.neg (adelicSmoothGenerator_compact_Cartan f)).trans
      (neg_smul (k : ℂ) (adelicSmoothGenerator f)).symm)
  lie_e := adelicSmoothGenerator_lowering_zero f

end
end Dubon2026

import Dubon2026.SourcePeriodBinaryEquivalence
import Dubon2026.SourcePeriodCohomologyInjective
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! The original primitive period class in column binary cohomology.
DUB-17/18 -> residual modular Galois association -> the original nonzero
binary H1 eigensystem. Native cohomological functoriality transports the
proved analytic period class along the actual coefficient equivalence.
SourcePrimitiveBinaryHeckeCohomology proves the actual full Hecke compatibility.
Integral-to-residual nonvanishing remains open.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CategoryTheory
open scoped MatrixGroups

/-- The original homogeneous column-substitution representation at the actual level. -/
abbrev sourcePeriodColumnRep (Γ : Subgroup SL(2, ℤ)) (n : ℕ) : Rep ℂ Γ :=
  Rep.of ((homogeneousGLRepresentation n).comp ((mapGL ℂ).comp Γ.subtype))

/-- The original analytic period coefficients and column binary forms are
isomorphic as representations, with factorial nonvanishing derived over C. -/
def sourcePeriodCoefficientIso (Γ : Subgroup SL(2, ℤ)) (n : ℕ) :
    sourcePeriodDualRep Γ n ≅ sourcePeriodColumnRep Γ n :=
  Rep.mkIso {
    __ := sourcePeriodBinaryEquiv n (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    isIntertwining' γ := sourcePeriodBinaryEquiv_intertwine n _ γ.val }

/-- The actual coefficient isomorphism induces the native H1 equivalence. -/
def sourcePeriodH1BinaryEquiv (Γ : Subgroup SL(2, ℤ)) (n : ℕ) :
    groupCohomology.H1 (sourcePeriodDualRep Γ n) ≃ₗ[ℂ]
      groupCohomology.H1 (sourcePeriodColumnRep Γ n) :=
  ((groupCohomology.functor ℂ Γ 1).mapIso (sourcePeriodCoefficientIso Γ n)).toLinearEquiv

/-- Transport of an actual original period class is the class of the transported
original cocycle, by native cohomological naturality. -/
theorem sourcePeriodH1BinaryEquiv_period
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {n : ℕ}
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = n + 2) (α : OnePoint ℚ) :
    sourcePeriodH1BinaryEquiv Γ n (sourcePeriodH1 f hk α) =
      groupCohomology.H1π (sourcePeriodColumnRep Γ n)
        (groupCohomology.mapCocycles₁ (MonoidHom.id Γ)
          (sourcePeriodCoefficientIso Γ n).hom (sourcePeriodCocycle f hk α)) := by
  change (groupCohomology.map (A := sourcePeriodDualRep Γ n)
    (B := sourcePeriodColumnRep Γ n) (MonoidHom.id Γ)
      (sourcePeriodCoefficientIso Γ n).hom 1)
        (groupCohomology.H1π (sourcePeriodDualRep Γ n) (sourcePeriodCocycle f hk α)) = _
  exact groupCohomology.H1π_comp_map_apply
    (A := sourcePeriodDualRep Γ n) (B := sourcePeriodColumnRep Γ n) (MonoidHom.id Γ)
    (sourcePeriodCoefficientIso Γ n).hom (sourcePeriodCocycle f hk α)

/-- The original Gamma0 cusp form realized in the literal column binary H1. -/
def sourceOriginalBinaryPeriodCohomology (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    CuspForm ((CongruenceSubgroup.Gamma0 Q).map (mapGL ℝ)) k →ₗ[ℂ]
      groupCohomology.H1 (sourcePeriodColumnRep (CongruenceSubgroup.Gamma0 Q) (k - 2).toNat) :=
  (sourcePeriodH1BinaryEquiv (CongruenceSubgroup.Gamma0 Q) (k - 2).toNat).toLinearMap.comp
    (sourceOriginalPeriodCohomology Q k hk)

/-- The original cusp form remains faithfully realized after the proved
coefficient-convention comparison. -/
theorem sourceOriginalBinaryPeriodCohomology_injective
    (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    Function.Injective (sourceOriginalBinaryPeriodCohomology Q k hk) :=
  (sourcePeriodH1BinaryEquiv (CongruenceSubgroup.Gamma0 Q) (k - 2).toNat).injective.comp
    (sourceOriginalPeriodCohomology_injective Q k hk)

/-- Every actual normalized primitive form has a nonzero native binary H1
class in every source weight, without a supplied class or nonvanishing premise. -/
theorem sourcePrimitive_binaryPeriodCohomology_ne_zero
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm ≠ 0 := by
  intro hz
  apply primitiveCuspForm_ne_zero f
  exact (sourceOriginalBinaryPeriodCohomology_injective Q k hk)
    (hz.trans (map_zero (sourceOriginalBinaryPeriodCohomology Q k hk)).symm)

end
end Dubon2026

import Dubon2026.SourceEllipticSubfieldPointLift
import Dubon2026.SourceEllipticVariableAddEquiv
import Dubon2026.SourceEllipticTorsionReductionHom

/-! Reduction of the original curve's actual prime-to-residue torsion
through the proved good model. The existing coordinate-change equivalence,
torsion reduction homomorphism and injectivity are composed directly.
This is the source map needed for inertia-equivariance and the DUB-17/18
exceptional-fiber census; no full reduction homomorphism on arbitrary
nonintegral points is required. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
open SourceEllipticFunctionField SourceEllipticVelu SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]
variable {A : ValuationSubring M}
variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
variable (hκ : κ • E.baseChange M = W.map A.subtype)

/-- The actual original-curve point transported to the specified good model. -/
def modelPointEquiv : (E.baseChange M).toAffine.Point ≃+ (W.map A.subtype).toAffine.Point :=
  (variableChangeAddEquiv κ (E.baseChange M).toAffine).symm.trans
    (AddEquiv.cast (M := fun V : WeierstrassCurve M => V.toAffine.Point) hκ)

theorem modelPointEquiv_coords (P : (E.baseChange M).toAffine.Point) :
    coordsOrZero (modelPointEquiv E W κ hκ P) =
      coordsOrZero (vcInvFun κ (E.baseChange M).toAffine P) := by
  exact coordsOrZero_cast hκ _

/-- The original torsion subgroup mapped into the good model's torsion subgroup. -/
def modelTorsionMap (N : ℕ) :
    Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
      Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ) where
  toFun P := ⟨modelPointEquiv E W κ hκ P, by
    have hP : (N : ℤ) • (P : (E.baseChange M).toAffine.Point) = 0 := by
      simpa only [Submodule.mem_torsionBy_iff] using P.property
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext ((modelPointEquiv E W κ hκ).map_add P.val Q.val)

variable [DecidableEq (ResidueField A)]

/-- Actual reduction of the original torsion, using the specified good model. -/
def modelTorsionReduction (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) :
    Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
      (W.map (residue A)).toAffine.Point :=
  (torsionReductionHom hΔ hN).comp (modelTorsionMap E W κ hκ N)

theorem modelTorsionReduction_apply (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A))
    (P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)) :
    modelTorsionReduction E W κ hκ hΔ hN P =
      reducePoint hΔ (modelPointEquiv E W κ hκ P) := rfl

theorem modelTorsionReduction_injective (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) :
    Function.Injective (modelTorsionReduction E W κ hκ hΔ hN) := by
  apply (torsionReductionHom_injective hΔ hN).comp
  intro P Q hPQ
  apply Subtype.ext
  exact (modelPointEquiv E W κ hκ).injective (congrArg Subtype.val hPQ)

end
end Dubon2026.SourceEllipticReduction

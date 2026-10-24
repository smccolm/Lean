import Dubon2026.SourceEllipticFaithfulTorsionModel
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! Identify the j-invariant of the actual reduced good model, then
produce its coordinate change to the prescribed elliptic residue curve.
Native j-invariance and the proved equal-j classification supply the
identification required by DUB-17/18 finite Galois specialization and the
exceptional-fiber census. No model identification is postulated. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve
noncomputable section

private theorem j_eq_of_curve_eq {R : Type*} [CommRing R]
    {V W : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic] (h : V = W) : V.j = W.j := by
  subst W
  rfl

theorem goodModel_integral_j
    {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
    (E : WeierstrassCurve F) [E.IsElliptic] (W : WeierstrassCurve A) [W.IsElliptic]
    (κ : VariableChange M) (hκ : κ • E.baseChange M = W.map A.subtype)
    {j : M} (hj : algebraMap F M E.j = j) (hjA : j ∈ A) : W.j = ⟨j, hjA⟩ := by
  apply Subtype.ext
  change A.subtype W.j = j
  rw [← W.map_j, ← j_eq_of_curve_eq hκ, variableChange_j]
  change (E.map (algebraMap F M)).j = j
  rw [E.map_j]
  exact hj

theorem goodModel_residue_j
    {F M K : Type*} [Field F] [Field M] [Field K] [Algebra F M] {A : ValuationSubring M}
    (E : WeierstrassCurve F) [E.IsElliptic] (W : WeierstrassCurve A) [W.IsElliptic]
    (κ : VariableChange M) (hκ : κ • E.baseChange M = W.map A.subtype)
    {j : M} (hj : algebraMap F M E.j = j) (hjA : j ∈ A)
    (φ : A →+* K) (a : K) (hφ : φ ⟨j, hjA⟩ = a) : (W.map φ).j = a := by
  rw [W.map_j, goodModel_integral_j E W κ hκ hj hjA, hφ]

theorem exists_prescribed_residue_model_change
    {F M K : Type*} [Field F] [Field M] [Field K] [IsAlgClosed K]
    [Algebra F M] {A : ValuationSubring M}
    (E : WeierstrassCurve F) [E.IsElliptic] (W : WeierstrassCurve A) [W.IsElliptic]
    (κ : VariableChange M) (hκ : κ • E.baseChange M = W.map A.subtype)
    {j : M} (hj : algebraMap F M E.j = j) (hjA : j ∈ A)
    (φ : A →+* K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hφ : φ ⟨j, hjA⟩ = E₀.j) :
    ∃ γ : VariableChange K, γ • W.map φ = E₀ :=
  exists_variableChange_of_j_eq (W.map φ) E₀
    (goodModel_residue_j E W κ hκ hj hjA φ E₀.j hφ)

end
end Dubon2026.SourceEllipticReduction

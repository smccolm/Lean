import Dubon2026.SourceGammaOneResidueArithmetic
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> original all-weight arithmetic association -> original
Gamma1 Tate Frobenius/inertia -> the action on residue places. Transport
the actual valuation rings by the inverse decomposition action; the
constant identity and native discrete-ring transport supply the place
axioms. This is a prerequisite for Picard specialization equivariance,
not a claim of good reduction or injectivity on torsion.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem decompositionResidueAut_constants (d : A.decompositionSubgroup ℚ) (a : kk) :
    decompositionResidueAut A Γ d (algebraMap kk Fb a) = algebraMap kk Fb (d • a) := by
  apply Subtype.ext
  change coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d)
      (algebraMap kk (LaurentSeries kk) a) = algebraMap kk (LaurentSeries kk) (d • a)
  simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt] using
    coeffMap_single (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d) 0 a

theorem decompositionResidueAut_inv (d : A.decompositionSubgroup ℚ) :
    decompositionResidueAut A Γ d⁻¹ = (decompositionResidueAut A Γ d).symm := by
  ext f
  rfl

/-- The literal valuation-ring equivalence under the inverse coefficient action. -/
def decompositionResidueValuationEquiv (d : A.decompositionSubgroup ℚ) (P : Place kk Fb) :
    P.toValuationSubring.comap (decompositionResidueAut A Γ d⁻¹).toRingHom ≃+*
      P.toValuationSubring where
  toFun f := ⟨decompositionResidueAut A Γ d⁻¹ f.val, f.property⟩
  invFun f := ⟨(decompositionResidueAut A Γ d⁻¹).symm f.val, by
    change decompositionResidueAut A Γ d⁻¹
      ((decompositionResidueAut A Γ d⁻¹).symm f.val) ∈ P.toValuationSubring
    rw [RingEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((decompositionResidueAut A Γ d⁻¹).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((decompositionResidueAut A Γ d⁻¹).apply_symm_apply f.val)
  map_mul' f g := Subtype.ext (map_mul (decompositionResidueAut A Γ d⁻¹) f.val g.val)
  map_add' f g := Subtype.ext (map_add (decompositionResidueAut A Γ d⁻¹) f.val g.val)

/-- The actual residue place transported by the original decomposition action. -/
def decompositionResiduePlace (d : A.decompositionSubgroup ℚ) (P : Place kk Fb) :
    Place kk Fb where
  toValuationSubring := P.toValuationSubring.comap (decompositionResidueAut A Γ d⁻¹).toRingHom
  algebraMap_mem' a := by
    change decompositionResidueAut A Γ d⁻¹ (algebraMap kk Fb a) ∈ P.toValuationSubring
    rw [decompositionResidueAut_constants]
    exact P.algebraMap_mem' _
  ne_top' := by
    intro h
    apply P.ne_top'
    apply SetLike.ext
    intro y
    constructor
    · intro _
      exact ValuationSubring.mem_top y
    · intro _
      have hy : (decompositionResidueAut A Γ d⁻¹).symm y ∈
          P.toValuationSubring.comap (decompositionResidueAut A Γ d⁻¹).toRingHom :=
        h ▸ ValuationSubring.mem_top _
      change decompositionResidueAut A Γ d⁻¹
        ((decompositionResidueAut A Γ d⁻¹).symm y) ∈ P.toValuationSubring at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
  isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective
    (decompositionResidueValuationEquiv A Γ d P).symm
    (decompositionResidueValuationEquiv A Γ d P).symm.surjective

theorem mem_decompositionResiduePlace_iff (d : A.decompositionSubgroup ℚ)
    (P : Place kk Fb) (f : Fb) :
    f ∈ (decompositionResiduePlace A Γ d P).toValuationSubring ↔
      decompositionResidueAut A Γ d⁻¹ f ∈ P.toValuationSubring := Iff.rfl

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction

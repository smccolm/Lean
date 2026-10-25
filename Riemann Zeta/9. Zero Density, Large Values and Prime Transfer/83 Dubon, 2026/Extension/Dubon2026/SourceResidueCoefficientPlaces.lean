import Dubon2026.SourceResidueCoefficientAutomorphism
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> original Frobenius/Picard comparison -> the arithmetic
Frobenius action on actual residue places. Restrict the literal coefficient
automorphism and transport its valuation rings. Native ring isomorphism
transport gives discreteness, and the nonunit criterion gives the exact
chart condition. No new general semilinear-action framework is required. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

/-- The valuation-ring isomorphism under inverse residue coefficient action. -/
def residueCoefficientValuationEquiv (e : K ≃+* K) (P : Place K FF) :
    P.toValuationSubring.comap (residueCoefficientRingAut N K e.symm).toRingHom ≃+*
      P.toValuationSubring where
  toFun f := ⟨residueCoefficientRingAut N K e.symm f.val, f.property⟩
  invFun f := ⟨(residueCoefficientRingAut N K e.symm).symm f.val, by
    change residueCoefficientRingAut N K e.symm
      ((residueCoefficientRingAut N K e.symm).symm f.val) ∈ P.toValuationSubring
    rw [RingEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((residueCoefficientRingAut N K e.symm).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((residueCoefficientRingAut N K e.symm).apply_symm_apply f.val)
  map_mul' f g := Subtype.ext (map_mul (residueCoefficientRingAut N K e.symm) f.val g.val)
  map_add' f g := Subtype.ext (map_add (residueCoefficientRingAut N K e.symm) f.val g.val)

/-- The actual residue place transported by inverse coefficient action. -/
def residueCoefficientPlace (e : K ≃+* K) (P : Place K FF) : Place K FF where
  toValuationSubring := P.toValuationSubring.comap (residueCoefficientRingAut N K e.symm).toRingHom
  algebraMap_mem' a := by
    change residueCoefficientRingAut N K e.symm (algebraMap K FF a) ∈ P.toValuationSubring
    rw [residueCoefficientRingAut_constants]
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
      have hy : (residueCoefficientRingAut N K e.symm).symm y ∈
          P.toValuationSubring.comap (residueCoefficientRingAut N K e.symm).toRingHom :=
        h ▸ ValuationSubring.mem_top _
      change residueCoefficientRingAut N K e.symm
        ((residueCoefficientRingAut N K e.symm).symm y) ∈ P.toValuationSubring at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
  isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective
    (residueCoefficientValuationEquiv N K e P).symm
    (residueCoefficientValuationEquiv N K e P).symm.surjective

theorem mem_residueCoefficientPlace_iff (e : K ≃+* K) (P : Place K FF) (f : FF) :
    f ∈ (residueCoefficientPlace N K e P).toValuationSubring ↔
      residueCoefficientRingAut N K e.symm f ∈ P.toValuationSubring := Iff.rfl

theorem nonunit_residueCoefficientPlace_iff (e : K ≃+* K) (P : Place K FF) (f : FF) :
    f ∈ (residueCoefficientPlace N K e P).toValuationSubring.nonunits ↔
      residueCoefficientRingAut N K e.symm f ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_residueCoefficientPlace_iff, map_inv₀]
  simp only [map_eq_zero]

theorem residueCoefficientPlace_j_mem (e : K ≃+* K) (P : Place K FF) :
    jCoeff N K ∈ (residueCoefficientPlace N K e P).toValuationSubring ↔
      jCoeff N K ∈ P.toValuationSubring := by
  rw [mem_residueCoefficientPlace_iff, residueCoefficientRingAut_j]

end
end Dubon2026.SourceFunctionField

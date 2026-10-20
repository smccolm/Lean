import Dubon2026.FiniteBaseCMSymmetricRealInvariants
import Dubon2026.FiniteBaseRealRestriction
import Dubon2026.ContinuousFiniteCohomologyVanishing
import Dubon2026.PolarizedContinuousFirstOrder

/-! The actual real absolute Galois restriction of the original polarized
CM symmetric power supplies the exact H0 dimension and vanishing of H1
and H2. These are the infinite-place obligations on DUB-17's source
polarized Selmer and deformation dimension chain. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the polarized symmetric-power consumer. -/
local instance finiteBaseCMSymmetricRealCohomologyUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {L : Type} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (hn : (n.factorial : L) ≠ 0) (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The actual original polarized CM symmetric power restricted through the original real absolute Galois embedding. -/
def finiteBaseCMSymmetricRealRepresentation : Gal(ℂ/ℝ) →ₜ* PolarizedGaloisGroup (Fin (n + 1)) L :=
  (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd).comp
    (finiteBaseRealArithmeticRestriction a F)

/-- The actual real absolute Galois invariant space has the source odd full-adjoint dimension. -/
theorem finiteBaseCMSymmetricRealRestriction_invariants_finrank (h2 : (2 : L) ≠ 0) :
    Module.finrank L (Representation.invariants (polarizedAdjointRepresentation.comp
      (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).toMonoidHom)) =
        (n + 1) * n / 2 := by
  let T := polarizedAdjointRepresentation.comp
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd).toMonoidHom
  let S := Subgroup.zpowers (finiteBaseRealConjugation a F)
  let γ : S := ⟨finiteBaseRealConjugation a F, Subgroup.mem_zpowers _⟩
  have hreal := representation_comp_invariants_eq_generator_ker T
    (finiteBaseRealArithmeticRestriction a F).toMonoidHom Complex.conjAe
    (finiteBaseRealArithmeticRestriction_generated a F)
  have hsub := representation_comp_invariants_eq_generator_ker T S.subtype γ (fun g => g.property)
  have he : Representation.invariants (polarizedAdjointRepresentation.comp
      (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).toMonoidHom) =
      Representation.invariants (T.comp S.subtype) := hreal.trans hsub.symm
  exact (LinearEquiv.ofEq _ _ he).finrank_eq.trans
    (finiteBaseCMSymmetricRealInvariants_finrank a F K n ρ hn hodd h2)

omit [Finite L] [TopologicalSpace L] [DiscreteTopology L] in
private theorem realGaloisCard_cast_ne_zero [Fintype Gal(ℂ/ℝ)] (h2 : (2 : L) ≠ 0) :
    (Fintype.card Gal(ℂ/ℝ) : L) ≠ 0 := by
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℝ ℂ := {}
  have hc : Fintype.card Gal(ℂ/ℝ) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]
  simpa only [hc, Nat.cast_ofNat] using h2

/-- Every actual continuous full-adjoint H1 class at the original real place is zero by native averaging. -/
theorem finiteBaseCMSymmetricRealH1_eq_zero (h2 : (2 : L) ≠ 0)
    (x : ContinuousRepresentationH1 (polarizedAdjointRep
      (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).toMonoidHom)
      (polarizedAdjointAction_continuous _
        (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).continuous)) : x = 0 := by
  letI : Fintype Gal(ℂ/ℝ) := Fintype.ofFinite _
  exact continuousFiniteH1_eq_zero _ _ (realGaloisCard_cast_ne_zero h2) x

/-- Every actual jointly continuous full-adjoint H2 class at the same original real place is zero by native averaging. -/
theorem finiteBaseCMSymmetricRealH2_eq_zero (h2 : (2 : L) ≠ 0)
    (x : ContinuousRepresentationH2 (polarizedAdjointRep
      (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).toMonoidHom)
      (polarizedAdjointAction_continuous _
        (finiteBaseCMSymmetricRealRepresentation a F K n ρ hn hodd).continuous)) : x = 0 := by
  letI : Fintype Gal(ℂ/ℝ) := Fintype.ofFinite _
  exact continuousFiniteH2_eq_zero _ _ (realGaloisCard_cast_ne_zero h2) x

end
end Dubon2026


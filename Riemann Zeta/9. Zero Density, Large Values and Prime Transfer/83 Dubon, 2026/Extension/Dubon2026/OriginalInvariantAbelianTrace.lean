import Dubon2026.OriginalSubgroupTraceEvaluation
import Dubon2026.OriginalTrivialDualHomologyNaturality
import Dubon2026.OriginalInvariantNormQuotientEquiv

/-! # Actual invariant norms and subgroup images in abelianization

The existing norm-quotient equivalence is read on literal invariant
coefficients. Its image on relative traces is exactly the subgroup image
in abelianization. These are the finite algebraic norm comparisons needed
for DUB-17's prescribed-support fixed-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G] (C : Rep.{0} ℤ G)
  (φ : groupCohomology.cocycles₂ C) (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (h : ∀ T : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 2))

/-- The existing actual norm-homology equivalence evaluated on a literal
invariant coefficient, with values in additive abelianization. -/
def originalInvariantAbelianMap : C.ρ.invariants →+ Additive (Abelianization G) :=
  (originalTrivialDualHomologyEquiv G).toAddMonoidHom.comp
    ((originalFundamentalHomologyLinear (Rep.trivial ℤ G ℤ) C φ p hG h).toAddMonoidHom.comp
      (originalTrivialSourceInvariantEquiv C).symm.toAddMonoidHom)

/-- The actual invariant map is the existing quotient equivalence after
the literal norm-quotient projection. -/
theorem originalInvariantAbelianMap_eq_quotient (x : C.ρ.invariants) :
    originalInvariantAbelianMap C φ p hG h x =
      originalInvariantNormAbelianEquiv C φ p hG h (Submodule.Quotient.mk x) := by
  rfl

/-- The kernel of the actual invariant map consists exactly of literal
original group norms. -/
theorem originalInvariantAbelianMap_eq_zero_iff (x : C.ρ.invariants) :
    originalInvariantAbelianMap C φ p hG h x = 0 ↔
      ∃ b : C, originalInvariantNormLinear C b = x := by
  rw [originalInvariantAbelianMap_eq_quotient, map_eq_zero_iff _
    (originalInvariantNormAbelianEquiv C φ p hG h).injective]
  exact Submodule.Quotient.mk_eq_zero _

variable (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- The literal quotient norm regarded as a full-group invariant. -/
def originalInvariantRelativeTrace (x : C.quotientToInvariants S) : C.ρ.invariants :=
  ⟨((C.quotientToInvariants S).ρ.norm x).val, originalSubgroup_trace_invariant S C x⟩

/-- The actual invariant abelianization map sends relative traces onto
exactly the image of the subgroup in the actual abelianization. -/
theorem originalInvariantAbelianMap_trace_range :
    Set.range (fun x : C.quotientToInvariants S =>
      originalInvariantAbelianMap C φ p hG h (originalInvariantRelativeTrace C S x)) =
      Set.range (Abelianization.map S.subtype).toAdditive := by
  let e := originalSubgroupTrivialSourceInvariantEquiv C S
  let M := Rep.trivial ℤ G ℤ
  let F := originalFundamentalHomologyLinear M C φ p hG h
  have he (x : ((Rep.ihom M).obj C).quotientToInvariants S) :
      originalInvariantAbelianMap C φ p hG h (originalInvariantRelativeTrace C S (e x)) =
        originalTrivialDualHomologyEquiv G (F (originalFundamentalSubgroupTraceMorphism M C S x)) := by
    have hx : (originalTrivialSourceInvariantEquiv C).symm
        (originalInvariantRelativeTrace C S (e x)) =
        originalFundamentalSubgroupTraceMorphism M C S x := by
      apply (originalTrivialSourceInvariantEquiv C).injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext (originalSubgroupTraceMorphism_eval C S x).symm
    change originalTrivialDualHomologyEquiv G (F _) = _
    exact congrArg (fun v => originalTrivialDualHomologyEquiv G (F v)) hx
  have hr := originalFundamentalHomology_subgroup_trace_range M C φ p hG h S
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hr ▸ (show F (originalFundamentalSubgroupTraceMorphism M C S (e.symm x)) ∈
      Set.range (fun v => F (originalFundamentalSubgroupTraceMorphism M C S v)) from ⟨e.symm x, rfl⟩)
    refine ⟨originalTrivialDualHomologyEquiv S y, ?_⟩
    rw [← originalTrivialDualHomologyEquiv_map]
    exact (congrArg (originalTrivialDualHomologyEquiv G) hy).trans
      ((he (e.symm x)).symm.trans (congrArg
        (fun v => originalInvariantAbelianMap C φ p hG h (originalInvariantRelativeTrace C S v))
          (e.apply_symm_apply x)))
  · rintro ⟨t, rfl⟩
    let y := (originalTrivialDualHomologyEquiv S).symm t
    obtain ⟨x, hx⟩ := hr.symm ▸ (show groupHomology.map S.subtype (𝟙 _) 1 y ∈
      Set.range (groupHomology.map S.subtype
        (𝟙 (Rep.res S.subtype ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)))) 1) from ⟨y, rfl⟩)
    refine ⟨e x, (he x).trans ((congrArg (originalTrivialDualHomologyEquiv G) hx).trans ?_)⟩
    rw [originalTrivialDualHomologyEquiv_map]
    exact congrArg (Abelianization.map S.subtype).toAdditive
      ((originalTrivialDualHomologyEquiv S).apply_symm_apply t)

end
end Dubon2026

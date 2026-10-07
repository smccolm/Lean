import Dubon2026.ModularRealProjective
import Dubon2026.FiniteCosetTrace

/-! # Genuine fundamental domains for finite congruence traces -/

namespace Dubon2026

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup MeasureTheory
open scoped MatrixGroups Pointwise ENNReal

noncomputable section

local instance integralSubgroupCosetsCountable (H : Subgroup SL(2, ℤ)) :
    Countable (SL(2, ℤ) ⧸ H) := Quotient.countable

/-- The projective image of an actual integral subgroup. -/
def projectiveIntegralSubgroup (H : Subgroup SL(2, ℤ)) : Subgroup PSL(2, ℤ) :=
  H.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Its faithful image in the actual real projective group. -/
def realProjectiveIntegralSubgroup (H : Subgroup SL(2, ℤ)) : Subgroup PGL(2, ℝ) :=
  (projectiveIntegralSubgroup H).map modularProjectiveEmbedding

/-- The literal integral-coset tiling, with no change to the coset multiplicities. -/
def integralSubgroupDomain (H : Subgroup SL(2, ℤ)) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ H, (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)

/-- Absorbing the center gives the exact integral-to-projective coset equivalence. -/
def integralProjectiveCosetEquiv (H : Subgroup SL(2, ℤ)) (hH : Subgroup.center SL(2, ℤ) ≤ H) :
    SL(2, ℤ) ⧸ H ≃ PSL(2, ℤ) ⧸ projectiveIntegralSubgroup H :=
  subgroupCosetEquiv (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) H
    (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hH)

/-- The equivalence uses the actual projected matrix representative. -/
theorem integralProjectiveCosetEquiv_out (H : Subgroup SL(2, ℤ))
    (hH : Subgroup.center SL(2, ℤ) ≤ H) (q : SL(2, ℤ) ⧸ H) :
    integralProjectiveCosetEquiv H hH q = QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
  conv_lhs => rw [← q.out_eq]
  rfl

/-- The actual integral tiling is a genuine fundamental domain for the projective subgroup. -/
theorem isFundamentalDomain_integralSubgroup (H : Subgroup SL(2, ℤ))
    (hH : Subgroup.center SL(2, ℤ) ≤ H) :
    IsFundamentalDomain (projectiveIntegralSubgroup H) (integralSubgroupDomain H) (volume : Measure ℍ) := by
  exact fundamentalDomain_iUnion_smul_of_transversal isFundamentalDomain_fdo_PSL
    (r := fun q : SL(2, ℤ) ⧸ H => (QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹)
    (integralProjectiveCosetEquiv H hH)
    (fun q => by simpa only [inv_inv] using integralProjectiveCosetEquiv_out H hH q)

/-- The same literal domain is a genuine domain for the faithful real projective subgroup. -/
theorem isFundamentalDomain_realIntegralSubgroup (H : Subgroup SL(2, ℤ))
    (hH : Subgroup.center SL(2, ℤ) ≤ H) :
    IsFundamentalDomain (realProjectiveIntegralSubgroup H) (integralSubgroupDomain H)
      (volume : Measure ℍ) := by
  have he : (Equiv.refl ℍ) '' integralSubgroupDomain H = integralSubgroupDomain H := by simp
  rw [← he]
  refine (isFundamentalDomain_integralSubgroup H hH).image_of_equiv (Equiv.refl ℍ)
    (Measure.QuasiMeasurePreserving.id _) ((Subgroup.equivMapOfInjective (projectiveIntegralSubgroup H)
      modularProjectiveEmbedding modularProjectiveEmbedding_injective).toEquiv.symm) ?_
  intro g z
  let e := Subgroup.equivMapOfInjective (projectiveIntegralSubgroup H)
    modularProjectiveEmbedding modularProjectiveEmbedding_injective
  have hv : (g : PGL(2, ℝ)) = modularProjectiveEmbedding (e.symm g : PSL(2, ℤ)) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (projectiveIntegralSubgroup H)
      modularProjectiveEmbedding modularProjectiveEmbedding_injective (e.symm g)]
    exact congrArg Subtype.val (e.apply_symm_apply g).symm
  change (e.symm g : PSL(2, ℤ)) • z = (g : PGL(2, ℝ)) • z
  rw [hv, modularProjectiveEmbedding_smul]

/-- Distinct actual inverse-coset tiles intersect only on hyperbolic null sets. -/
theorem integralSubgroupDomain_tiles_aedisjoint (H : Subgroup SL(2, ℤ))
    (hH : Subgroup.center SL(2, ℤ) ≤ H) :
    Pairwise (fun q r : SL(2, ℤ) ⧸ H => AEDisjoint (volume : Measure ℍ)
      ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) ((r.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q r hqr
  have hne : (QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ ≠
      (QuotientGroup.mk r.out : PSL(2, ℤ))⁻¹ := by
    intro he
    apply hqr
    apply (integralProjectiveCosetEquiv H hH).injective
    rw [integralProjectiveCosetEquiv_out, integralProjectiveCosetEquiv_out, inv_injective he]
  have hdisj := isFundamentalDomain_fdo_PSL.aedisjoint hne
  exact hdisj

/-- The actual finite trace integral is exactly the integral on the complete subgroup tiling. -/
theorem lintegral_finiteCosetTrace (H : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ H)]
    (hH : Subgroup.center SL(2, ℤ) ≤ H) (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in fdo, finiteCosetTrace H F z) = ∫⁻ z in integralSubgroupDomain H, F z := by
  simp only [finiteCosetTrace]
  rw [lintegral_finsetSum Finset.univ (f := fun q : SL(2, ℤ) ⧸ H => fun z => F (q.out⁻¹ • z))
    (fun q _ => hF.comp (measurable_const_smul _))]
  unfold integralSubgroupDomain
  rw [lintegral_iUnion₀ (fun q : SL(2, ℤ) ⧸ H =>
    isOpen_fdo.measurableSet.nullMeasurableSet.smul q.out⁻¹)
    (integralSubgroupDomain_tiles_aedisjoint H hH), tsum_fintype]
  apply Finset.sum_congr rfl
  intro q _
  exact (measurePreserving_smul q.out⁻¹ (volume : Measure ℍ)).setLIntegral_comp_emb
    (measurableEmbedding_const_smul _) F fdo

/-- Real projectivization agrees with directly mapping the integral matrices. -/
theorem realProjectiveIntegralSubgroup_eq_map (H : Subgroup SL(2, ℤ)) :
    realProjectiveIntegralSubgroup H = H.map slToRealProjective := by
  rw [realProjectiveIntegralSubgroup, projectiveIntegralSubgroup, Subgroup.map_map]
  rfl

end
end Dubon2026

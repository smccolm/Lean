import Dubon2026.AdelicProjectiveDomain

/-! # Genuine adelic arithmetic fundamental domains at every nonzero level -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Set MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Pointwise

/-- Almost every original adelic projective point has an actual rational arithmetic translate in the original level region. -/
theorem adelicProjectiveGamma0Domain_ae_covers (N : ℕ) [NeZero N] :
    ∀ᵐ p ∂adelicProjectiveMeasure, ∃ γ : adelicProjectiveArithmetic,
      γ • p ∈ adelicProjectiveGamma0Domain N := by
  have hall : ∀ᵐ q ∂realProjectiveMeasure, ∀ r : GL(2, ℚ)⁺,
      ∃ σ : projectiveGamma0 N,
        σ • ((rationalPositiveToAdelicProjective r).1⁻¹ * q) ∈ realProjectiveGamma0Domain N := by
    apply ae_all_iff.mpr
    intro r
    exact (measurePreserving_mul_left realProjectiveMeasure
      (rationalPositiveToAdelicProjective r).1⁻¹).quasiMeasurePreserving.ae
        (realProjectiveGamma0Domain_isFundamental N).ae_covers
  have hprod : ∀ᵐ p ∂adelicProjectiveMeasure, ∀ r : GL(2, ℚ)⁺,
      ∃ σ : projectiveGamma0 N,
        σ • ((rationalPositiveToAdelicProjective r).1⁻¹ * p.1) ∈ realProjectiveGamma0Domain N :=
    Measure.quasiMeasurePreserving_fst.ae hall
  filter_upwards [hprod] with p hp
  obtain ⟨r, u, hu⟩ := rationalProjectiveFinite_level_factorization N p.2
  obtain ⟨σ, hσ⟩ := hp r
  let ρ : adelicProjectiveArithmetic := ⟨rationalPositiveToAdelicProjective r, ⟨r, rfl⟩⟩
  refine ⟨integralProjectiveLevelToArithmetic N σ * ρ⁻¹, ?_, ?_⟩
  · change integralToRealPSL σ.val * ((rationalPositiveToAdelicProjective r).1⁻¹ * p.1) ∈
      realProjectiveGamma0Domain N at hσ
    change (integralToRealPSL σ.val * (rationalPositiveToAdelicProjective r).1⁻¹) * p.1 ∈ _
    rwa [mul_assoc]
  · change ((integralProjectiveLevelToArithmetic N σ).val.2 *
      (rationalPositiveToAdelicProjective r).2⁻¹) * p.2 ∈ finiteProjectiveGL2Level N
    rw [hu, mul_assoc, inv_mul_cancel_left]
    exact (finiteProjectiveGL2Level N).mul_mem
      (integralProjectiveLevelToArithmetic_finite_level N σ) u.property

/-- Distinct actual rational arithmetic translates of the original adelic region have null overlap. -/
theorem adelicProjectiveGamma0Domain_aedisjoint (N : ℕ) [NeZero N]
    (γ : adelicProjectiveArithmetic) (hγ : γ ≠ 1) :
    AEDisjoint adelicProjectiveMeasure (γ • adelicProjectiveGamma0Domain N)
      (adelicProjectiveGamma0Domain N) := by
  by_cases hlevel : γ.val.2 ∈ finiteProjectiveGL2Level N
  · obtain ⟨σ, hσ⟩ := (adelicProjectiveArithmetic_level_iff N γ).mp hlevel
    let τ : projectiveGamma0 N := ⟨QuotientGroup.mk σ.val, ⟨σ.val, σ.property, rfl⟩⟩
    have hτ : τ ≠ 1 := by
      intro he
      apply hγ
      apply Subtype.ext
      rw [← hσ]
      have hv := congrArg Subtype.val he
      change (QuotientGroup.mk σ.val : PSL(2, ℤ)) = 1 at hv
      rw [hv, map_one]
      rfl
    have hd : AEDisjoint realProjectiveMeasure (τ • realProjectiveGamma0Domain N)
        (realProjectiveGamma0Domain N) := by
      simpa only [Function.onFun, one_smul] using (realProjectiveGamma0Domain_isFundamental N).aedisjoint hτ
    have hp : AEDisjoint adelicProjectiveMeasure
        (Prod.fst ⁻¹' (τ • realProjectiveGamma0Domain N))
        (Prod.fst ⁻¹' realProjectiveGamma0Domain N) :=
      hd.preimage Measure.quasiMeasurePreserving_fst
    apply hp.mono
    · rintro p ⟨q, hq, rfl⟩
      refine ⟨q.1, hq.1, ?_⟩
      change integralToRealPSL (QuotientGroup.mk σ.val) * q.1 = γ.val.1 * q.1
      exact congrArg (fun a : AdelicProjectiveGroup => a.1 * q.1) hσ
    · exact fun _ hp => hp.1
  · apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    rintro p ⟨q, hq, rfl⟩ hp
    apply hlevel
    have hm : γ.val.2 * q.2 ∈ finiteProjectiveGL2Level N := hp.2
    have he := (finiteProjectiveGL2Level N).mul_mem hm
      ((finiteProjectiveGL2Level N).inv_mem hq.2)
    simpa only [mul_inv_cancel_right] using he

/-- The literal real Gamma0 domain times the literal compact finite level is an actual fundamental domain for the whole original rational projective arithmetic group. -/
theorem adelicProjectiveGamma0Domain_isFundamental (N : ℕ) [NeZero N] :
    IsFundamentalDomain adelicProjectiveArithmetic (adelicProjectiveGamma0Domain N)
      adelicProjectiveMeasure := by
  apply IsFundamentalDomain.mk'' (adelicProjectiveGamma0Domain_isOpen N).measurableSet.nullMeasurableSet
    (adelicProjectiveGamma0Domain_ae_covers N) (adelicProjectiveGamma0Domain_aedisjoint N)
  intro γ
  exact (measurePreserving_mul_left adelicProjectiveMeasure γ.val).quasiMeasurePreserving

/-- The original full-level product region is genuinely an arithmetic fundamental domain. -/
theorem adelicProjectiveBaseRegion_isFundamental :
    IsFundamentalDomain adelicProjectiveArithmetic adelicProjectiveBaseRegion
      adelicProjectiveMeasure :=
  adelicProjectiveGamma0Domain_isFundamental 1

end
end Dubon2026

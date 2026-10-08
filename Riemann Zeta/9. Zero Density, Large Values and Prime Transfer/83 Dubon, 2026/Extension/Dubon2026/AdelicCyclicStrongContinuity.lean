import Dubon2026.AdelicCyclicParameterContinuity

/-! # Strong continuity of the genuine full adelic action on the original cyclic L2 space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology

/-- The actual original full adelic cyclic representation is strongly continuous for its genuine quotient L2 norm. -/
theorem adelicLiftCyclic_stronglyContinuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    Continuous (fun h : RationalAdelicGL2 => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation h v)) := by
  letI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  letI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  letI : FirstCountableTopology (GeneralLinearGroup (Fin 2) ℝ) :=
    Units.isInducing_embedProduct.firstCountableTopology
  obtain ⟨K, _, hKo, hK⟩ := adelicLiftCyclic_finite_smooth N f v.property
  apply continuous_iff_continuousAt.mpr
  intro h₀
  let ψ : GeneralLinearGroup (Fin 2) ℝ → RationalAdelicGL2 := fun r =>
    rationalAdelicGL2RealFiniteEquiv.symm (r, (rationalAdelicGL2RealFiniteEquiv h₀).2)
  have hψ : Continuous ψ := rationalAdelicGL2RealFiniteEquiv_symm_continuous.comp
    (continuous_id.prodMk continuous_const)
  have hc := (adelicLiftCyclic_parameter_stronglyContinuous N f v ψ hψ).comp
    (continuous_fst.comp rationalAdelicGL2RealFiniteEquiv_continuous)
  have hU : {h : RationalAdelicGL2 | (rationalAdelicGL2RealFiniteEquiv h₀).2⁻¹ *
      (rationalAdelicGL2RealFiniteEquiv h).2 ∈ K} ∈ 𝓝 h₀ := by
    apply (hKo.preimage (continuous_const.mul
      (continuous_snd.comp rationalAdelicGL2RealFiniteEquiv_continuous))).mem_nhds
    change (rationalAdelicGL2RealFiniteEquiv h₀).2⁻¹ *
      (rationalAdelicGL2RealFiniteEquiv h₀).2 ∈ K
    simpa only [inv_mul_cancel] using K.one_mem
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hU] with h hh
  apply congrArg (adelicProjectiveCyclicToL2 N f)
  apply Subtype.ext
  funext g
  have he : h = ψ (rationalAdelicGL2RealFiniteEquiv h).1 * rationalAdelicFiniteGL2Embedding
      ((rationalAdelicGL2RealFiniteEquiv h₀).2⁻¹ * (rationalAdelicGL2RealFiniteEquiv h).2) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [map_mul, rationalAdelicFiniteGL2Embedding_coordinates]
    dsimp only [ψ]
    rw [MulEquiv.apply_symm_apply]
    ext <;> simp
  change v.val (g * h) = v.val (g * ψ (rationalAdelicGL2RealFiniteEquiv h).1)
  conv_lhs => rw [he, ← mul_assoc]
  exact hK _ _ hh

end
end Dubon2026

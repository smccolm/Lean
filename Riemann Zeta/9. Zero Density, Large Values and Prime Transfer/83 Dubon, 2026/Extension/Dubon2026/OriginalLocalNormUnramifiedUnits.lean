import Dubon2026.OriginalLocalNormUnitProducts
import Dubon2026.LocalIntegerUnitFixedUniformizerNorm
import Dubon2026.SupportedOutsideUnramifiedVanishing

/-! # Original finite-local integer units are norms away from ramification

The existing original integer uniformizer and local cyclic H2 vanishing
supply invariant integer-unit norm preimages. The actual decomposition
action and local norm product identify these with the original completed
field norm. This discharges the outside-support unit condition in
DUB-17's prime-degree norm-index upper-bound chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical WithZero
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Every original base integer unit is an actual local norm at an absolutely unramified upper prime. -/
theorem originalFiniteLocalNorm_integerUnit_of_unramified
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (u : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ)
    (hu : u ∈ ((originalFinitePrimeBelow K L w).adicCompletionIntegers K).units) :
    u ∈ (originalFiniteLocalNorm K L w).range := by
  letI := originalFinitePrimeBelow_liesOver K L w
  let H := OriginalFiniteDecompositionGroup K L w
  let F := w.adicCompletion L
  letI := originalAdicDecompositionAction K L w
  haveI : FaithfulSMul H F := originalAdicDecompositionAction_faithful K L w
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F ℤᵐ⁰
  haveI : ProperSpace F := original_adicCompletion_properSpace L w
  have hn (σ : H) (x : F) : ‖σ • x‖ = ‖x‖ := by
    change ‖numberFieldGaloisLocalTransport K L σ.val w w σ.property x‖ = ‖x‖
    simp only [Valued.toNormedField.norm_def]
    rw [(Valued.v.restrict_inj).mpr (numberFieldGaloisLocalTransport_valuation K L σ.val w w σ.property x)]
  let E := FixedPoints.subfield H F
  letI : NontriviallyNormedField E := {
    toNormedField := inferInstance
    non_trivial := normPreserving_fixedField_exists_norm_gt_one H F hn }
  haveI : LocallyCompactSpace E := (normPreserving_fixedField_isClosed H F hn).locallyCompactSpace
  letI : NormedAlgebra E F := {
    toAlgebra := inferInstance
    norm_smul_le := fun a b => (norm_mul (a : F) b).le }
  let e := FixedPoints.toAlgAutMulEquiv H F
  haveI : IsCyclic Gal(F/E) := isCyclic_of_surjective e.toMonoidHom e.surjective
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField E := normValuation_isNonarchimedeanLocalField E
  haveI : IsNonarchimedeanLocalField F := normValuation_isNonarchimedeanLocalField F
  haveI := normedFieldValuation_hasExtension E F
  haveI : Algebra.IsUnramifiedAt ℤ w.asIdeal := hw
  obtain ⟨r, hr⟩ := original_unramified_exists_completion_integer_uniformizer L w
  have hr0 : (r : F) ≠ 0 := by
    intro h
    have hz : (0 : ℤᵐ⁰) = WithZero.exp (-1 : ℤ) := by simpa only [h, map_zero] using hr
    exact WithZero.exp_ne_zero hz.symm
  let π : Fˣ := Units.mk0 (r : F) hr0
  have hp : localFieldUnitOrder F (Additive.ofMul π) = 1 := originalAdicUnitOrder_of_uniformizer L w π hr
  have hfixed : ∀ σ : Gal(F/E), Units.map σ.toMonoidHom π = π := by
    intro σ
    apply Units.ext
    exact map_intCast σ r
  letI := localFieldIntegerUnitMulDistribMulAction E F
  let B := Rep.ofMulDistribMulAction Gal(F/E) (ValuativeRel.valuation F).integerˣ
  let f := originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w
  have hb (a : ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ)
      (ha : a ∈ ((originalFinitePrimeBelow K L w).adicCompletionIntegers K).units) :
      f a.val ∈ (ValuativeRel.valuation F).integer := by
    apply (normValuativeInteger_mem_iff F _).mpr
    apply Valued.toNormedField.norm_le_one_iff.mpr
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at ha
    change Valued.v (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w a.val) ≤ 1
    rw [originalAdicBaseChangeMap_valuation, ha, one_pow]
  let x : (ValuativeRel.valuation F).integerˣ := {
    val := ⟨f u.val, hb u hu⟩
    inv := ⟨f (u⁻¹).val, hb u⁻¹ (inv_mem hu)⟩
    val_inv := by apply Subtype.ext; exact (map_mul f u.val (u⁻¹).val).symm.trans (by simp)
    inv_val := by apply Subtype.ext; exact (map_mul f (u⁻¹).val u.val).symm.trans (by simp) }
  have hx : (Additive.ofMul x : B) ∈ B.ρ.invariants := by
    intro σ
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    change algebraMap (ValuativeRel.valuation F).integer F (localFieldIntegerGaloisEquiv E F σ x.val) = f u.val
    rw [localFieldIntegerGaloisEquiv_apply]
    obtain ⟨τ, rfl⟩ := e.surjective σ
    exact originalAdicBaseChangeMap_fixed K L (originalFinitePrimeBelow K L w) w τ.val τ.property u.val
  obtain ⟨y, hy⟩ := localIntegerUnit_norm_preimages_of_fixed_uniformizer E F π hfixed hp (Additive.ofMul x) hx
  let yUnit : (ValuativeRel.valuation F).integerˣ := Additive.toMul (Rep.toAdditive y)
  let b : Fˣ := Units.map (algebraMap (ValuativeRel.valuation F).integer F).toMonoidHom yUnit
  refine ⟨b, ?_⟩
  apply Units.ext
  apply f.injective
  have hnorm := congrArg Units.val (originalFiniteLocalNorm_baseChange K L w b)
  change f (↑(originalFiniteLocalNorm K L w b)) = _ at hnorm
  rw [hnorm, Units.coe_prod]
  have hprod : ∏ σ : Gal(F/E), σ (yUnit.val : F) = f u.val := by
    have h := (Representation.norm_ofMulDistribMulAction_eq (G := Gal(F/E)) (M := (ValuativeRel.valuation F).integerˣ) (Additive.ofMul yUnit)).symm.trans
      (congrArg Additive.toMul hy)
    have hh := congrArg (fun z : (ValuativeRel.valuation F).integerˣ => (z.val : F)) h
    change algebraMap (ValuativeRel.valuation F).integer F
      ((∏ σ : Gal(F/E), σ • yUnit).val) = f u.val at hh
    rw [Units.coe_prod, map_prod] at hh
    change (∏ σ : Gal(F/E), algebraMap (ValuativeRel.valuation F).integer F
      (localFieldIntegerGaloisEquiv E F σ yUnit.val)) = f u.val at hh
    simpa only [localFieldIntegerGaloisEquiv_apply] using hh
  calc
    (∏ τ : H, ↑(Units.map (numberFieldGaloisLocalTransport K L τ.val w w τ.property).toMonoidHom b)) =
        ∏ σ : Gal(F/E), σ (yUnit.val : F) :=
      Fintype.prod_equiv e.toEquiv _ _ (fun _ => rfl)
    _ = f u.val := hprod

end
end Dubon2026

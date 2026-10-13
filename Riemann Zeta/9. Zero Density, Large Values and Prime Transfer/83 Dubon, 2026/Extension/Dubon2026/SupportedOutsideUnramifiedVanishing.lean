import Dubon2026.SupportedOutsideOrbitFieldAction
import Dubon2026.LocalIntegerUnitFixedUniformizerVanishing
import Dubon2026.FaithfulLocalFieldSecondCohomology

/-! # Actual outside-support stabilizer cohomology vanishes at unramified places

The original integer uniformizer is fixed by the original stabilizer.
The actual fixed-field extension and identity-on-values integer-ring
comparison transfer the proved local vanishing to the exact existing
outside-support representation. This discharges its H1/H2 inputs to
DUB-17's idele Herbrand formula without another completion model.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical WithZero
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The exact original outside-support point H1 and H2 vanish when its actual place is absolutely unramified. -/
theorem supportedOutsideOrbitPoint_first_second_zero_of_unramified :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω hw
  let w := ω.out.val
  let H := MulAction.stabilizer Gal(L/K)
    (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)
  let F := w.adicCompletion L
  letI := supportedOutsideOrbitFieldAction K L S hS ω
  haveI : FaithfulSMul H F := supportedOutsideOrbitField_faithful K L S hS ω
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F ℤᵐ⁰
  haveI : ProperSpace F := original_adicCompletion_properSpace L w
  have hn (σ : H) (x : F) : ‖σ • x‖ = ‖x‖ := supportedOutsideOrbitField_norm K L S hS ω σ x
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
  have hp : localFieldUnitOrder F (Additive.ofMul π) = 1 :=
    originalAdicUnitOrder_of_uniformizer L w π hr
  have hfixed : ∀ σ : Gal(F/E), Units.map σ.toMonoidHom π = π := by
    intro σ
    apply Units.ext
    exact map_intCast σ r
  letI := localFieldIntegerUnitMulDistribMulAction E F
  let B := Rep.ofMulDistribMulAction Gal(F/E) (ValuativeRel.valuation F).integerˣ
  let A := supportedOutsideOrbitPointRep K L S hS ω
  let c : Rep.res e.toMonoidHom B ≅ A := by
    apply Rep.mkIso
    refine Representation.Equiv.mk
      ((Units.mapEquiv (originalAdicIntegerNormEquiv L w).symm.toMulEquiv).toAdditive.toIntLinearEquiv) ?_
    intro σ
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    exact localFieldIntegerGaloisEquiv_apply E F (e σ) x.toMul.val
  have hz := localIntegerUnit_first_second_zero_of_fixed_uniformizer E F π hfixed hp
  let co (n : ℕ) : groupCohomology B n ≅ groupCohomology A n :=
    originalCohomologyReindex B e n ≪≫ (groupCohomology.functor ℤ H n).mapIso c
  exact ⟨Limits.IsZero.of_iso hz.1 (co 1).symm, Limits.IsZero.of_iso hz.2 (co 2).symm⟩

end
end Dubon2026

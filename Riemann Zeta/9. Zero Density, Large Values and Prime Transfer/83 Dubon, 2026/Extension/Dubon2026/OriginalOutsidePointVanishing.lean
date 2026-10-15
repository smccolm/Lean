import Dubon2026.OriginalProductH1Detection
import Dubon2026.OriginalSupportedOutsideFieldAction
import Dubon2026.OriginalUnramifiedDecompositionCyclic
import Dubon2026.LocalIntegerUnitFixedUniformizerVanishing
import Dubon2026.FaithfulLocalFieldSecondCohomology

/-! # Original outside-support H1 and H2 vanishing for finite Galois extensions

Only the actual unramified decomposition group must be cyclic; its cyclicity
is proved from the original residue action. The existing fixed-uniformizer
local theorem then kills each factor, and the direct product H2 argument
kills the original outside-support coefficient. Degree-one vanishing
also supplies invariant class-quotient descent on DUB-17's class-formation
and original localization-duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical WithZero
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The original outside-support stabilizer H1 and H2 vanish at an absolutely unramified place, with no cyclic global-group assumption. -/
theorem originalOutsideOrbitPoint_first_second_zero_of_unramified :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (originalOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (originalOutsideOrbitPointRep K L S hS ω) 2) := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω hw
  let w := ω.out.val
  let H := MulAction.stabilizer Gal(L/K)
    (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)
  let f : H →* OriginalFiniteDecompositionGroup K L w := {
    toFun := fun σ => ⟨σ.val, by
      change numberFieldGaloisPlaceEquiv K L σ.val w = w
      exact congrArg (fun z : ω.orbit => z.val.val) σ.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun z : OriginalFiniteDecompositionGroup K L w => z.val) h)
  haveI : IsCyclic (OriginalFiniteDecompositionGroup K L w) :=
    originalFiniteDecomposition_isCyclic_of_unramified K L w hw
  haveI : IsCyclic H := isCyclic_of_injective f hf
  let F := w.adicCompletion L
  letI := originalOutsideOrbitFieldAction K L S hS ω
  haveI : FaithfulSMul H F := originalOutsideOrbitField_faithful K L S hS ω
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F ℤᵐ⁰
  haveI : ProperSpace F := original_adicCompletion_properSpace L w
  have hn (σ : H) (x : F) : ‖σ • x‖ = ‖x‖ := originalOutsideOrbitField_norm K L S hS ω σ x
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
  let A := originalOutsideOrbitPointRep K L S hS ω
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

/-- The actual outside-unit H1 vanishes at the original absolutely unramified support. -/
theorem originalOutsideUnit_first_zero_of_unramified
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) 1) := by
  letI := supportedOutsidePlaceAction K L S hS
  apply originalTransported_first_zero_of_stabilizers ℤ Gal(L/K)
    {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS)
  intro ω
  exact (originalOutsideOrbitPoint_first_second_zero_of_unramified K L S hS ω
    (hu ω.out.val ω.out.property)).1

end
end Dubon2026

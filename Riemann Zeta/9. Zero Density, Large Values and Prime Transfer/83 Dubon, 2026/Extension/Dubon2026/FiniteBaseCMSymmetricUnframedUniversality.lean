import Dubon2026.FiniteBaseCMSymmetricFullTraceDescent
import Dubon2026.PolarizedTraceUnframedCriterion
import Dubon2026.FiniteBasePolarizedUniversality
import Dubon2026.OriginalPolarizedUnframedNaturality

/-! The actual original CM trace ring represents the full polarized
unframed deformation classes. The source local crystalline conditions
and automorphic comparison on DUB-17 remain separate obligations. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricUnframedUniversalityUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) (IsLocalRing.ResidueField O))
  (hn : (n.factorial : IsLocalRing.ResidueField O) ≠ 0)
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hνk : ∀ g : FiniteBaseCMKernel a F K,
    (GeneralLinearGroup.det (ρ g.val)) ^ n =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g.val))
  (hνc : ν (finiteBaseRealConjugation a F) = -1)

variable [IsNoetherianRing O] (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)

variable [CharP (IsLocalRing.ResidueField O) p]
  (hq : 3 < p) (hsize : 2 * n < Nat.card (IsLocalRing.ResidueField O) - 1) (hchar : n < p)
  (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := IsLocalRing.ResidueField O)).range ≤ ρ.toMonoidHom.range)

include hq hsize hchar himage in
/-- The actual original universal CM trace algebra is complete local and
Noetherian and classifies all original continuous unframed polarized lifts
with the source fixed similitude over every complete Noetherian local target.
Full trace descent and framed universality are derived from the original
arithmetic residual input, rather than supplied as certificates. -/
theorem finiteBaseCMSymmetricTrace_unframedUniversality :
    (let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     let σ := finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd
     ∃ hlocal : IsLocalRing T,
       letI := hlocal
       IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
       ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (τ : finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup (Fin (n + 1)) T)
         (hτres : (polarizedCoefficientMap (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom = σ.toMonoidHom)
         (hτν : ∀ g, polarizedSimilitude (τ g) = Units.map (algebraMap O T).toMonoidHom (ν g)),
         ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
           [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
           (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
           (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
           Function.Bijective (originalPolarizedCoefficientClass eT eA
             (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom ν τ hτres hτν) ∧
           ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]
             (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
             (k : A →ₐ[O] B) (hk : Continuous k)
             (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
             (f : OriginalContinuousCoefficientFiber eT eA),
             originalPolarizedCoefficientClass eT eB (finiteBaseArithmeticGaloisGroup a F)
                 σ.toMonoidHom ν τ hτres hτν (originalCoefficientFiberPostcomp eT eA eB k hk hres f) =
               originalPolarizedUnframedPostcomp eA eB (finiteBaseArithmeticGaloisGroup a F)
                 σ.toMonoidHom ν k hk hres
                 (originalPolarizedCoefficientClass eT eA (finiteBaseArithmeticGaloisGroup a F)
                   σ.toMonoidHom ν τ hτres hτν f)) := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let σ := finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd
  let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let T := closedMatrixTraceAlgebra (O := O) r
  let υ := finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, W, hW, he, hχ, hν, hres⟩ :=
    finiteBaseCMSymmetricUniversal_full_traceDescent a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage
  letI : IsLocalRing T := hlocal
  have hτres : (polarizedCoefficientMap (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom = σ.toMonoidHom :=
    MonoidHom.ext hres
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτres, hν, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  constructor
  · have hAtop : IsAdic (IsLocalRing.maximalIdeal A) := by rw [← hA]; rfl
    letI : T2Space A := originalAdicCompleteLocal_t2Space hAtop
    have hcR (g : FiniteBaseCMKernel a F K) : polarizedComponent (υ g.val) = 1 :=
      (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
        ha p hp hpa g.val).1.trans g.property
    have hcT (g : FiniteBaseCMKernel a F K) : polarizedComponent (τ g.val) = 1 := (hχ g.val).trans g.property
    have hdesc : PolarizedStrictlyConjugate (localCoefficientReduction eQ).toRingHom
        ((polarizedCoefficientMap T.val.toRingHom).comp τ.toMonoidHom) υ.toMonoidHom := by
      refine ⟨W, ?_, he⟩
      change GeneralLinearGroup.map eQ.toRingHom (GeneralLinearGroup.map (IsLocalRing.residue Q) W) = 1
      rw [hW, map_one]
    apply polarizedTraceUnframed_bijective_of_framed r eQ eT eA (finiteBaseArithmeticGaloisGroup a F)
      (FiniteBaseCMKernel a F K).subtype σ.toMonoidHom ν υ τ hτres hν hcR hcT rfl
      (finiteBaseCMSymmetricTrace_reduction_compatibility a F K n ρ hn hodd ν hνk hνc ha p hp hpa hlocal eT)
      hdesc
    intro ω
    let E := finiteBasePolarizedFiberEquiv a F ha p hp hpa σ ν
      (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc) hA eA
    let f := E.symm ω
    refine ⟨f, ?_⟩
    apply MonoidHom.ext
    intro g
    have hv := finiteBasePolarizedFiberEquiv_evaluation a F ha p hp hpa σ ν
      (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc) hA eA f g
    have hinv := congrArg (fun z : OriginalContinuousPolarizedFiber eA (finiteBaseArithmeticGaloisGroup a F)
      σ.toMonoidHom ν => z.val g) (E.apply_symm_apply ω)
    change polarizedCoefficientMap f.val.toRingHom (υ g) = ω.val g
    unfold υ finiteBaseCMSymmetricUniversalRepresentation
    exact hv.symm.trans hinv
  · intro B _ _ _ _ eB k hk hres f
    exact originalPolarizedCoefficientClass_natural eA eB (finiteBaseArithmeticGaloisGroup a F)
      σ.toMonoidHom ν k hk hres eT τ hτres hν f

end
end Dubon2026


import Dubon2026.FiniteBaseCMSymmetricTraceSymmetry
import Dubon2026.FiniteBaseCMPolarizationFromDuality

/-! Construct the whole polarized arithmetic representation over the actual
CM trace ring. This supplies the symmetric-form and full-group existence
steps in the DUB-17 trace descent; strict comparison remains separate. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTracePolarizationUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The original universal CM trace ring supports an actual continuous
polarized arithmetic representation, with its derived symmetric form,
original CM matrix descent, quadratic component and base similitude. -/
theorem finiteBaseCMSymmetricUniversal_tracePolarization_exists :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
     let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     let νT := (Units.map (algebraMap O T).toMonoidHom).comp ν
     ∃ hlocal : IsLocalRing T,
       letI := hlocal
       IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
       ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1)) T)
         (B : GeneralLinearGroup (Fin (n + 1)) T)
         (σT : finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup (Fin (n + 1)) T),
         (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom =
           (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom ∧
         MatrixStrictlyConjugate (IsLocalRing.residue Q)
           ((GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom) r.toMonoidHom ∧
         GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom B =
           symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)) ∧
         (∀ g, τ (finiteBaseCMConjugation a F K g) =
           B * polarizedTwistedDual τ.toMonoidHom (νT.comp (FiniteBaseCMKernel a F K).subtype) g * B⁻¹) ∧
         B.val.transpose = B.val ∧
         (∀ g : FiniteBaseCMKernel a F K, σT g.val = polarizedIdentityComponent (τ g, νT g.val)) ∧
         σT (finiteBaseRealConjugation a F) = polarizedInvolution B ∧
         (∀ g, polarizedComponent (σT g) = finiteBaseQuadraticComponent a F K g) ∧
         (∀ g, polarizedSimilitude (σT g) = νT g)) := by
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, B, hτred, hτ, hBred, hB⟩ :=
    finiteBaseCMSymmetricUniversal_traceIntertwiner_exists a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  letI : Finite (IsLocalRing.ResidueField T) := Finite.of_injective eT eT.injective
  letI : CompactSpace T := originalAdicCompleteLocal_compactSpace htop
  letI : T2Space T := originalAdicCompleteLocal_t2Space htop
  have hsym := finiteBaseCMSymmetricTrace_intertwiner_symmetric a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa hq hsize hchar himage τ B hτ hB
  have hd := finiteBaseCMSymmetricUniversal_traceDuality a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa τ hτ
  let νT := (Units.map (algebraMap O T).toMonoidHom).comp ν
  have hνTc : νT (finiteBaseRealConjugation a F) = -1 := by
    change Units.map (algebraMap O T).toMonoidHom (ν (finiteBaseRealConjugation a F)) = -1
    rw [hνc]
    apply Units.ext
    change algebraMap O T (-1) = -1
    simp only [map_neg, map_one]
  obtain ⟨σT, hk, hc, hχ, hν⟩ := finiteBaseCM_polarized_of_duality a F K τ νT hd.1 hνTc B hsym hB
  exact ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, B, σT, hτred, hτ, hBred, hB, hsym, hk, hc, hχ, hν⟩

end
end Dubon2026


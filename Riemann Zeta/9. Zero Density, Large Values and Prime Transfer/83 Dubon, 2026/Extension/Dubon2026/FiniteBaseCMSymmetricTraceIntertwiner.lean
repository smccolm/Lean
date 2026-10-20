import Dubon2026.FiniteBaseCMSymmetricTraceDescentData
import Dubon2026.FiniteBaseCMSymmetricTraceDuality
import Dubon2026.FiniteBaseCMSymmetricResidualDuality
import Dubon2026.FiniteBaseCMPolarizationIntertwiner

/-! Construct the original CM conjugate-duality matrix over the actual
complete local trace ring, with the original residual polarization. This
closes the intertwiner-existence step in DUB-17; symmetry and full
polarized strict equivalence are subsequent obligations. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricTraceIntertwinerUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The actual universal CM trace ring has continuous descended matrices
and an original conjugate-duality matrix reducing to the original residual
polarization. Its complete local data, traces and residual duality are all
derived from the original arithmetic polarized representation. -/
theorem finiteBaseCMSymmetricUniversal_traceIntertwiner_exists :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
     let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     let μ := ((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
       (FiniteBaseCMKernel a F K).subtype
     ∃ hlocal : IsLocalRing T,
       letI := hlocal
       IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
       ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (τ : FiniteBaseCMKernel a F K →ₜ* GeneralLinearGroup (Fin (n + 1)) T)
         (B : GeneralLinearGroup (Fin (n + 1)) T),
         (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp τ.toMonoidHom =
           (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom ∧
         MatrixStrictlyConjugate (IsLocalRing.residue Q)
           ((GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom) r.toMonoidHom ∧
         GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom B =
           symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)) ∧
         ∀ g, τ (finiteBaseCMConjugation a F K g) =
           B * polarizedTwistedDual τ.toMonoidHom μ g * B⁻¹) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, _hcompat, hτred, hτ⟩ :=
    finiteBaseCMSymmetricUniversal_traceDescentData a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage
  letI : IsLocalRing T := hlocal
  letI : IsNoetherianRing T := hnoeth
  letI : IsTopologicalRing T := inferInstanceAs (IsTopologicalRing T.toSubring)
  letI : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
  have hd := finiteBaseCMSymmetricUniversal_traceDuality a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa τ hτ
  let μ : finiteBaseCMProfiniteGroup a F K →ₜ* Tˣ :=
    ⟨((Units.map (algebraMap O T).toMonoidHom).comp ν).comp
      (FiniteBaseCMKernel a F K).subtype, hd.1⟩
  let σ : finiteBaseCMProfiniteGroup a F K →* GeneralLinearGroup (Fin (n + 1))
      (IsLocalRing.ResidueField O) :=
    (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom
  have hσ : Continuous σ := continuous_fst.comp (finiteBaseCMSymmetricMatrices a F K n ρ).continuous
  have hirr : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ)) :=
    finiteBaseCMSymmetricMatrices_absoluteIrreducible a F K p n ρ himage hq hsize hchar
  have hμ : (Units.map (localCoefficientReduction eT).toMonoidHom).comp μ.toMonoidHom =
      ((Units.map (algebraMap O (IsLocalRing.ResidueField O)).toMonoidHom).comp ν).comp
        (FiniteBaseCMKernel a F K).subtype := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact (localCoefficientReduction eT).commutes (ν g.val : O)
  have hbar : σ.comp (finiteBaseCMConjugation a F K).toMonoidHom =
      matrixRepresentationConjugate (polarizedTwistedDual σ
        ((Units.map (localCoefficientReduction eT).toMonoidHom).comp μ.toMonoidHom))
        (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) := by
    rw [hμ]
    exact finiteBaseCMSymmetricResidual_duality a F K n ρ hn ν hνk
  obtain ⟨B, hB, hpol⟩ := finiteBaseCM_polarizationIntertwiner_exists
    (L := AlgebraicClosure (IsLocalRing.ResidueField O)) (hσirr := hirr)
    a F K ha p hp hpa htop eT σ hσ τ μ hτred
    (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) hbar hd.2 0
  exact ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, B, hτred, hτ, hB, hpol⟩

end
end Dubon2026


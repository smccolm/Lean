import Dubon2026.FiniteBaseCMSymmetricTracePolarization
import Dubon2026.FiniteBaseCMSymmetricStrictAlignment
import Dubon2026.FiniteBaseCMPolarizedAlignment
import Dubon2026.PolarizedCoefficientConjugacy

/-! Whole polarized descent of the original universal representation over
its actual CM trace ring. This discharges full strict descent in DUB-17;
unframed universality, source crystalline conditions and automorphy are
separate remaining obligations. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the symmetric-power deformation consumer. -/
local instance finiteBaseCMSymmetricFullTraceDescentUnionAlgebra (a : 𝓞 ℚ) :
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
/-- The original universal polarized arithmetic representation is strictly
conjugate to an actual continuous representation over its own complete
local CM trace algebra, with its exact component and prescribed similitude. -/
theorem finiteBaseCMSymmetricUniversal_full_traceDescent :
    (letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
     let r := finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa
     let T := closedMatrixTraceAlgebra (O := O) r.toMonoidHom
     ∃ hlocal : IsLocalRing T,
       letI := hlocal
       IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
       ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
         (σT : finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup (Fin (n + 1)) T)
         (W : GeneralLinearGroup (Fin (n + 1)) Q),
         GeneralLinearGroup.map (IsLocalRing.residue Q) W = 1 ∧
         (∀ g, finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa g =
           polarizedLinearInclusion W * polarizedCoefficientMap T.val.toRingHom (σT g) *
             (polarizedLinearInclusion W)⁻¹) ∧
         (∀ g, polarizedComponent (σT g) = finiteBaseQuadraticComponent a F K g) ∧
         (∀ g, polarizedSimilitude (σT g) = Units.map (algebraMap O T).toMonoidHom (ν g)) ∧
         (∀ g, polarizedCoefficientMap (localCoefficientReduction eT).toRingHom (σT g) =
           finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd g)) := by
  let Q := FiniteBaseCMSymmetricCoefficientRing a F K n ρ hn hodd ν ha p hp hpa
  letI := finiteBaseCMSymmetricCoefficientRing_isLocal a F K n ρ hn hodd ν hνk hνc ha p hp hpa
  let eQ := finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc)
  let r := (finiteBaseCMSymmetricUniversalMatrices a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let T := closedMatrixTraceAlgebra (O := O) r
  let σQ := (finiteBaseCMSymmetricUniversalRepresentation a F K n ρ hn hodd ν hνk hνc ha p hp hpa).toMonoidHom
  let μQ := ((Units.map (algebraMap O Q).toMonoidHom).comp ν).comp (FiniteBaseCMKernel a F K).subtype
  let BQ := (σQ (finiteBaseRealConjugation a F)).left.1
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, B, σT, _hτred, hτ, hBred, hB, _hsym, hk, hc, hχ, hν⟩ :=
    finiteBaseCMSymmetricUniversal_tracePolarization_exists a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa hq hsize hchar himage
  letI : IsLocalRing T := hlocal
  obtain ⟨W, hW, hm, hf⟩ := finiteBaseCMSymmetricTrace_strict_alignment a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa hq hsize hchar himage hlocal eT τ B hBred hτ hB
  let σ := (polarizedCoefficientMap T.val.toRingHom).comp σT.toMonoidHom
  let s := (GeneralLinearGroup.map T.val.toRingHom).comp τ.toMonoidHom
  have hkQ (g : FiniteBaseCMKernel a F K) : σQ g.val = polarizedIdentityComponent (r g, μQ g) := by
    have hg := (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
      ha p hp hpa g.val).1.trans g.property
    have he := polarizedIdentity_eq (σQ g.val) hg
    have hμ := (polarizedIdentity_similitude (σQ g.val) hg).symm.trans
      (finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
        ha p hp hpa g.val).2
    rw [he]
    congr 1
    exact Prod.ext rfl hμ
  have hkT (g : FiniteBaseCMKernel a F K) : σ g.val = polarizedIdentityComponent (s g, μQ g) := by
    change polarizedCoefficientMap T.val.toRingHom (σT g.val) = _
    rw [hk]
    rfl
  have hcQ : σQ (finiteBaseRealConjugation a F) = polarizedInvolution BQ :=
    polarizedOdd_eq_involution _
      ((finiteBaseCMSymmetricUniversalRepresentation_characters a F K n ρ hn hodd ν hνk hνc
        ha p hp hpa (finiteBaseRealConjugation a F)).1.trans (finiteBaseCMComponent_conjugation a F K))
      (finiteBaseCMSymmetricUniversal_real_odd a F K n ρ hn hodd ν hνk hνc ha p hp hpa)
  have hcT : σ (finiteBaseRealConjugation a F) = polarizedInvolution (GeneralLinearGroup.map T.val.toRingHom B) := by
    change polarizedCoefficientMap T.val.toRingHom (σT (finiteBaseRealConjugation a F)) = _
    rw [hc]
    rfl
  have he := finiteBaseCM_polarized_conjugate_of_alignment a F K σQ σ r s μQ BQ
    (GeneralLinearGroup.map T.val.toRingHom B) W hkQ hkT hcQ hcT hm hf
  refine ⟨hlocal, hnoeth, htop, hcomplete, eT, σT, W, hW, he, hχ, hν, ?_⟩
  have hcompat := finiteBaseCMSymmetricTrace_reduction_compatibility a F K n ρ hn hodd ν hνk hνc
    ha p hp hpa hlocal eT
  have hWk : GeneralLinearGroup.map (localCoefficientReduction eQ).toRingHom W = 1 := by
    change GeneralLinearGroup.map eQ.toRingHom (GeneralLinearGroup.map (IsLocalRing.residue Q) W) = 1
    rw [hW, map_one]
  intro g
  have hr := polarizedStrictConjugate_reduction (localCoefficientReduction eQ).toRingHom σQ σ W hWk he g
  have hleft := finiteBasePolarizedUniversalRepresentation_residue a F ha p hp hpa
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd) ν
    (finiteBaseCMSymmetricResidualSimilitude a F K n ρ hn hodd ν hνk hνc) g
  change polarizedCoefficientMap (localCoefficientReduction eQ).toRingHom (σQ g) =
    polarizedCoefficientMap ((localCoefficientReduction eQ).comp T.val).toRingHom (σT g) at hr
  rw [← hcompat] at hr
  unfold σQ finiteBaseCMSymmetricUniversalRepresentation at hr
  exact hr.symm.trans hleft

end
end Dubon2026


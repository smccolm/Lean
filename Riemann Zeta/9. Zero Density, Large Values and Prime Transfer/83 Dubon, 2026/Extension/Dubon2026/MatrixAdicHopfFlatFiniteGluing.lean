import Dubon2026.MatrixAdicHopfFlatFiniteCoefficients
import Dubon2026.ContinuousFiberProductHopfModels

/-! # The actual full adic model condition under finite coefficient gluing -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι A B C k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C] [CommRing k]
  [IsLocalRing A] [IsLocalRing B] [Finite A] [Finite B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Continuous strict-conjugacy gluing over actual finite local coefficients preserves the entire all-positive-level model condition. The two original conditions give actual models, the genuine compatible-vector embedding constructs the glued model, and its actual coefficient reductions supply every required level. -/
theorem matrixAdicHopfFlat_finite_continuous_gluing
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* k)
    (ρA : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι A)
    (ρB : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom))
    (hA : MatrixAdicHopfFlat R F K ρA.toMonoidHom)
    (hB : MatrixAdicHopfFlat R F K ρB.toMonoidHom) :
    letI := coefficientFiberProduct_isLocalRing f g
    ∃ ρ : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) ∧
      MatrixAdicHopfFlat R F K ρ.toMonoidHom := by
  letI := coefficientFiberProduct_isLocalRing f g
  obtain ⟨mA⟩ := (matrixAdicHopfFlat_finite_iff ρA.toMonoidHom).mp hA
  obtain ⟨mB⟩ := (matrixAdicHopfFlat_finite_iff ρB.toMonoidHom).mp hB
  obtain ⟨ρ, hρA, hρB, ⟨m⟩⟩ :=
    continuousCoefficientFiberProductHopfModel_exists f g hg rC ρA ρB h mA mB
  exact ⟨ρ, hρA, hρB, matrixAdicHopfFlat_of_model ρ.toMonoidHom m⟩

end
end Dubon2026

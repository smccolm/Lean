import Dubon2026.ArithmeticUnramifiedUniversality

/-! # The original continuous universal unramified arithmetic representation -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

/-- Continuous original matrix representations descend through each actual coefficient ideal with the original quotient topology. -/
def continuousCoefficientQuotientRepresentation
    {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]
    (ρ : G →ₜ* GeneralLinearGroup ι R) (J : Ideal R) :
    G →ₜ* GeneralLinearGroup ι (R ⧸ J) := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J)) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_apply_apply i j)
  exact ⟨(GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J)).comp ρ.toMonoidHom,
    hmap.comp ρ.continuous⟩

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The original continuous arithmetic matrices reduced by the literal ideal of all genuine inertia relations. -/
def arithmeticUnramifiedRepresentation
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a))) :
    rationalArithmeticGaloisGroup a →ₜ*
      GeneralLinearGroup ι (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P) :=
  continuousCoefficientQuotientRepresentation
    (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ)
    (matrixRepresentationRelationIdeal
      (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
      (rationalArithmeticInertia a P.asIdeal))

/-- The same actual continuous universal arithmetic representation kills every element of the genuine original inertia subgroup. -/
theorem arithmeticUnramifiedRepresentation_inertia
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a))) :
    rationalArithmeticInertia a P.asIdeal ≤
      (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom.ker :=
  matrixRepresentationRelationIdeal_quotient_kills
    (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom
    (rationalArithmeticInertia a P.asIdeal)

/-- The genuine universal unramified representation retains the prescribed original determinant on the whole arithmetic group. -/
theorem arithmeticUnramifiedRepresentation_det
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (g : rationalArithmeticGaloisGroup a) :
    GeneralLinearGroup.det (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g) =
      Units.map
        (algebraMap O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toMonoidHom
        (δ g) := by
  let ρ := arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ
  let J := matrixRepresentationRelationIdeal ρ.toMonoidHom (rationalArithmeticInertia a P.asIdeal)
  exact (GeneralLinearGroup.map_det (Ideal.Quotient.mk J) (ρ g)).trans
    (congrArg (Units.map (Ideal.Quotient.mk J).toMonoidHom)
      (arithmeticFixedDeterminantRepresentation_det a ha p hp hpa σ hσ δ g))

/-- The actual residue of the entire original unramified universal representation is the original residual arithmetic representation. -/
theorem arithmeticUnramifiedRepresentation_residue
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction
         (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)).toRingHom).comp
         (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom = σ) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  let ρ := arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ
  let J := matrixRepresentationRelationIdeal ρ.toMonoidHom (rationalArithmeticInertia a P.asIdeal)
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hc := originalLocalQuotientResidueEquiv_original
    (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ) J ((ρ g).val i j)
  have hr := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun
      (arithmeticFixedDeterminantRepresentation_residue a ha p hp hpa σ hσ δ hδ) g)
  exact hc.trans hr

end
end Dubon2026

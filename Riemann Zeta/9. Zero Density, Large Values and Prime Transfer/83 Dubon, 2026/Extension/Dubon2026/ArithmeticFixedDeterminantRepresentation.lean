import Dubon2026.ArithmeticFixedDeterminantUniversality

/-! # The genuine universal arithmetic representation with prescribed determinant -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The actual universal arithmetic matrices reduced by every original prescribed-determinant equation. -/
def arithmeticFixedDeterminantRepresentation
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ) :
    rationalArithmeticGaloisGroup a →ₜ*
      GeneralLinearGroup ι (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) := by
  let ρ := arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ
  let J := representationDeterminantIdeal ρ.toMonoidHom δ
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J)) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_apply_apply i j)
  exact ⟨(GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J)).comp ρ.toMonoidHom,
    hmap.comp ρ.continuous⟩

/-- The entire original continuous universal arithmetic representation has the prescribed determinant after the literal coefficient quotient. -/
theorem arithmeticFixedDeterminantRepresentation_det
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (g : rationalArithmeticGaloisGroup a) :
    GeneralLinearGroup.det (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ g) =
      Units.map (algebraMap O (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ)) (δ g) :=
  representationDeterminantIdeal_quotient_det
    (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ g

/-- The true residue of the genuine continuous fixed-determinant universal representation is the original entire arithmetic residual representation. -/
theorem arithmeticFixedDeterminantRepresentation_residue
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ)).toRingHom).comp
         (arithmeticFixedDeterminantRepresentation a ha p hp hpa σ hσ δ).toMonoidHom = σ) := by
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  let ρ := arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ
  let J := representationDeterminantIdeal ρ.toMonoidHom δ
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hc := originalLocalQuotientResidueEquiv_original
    (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ) J ((ρ g).val i j)
  have hr := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun (arithmeticFramedUniversalRepresentation_residue a ha p hp hpa σ hσ) g)
  exact hc.trans hr

end
end Dubon2026

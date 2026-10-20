import Dubon2026.SmallLevelFromLargeCongruence
import Dubon2026.CMHermitianArithmeticSmallLevel
import Dubon2026.OriginalAdicCompletionResidue
import Dubon2026.SmallLevelSubgroupRestriction

/-! # The original Hermitian arithmetic group at a large congruence prime

For DUB-17 through CHT Lemma 3.3.1 and BLGG Section 3.6, this derives
smallness from a literal principal congruence condition at an original
finite place. Definiteness, compactness, original adic separation and
the cyclotomic rank bound replace the supplied torsion-free certificate.
The global source level and finite double cosets remain to be constructed.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix IsLocalRing
open scoped NumberField ComplexOrder

/-- The original principal congruence subgroup inside the actual completed local matrix group. -/
def finitePlacePrincipalCongruenceImage
    (K ι : Type*) [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (GeneralLinearGroup ι (v.adicCompletion K)) :=
  (MatrixCongruenceKernel (ι := ι)
    (maximalIdeal (Valued.integer (v.adicCompletion K)))).map
      (GeneralLinearGroup.map (Valued.integer (v.adicCompletion K)).subtype)

/-- A large original congruence prime proves arithmetic smallness for the given definite form. -/
theorem cmHermitian_smallLevel_of_large_congruence
    {K ι : Type*} [Field K] [NumberField K] [IsCMField K] [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hU : IsCompact (U : Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ))
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (hlevel : U.map (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
      finitePlacePrincipalCongruenceImage K ι v) :
    ∀ (g : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) (u : U),
      g * u.val * g⁻¹ ∈ (cmHermitianFiniteAdeleHom H).range → u = 1 := by
  letI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  exact smallLevel_of_large_residue_congruence p hp hlarge
    (Valued.integer (v.adicCompletion K)).subtype Subtype.val_injective
    (cmHermitianUnitaryGroup H).subtype Subtype.val_injective
    (cmHermitianFiniteAdeleHom H) U (numberFieldFiniteAdelicMatrixProjection K ι v)
    (cmHermitian_finitePlace_faithful H v)
    (cmHermitian_compactLevel_stabilizer_finite H hH U hU) hlevel

/-- The same derived smallness holds inside the source's original adelic unitary subgroup. -/
theorem cmHermitianAdelic_smallLevel_of_large_congruence
    {K ι : Type*} [Field K] [NumberField K] [IsCMField K] [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (S : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hS : ∀ a, cmHermitianFiniteAdeleHom H a ∈ S)
    (U : Subgroup S) (hU : IsCompact (U : Set S))
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (hlevel : (U.map S.subtype).map (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
      finitePlacePrincipalCongruenceImage K ι v) :
    ∀ (g : S) (u : U),
      g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range → u = 1 := by
  apply smallLevel_restrict_to_subgroup (cmHermitianFiniteAdeleHom H) S hS U
  apply cmHermitian_smallLevel_of_large_congruence H hH (U.map S.subtype)
    (hU.image continuous_subtype_val) v p hp hlarge hlevel

end
end Dubon2026

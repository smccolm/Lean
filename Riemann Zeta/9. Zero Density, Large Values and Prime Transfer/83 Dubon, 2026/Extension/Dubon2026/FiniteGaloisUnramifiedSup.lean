import Dubon2026.NumberFieldUnramifiedCompositum
import Dubon2026.IntermediateFieldSupEmbeddings
import Dubon2026.UnramifiedGaloisCharacters

/-! # Actual unramified finite Galois stages are closed under their literal supremum -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- The actual supremum of two original finite Galois subextensions unramified away from the original integer remains unramified there. The compositum embeddings and generation are derived for that literal supremum. -/
theorem finiteGalois_sup_unramified (a : 𝓞 K) (ha : a ≠ 0)
    (F G : FiniteGaloisIntermediateField K Ω)
    (hF : ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (hG : ∀ w : HeightOneSpectrum (𝓞 G), algebraMap (𝓞 K) (𝓞 G) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∀ w : HeightOneSpectrum (𝓞 (F ⊔ G : FiniteGaloisIntermediateField K Ω)),
      algebraMap (𝓞 K) (𝓞 (F ⊔ G : FiniteGaloisIntermediateField K Ω)) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let H := F ⊔ G
  let f := IntermediateField.inclusion
    (show F.toIntermediateField ≤ H.toIntermediateField from le_sup_left)
  let g := IntermediateField.inclusion
    (show G.toIntermediateField ≤ H.toIntermediateField from le_sup_right)
  letI : Algebra F H := f.toRingHom.toAlgebra
  letI : Algebra G H := g.toRingHom.toAlgebra
  letI : IsScalarTower K F H := IsScalarTower.of_algHom f
  letI : IsScalarTower K G H := IsScalarTower.of_algHom g
  exact numberField_unramified_compositum (L := F) (M := G) (Ω := H) a ha hF hG
    (intermediateField_sup_inclusion_ranges F.toIntermediateField G.toIntermediateField)

end
end Dubon2026

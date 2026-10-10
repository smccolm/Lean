import Dubon2026.FiniteGaloisUnramifiedSup

/-! # The actual union of original unramified finite Galois stages -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- The genuine finite Galois intermediate fields with the original primewise unramifiedness condition outside the original integer. -/
abbrev OriginalUnramifiedGaloisStage (a : 𝓞 K) :=
  {F : FiniteGaloisIntermediateField K Ω //
    ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1}

/-- The literal supremum of all original finite Galois stages unramified outside the original integer in the given ambient field. -/
def originalUnramifiedGaloisUnion (a : 𝓞 K) : IntermediateField K Ω :=
  ⨆ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, F.val.toIntermediateField

omit [NumberField K] in
/-- Every original unramified finite Galois stage lies in the actual stage union. -/
theorem originalUnramifiedGaloisStage_le_union (a : 𝓞 K)
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    F.val.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a :=
  le_iSup (fun F : OriginalUnramifiedGaloisStage (Ω := Ω) a =>
    F.val.toIntermediateField) F

/-- The original nonzero exceptional integer gives an actually directed family of genuine unramified finite Galois stages. -/
theorem originalUnramifiedGaloisStages_directed (a : 𝓞 K) (ha : a ≠ 0) :
    Directed (· ≤ ·) (fun F : OriginalUnramifiedGaloisStage (Ω := Ω) a =>
      F.val.toIntermediateField) := by
  intro F G
  refine ⟨⟨F.val ⊔ G.val, finiteGalois_sup_unramified a ha F.val G.val
    F.property G.property⟩, ?_, ?_⟩
  · exact le_sup_left
  · exact le_sup_right

/-- The actual union of all original unramified finite Galois stages is a genuine Galois extension of the original number field. Its finite-subextension ramification property is a separate obligation. -/
theorem originalUnramifiedGaloisUnion_isGalois (a : 𝓞 K) :
    IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := by
  letI : Normal K (originalUnramifiedGaloisUnion (Ω := Ω) a) := by
    change Normal K (⨆ F : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      F.val.toIntermediateField : IntermediateField K Ω)
    exact IntermediateField.normal_iSup K Ω _
  exact { }

end
end Dubon2026

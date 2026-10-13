import Dubon2026.EmbeddedFiniteGaloisCompositum

/-! # The exact original embeddings generate the constructed local compositum

This discharges the generation premise in the already proved unramified
base-change theorem, preparing DUB-17's original local H2 restriction comparison.
-/

namespace Dubon2026
noncomputable section

variable {R K L Ω : Type} [Field R] [Field K] [Field L] [Field Ω]
  [Algebra R K] [Algebra R L] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [FiniteDimensional R L] [IsGalois R L] (i : L →ₐ[R] Ω)

/-- The original arithmetic embedding, with its codomain restricted to the
same actual compositum it generates over the original local base. -/
def embeddedFiniteGaloisCompositumInclusion : L →ₐ[R] embeddedFiniteGaloisCompositum (K := K) i :=
  i.codRestrict ((embeddedFiniteGaloisCompositum (K := K) i).toIntermediateField.restrictScalars R).toSubalgebra
    (fun x => IntermediateField.subset_adjoin K (Set.range i) ⟨x, rfl⟩)

/-- Codomain restriction leaves the original arithmetic field value unchanged. -/
theorem embeddedFiniteGaloisCompositumInclusion_coe (x : L) :
    (embeddedFiniteGaloisCompositumInclusion (K := K) i x : Ω) = i x := by
  rfl

/-- The original local base and the exact arithmetic embedding generate the
entire constructed original finite Galois compositum as an actual field. -/
theorem embeddedFiniteGaloisCompositum_ranges :
    (algebraMap K (embeddedFiniteGaloisCompositum (K := K) i)).fieldRange ⊔
      (embeddedFiniteGaloisCompositumInclusion (K := K) i).toRingHom.fieldRange = ⊤ := by
  let M := embeddedFiniteGaloisCompositum (K := K) i
  let j := embeddedFiniteGaloisCompositumInclusion (K := K) i
  let S : Subfield M := (algebraMap K M).fieldRange ⊔ j.toRingHom.fieldRange
  have hle : M.toIntermediateField.toSubfield ≤ S.map M.toIntermediateField.val.toRingHom := by
    apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K M x, (show (algebraMap K M).fieldRange ≤ S from le_sup_left) ⟨x, rfl⟩, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨j x, (show j.toRingHom.fieldRange ≤ S from le_sup_right) ⟨x, rfl⟩, rfl⟩
  change S = ⊤
  apply top_unique
  intro x _hx
  obtain ⟨y, hy, he⟩ := hle x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

end
end Dubon2026

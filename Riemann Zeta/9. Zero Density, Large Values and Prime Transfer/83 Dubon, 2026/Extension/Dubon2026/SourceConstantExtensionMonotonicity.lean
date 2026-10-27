import Dubon2026.SourceConstantExtensionChain

/-! DUB-17/18 -> rational Fourier spanning -> Fricke integral base change.
The generated algebra, generated field and integral relations persist under
an inclusion of constant fields. Native adjoin induction captures only the
finitely many complex constants occurring in each element. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]

theorem adjoin_constants_mono {F G : IntermediateField ℚ ℂ} (h : F ≤ G)
    (T : Set K) {x : K} (hx : x ∈ Algebra.adjoin F T) : x ∈ Algebra.adjoin G T := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap z => exact Subalgebra.algebraMap_mem _ (⟨z, h z.property⟩ : G)
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy

theorem generated_constants_mono {F G : IntermediateField ℚ ℂ} (h : F ≤ G)
    (S : Set K) {x : K} (hx : x ∈ KFld F S) : x ∈ KFld G S := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
  | algebraMap z => exact IntermediateField.algebraMap_mem _ (⟨z, h z.property⟩ : G)
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem integral_constants_mono {F G : IntermediateField ℚ ℂ} (h : F ≤ G)
    (T : Set K) {x : K} (hx : IsIntegral (Algebra.adjoin F T) x) :
    IsIntegral (Algebra.adjoin G T) x := by
  obtain ⟨P, hm, hc, hx⟩ := (isIntegral_subalgebra_iff _ x).mp hx
  exact (isIntegral_subalgebra_iff _ x).mpr
    ⟨P, hm, fun n => adjoin_constants_mono h T (hc n), hx⟩

theorem generated_mem_iff_closure (F : IntermediateField ℚ ℂ) (S : Set K) (x : K) :
    x ∈ KFld F S ↔ x ∈ Subfield.closure (algebraMap ℂ K '' (F : Set ℂ) ∪ S) := by
  have hr : Set.range (algebraMap F K) = algebraMap ℂ K '' (F : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hr]

theorem exists_list_mem_algebra (F : IntermediateField ℚ ℂ) {T : Set K} {x : K}
    (hx : x ∈ Algebra.adjoin ℂ T) : ∃ l : List ℂ, x ∈ Algebra.adjoin (constantChain F l) T := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨[], Algebra.subset_adjoin hy⟩
  | algebraMap z =>
    exact ⟨[z], Subalgebra.algebraMap_mem _
      (⟨z, mem_constantChain_of_mem F List.mem_cons_self⟩ : constantChain F [z])⟩
  | add x y _ _ hx hy =>
    obtain ⟨l₁, h₁⟩ := hx
    obtain ⟨l₂, h₂⟩ := hy
    exact ⟨l₁ ++ l₂, Subalgebra.add_mem _
      (adjoin_constants_mono (constantChain_le_append_left F l₁ l₂) T h₁)
      (adjoin_constants_mono (constantChain_le_append_right F l₁ l₂) T h₂)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, h₁⟩ := hx
    obtain ⟨l₂, h₂⟩ := hy
    exact ⟨l₁ ++ l₂, Subalgebra.mul_mem _
      (adjoin_constants_mono (constantChain_le_append_left F l₁ l₂) T h₁)
      (adjoin_constants_mono (constantChain_le_append_right F l₁ l₂) T h₂)⟩

theorem exists_list_mem_field (F : IntermediateField ℚ ℂ) {S : Set K} {x : K}
    (hx : x ∈ IntermediateField.adjoin ℂ S) : ∃ l : List ℂ, x ∈ KFld (constantChain F l) S := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact ⟨[], IntermediateField.subset_adjoin _ _ hy⟩
  | algebraMap z =>
    exact ⟨[z], IntermediateField.algebraMap_mem _
      (⟨z, mem_constantChain_of_mem F List.mem_cons_self⟩ : constantChain F [z])⟩
  | add x y _ _ hx hy =>
    obtain ⟨l₁, h₁⟩ := hx
    obtain ⟨l₂, h₂⟩ := hy
    exact ⟨l₁ ++ l₂, add_mem
      (generated_constants_mono (constantChain_le_append_left F l₁ l₂) S h₁)
      (generated_constants_mono (constantChain_le_append_right F l₁ l₂) S h₂)⟩
  | inv x _ hx =>
    obtain ⟨l, hl⟩ := hx
    exact ⟨l, inv_mem hl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, h₁⟩ := hx
    obtain ⟨l₂, h₂⟩ := hy
    exact ⟨l₁ ++ l₂, mul_mem
      (generated_constants_mono (constantChain_le_append_left F l₁ l₂) S h₁)
      (generated_constants_mono (constantChain_le_append_right F l₁ l₂) S h₂)⟩

end
end Dubon2026.SourceFricke.ConstantDescent
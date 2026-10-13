import Dubon2026.SupportedIdeleCoordinates

/-! # The unrestricted and integral factors of the actual finite coordinates

The coordinate product is split at the original support. Outside it the
factor is the unit group of the original completion's integer ring. This
is the literal coefficient bridge to the unramified vanishing theorem
in DUB-17's supported-idele cohomology calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Split the actual finite coordinates into unrestricted field units and original integer units. -/
def numberFieldSupportedFiniteFactorEquiv :
    numberFieldSupportedFiniteCoordinates K S ≃*
      ((v : S) → (v.val.adicCompletion K)ˣ) ×
        ((v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) → (v.val.adicCompletionIntegers K)ˣ) where
  toFun x := (fun v => x.val v.val, fun v => by
    have hx : x.val v.val ∈ (v.val.adicCompletionIntegers K).units := by
      have h := x.property
      simp only [numberFieldSupportedFiniteCoordinates, Subgroup.mem_iInf,
        Subgroup.mem_comap, Pi.evalMonoidHom_apply] at h
      exact h v.val v.property
    exact ⟨⟨(x.val v.val).val, hx.1⟩, ⟨(x.val v.val).inv, hx.2⟩,
      Subtype.ext (x.val v.val).val_inv, Subtype.ext (x.val v.val).inv_val⟩)
  invFun x := ⟨fun v => if h : v ∈ S then x.1 ⟨v, h⟩ else
    Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom (x.2 ⟨v, h⟩), by
      simp only [numberFieldSupportedFiniteCoordinates, Subgroup.mem_iInf,
        Subgroup.mem_comap, Pi.evalMonoidHom_apply]
      intro v hv
      simp only [dif_neg hv]
      exact ⟨(x.2 ⟨v, hv⟩).val.property, (x.2 ⟨v, hv⟩).inv.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    dsimp only
    split_ifs with h
    · rfl
    · apply Units.ext
      rfl
  right_inv x := by
    apply Prod.ext
    · funext v
      simp only [dif_pos v.property]
    · funext v
      apply Units.ext
      apply Subtype.ext
      simp only [dif_neg v.property]
      rfl
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · funext v
      apply Units.ext
      apply Subtype.ext
      rfl

/-- The unrestricted factor remains the original finite field-unit evaluation. -/
theorem numberFieldSupportedFiniteFactorEquiv_inside
    (x : numberFieldSupportedFiniteCoordinates K S) (v : S) :
    (numberFieldSupportedFiniteFactorEquiv K S x).1 v = x.val v.val := rfl

/-- The outside-support factor retains the original completion-field value. -/
theorem numberFieldSupportedFiniteFactorEquiv_outside
    (x : numberFieldSupportedFiniteCoordinates K S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (((numberFieldSupportedFiniteFactorEquiv K S x).2 v).val : v.val.adicCompletion K) =
      (x.val v.val).val := rfl

end
end Dubon2026

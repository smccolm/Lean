import Dubon2026.SourceOriginalPairBaseChange

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
degeneracy maps. Equality of the two original generator values determines
the whole field map, including maps into punctured germs. Native equality
on inverses avoids constructing an additional meromorphic function field.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem original_field_ringHom_ext (N : ℕ) [NeZero N]
    {R : Type*} [Semiring R]
    (f g : modularFunctionFieldOver N ℂ →+* R)
    (hc : ∀ c : ℂ, f (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =
      g (algebraMap ℂ (modularFunctionFieldOver N ℂ) c))
    (hj : f (jOver N ℂ) = g (jOver N ℂ))
    (hjN : f (jNOver N ℂ) = g (jNOver N ℂ)) : f = g := by
  ext x
  have hx : x ∈ IntermediateField.adjoin ℂ
      ({jOver N ℂ, jNOver N ℂ} : Set (modularFunctionFieldOver N ℂ)) := by
    rw [original_internal_pair_adjoin_top]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact hj
    · rcases hy with rfl
      exact hjN
  | algebraMap c => exact hc c
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | inv y _ hy => exact eq_on_inv₀ f g hy
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

end
end Dubon2026.SourceFunctionField

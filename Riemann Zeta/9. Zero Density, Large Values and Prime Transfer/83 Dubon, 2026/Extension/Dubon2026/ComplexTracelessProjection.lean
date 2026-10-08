import Dubon2026.ComplexSl2Basis

/-! # The actual scalar-trace projection from GL₂ infinitesimals to SL₂ -/

namespace Dubon2026

noncomputable section

/-- Remove exactly half the original trace from the diagonal of a genuine complex two-by-two matrix. -/
def complexTracelessProjection : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ ComplexSl2 where
  toFun a := ⟨a - (Matrix.trace a / 2) • 1, by
    change Matrix.trace (a - (Matrix.trace a / 2) • 1) = 0
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    ring⟩
  map_add' a b := by
    apply Subtype.ext
    change a + b - (Matrix.trace (a + b) / 2) • 1 =
      (a - (Matrix.trace a / 2) • 1) + (b - (Matrix.trace b / 2) • 1)
    rw [Matrix.trace_add]
    module
  map_smul' c a := by
    apply Subtype.ext
    change c • a - (Matrix.trace (c • a) / 2) • 1 = c • (a - (Matrix.trace a / 2) • 1)
    rw [Matrix.trace_smul]
    module
  map_lie' {a b} := by
    apply Subtype.ext
    change ⁅a, b⁆ - (Matrix.trace ⁅a, b⁆ / 2) • 1 =
      ⁅a - (Matrix.trace a / 2) • 1, b - (Matrix.trace b / 2) • 1⁆
    have ht : Matrix.trace ⁅a, b⁆ = 0 := by
      rw [LieRing.of_associative_ring_bracket, Matrix.trace_sub, Matrix.trace_mul_comm a b, sub_self]
    rw [ht, zero_div, zero_smul, sub_zero]
    simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_smul_comm,
      smul_mul_assoc, one_mul, mul_one]
    module

/-- The genuine trace projection retains exactly its original matrix formula. -/
theorem complexTracelessProjection_val (a : Matrix (Fin 2) (Fin 2) ℂ) :
    (complexTracelessProjection a).val = a - (Matrix.trace a / 2) • 1 := rfl

/-- The genuine projection is exactly the identity on every original traceless matrix. -/
theorem complexTracelessProjection_sl (x : ComplexSl2) : complexTracelessProjection x.val = x := by
  apply Subtype.ext
  rw [complexTracelessProjection_val, show Matrix.trace x.val = 0 from x.property,
    zero_div, zero_smul, sub_zero]

/-- Every original traceless matrix is the projection of its literal original matrix. -/
theorem complexTracelessProjection_surjective : Function.Surjective complexTracelessProjection :=
  fun x => ⟨x.val, complexTracelessProjection_sl x⟩

/-- The actual scalar matrix infinitesimal is annihilated by the genuine trace projection. -/
theorem complexTracelessProjection_scalar (c : ℂ) :
    complexTracelessProjection (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  apply Subtype.ext
  rw [complexTracelessProjection_val]
  simp [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]

end
end Dubon2026

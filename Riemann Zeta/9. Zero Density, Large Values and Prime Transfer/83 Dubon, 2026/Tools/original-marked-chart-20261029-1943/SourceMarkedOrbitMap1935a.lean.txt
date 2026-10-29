import Mathlib.GroupTheory.GroupAction.Quotient

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> natural original-field
marked chart. Equal stabilizers extend one matched pair to an injective
equivariant map on a transitive orbit. The consumer uses actual point sign
classes and normalized original-field embeddings, with both hypotheses proved.
The native stabilizer API suffices; no unsigned point transitivity is needed. -/
namespace Dubon2026.SourceFunctionField.MarkedChart

theorem exists_injective_equivariant_map_of_stabilizer_eq
    {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (x : X) (y : Y) (htrans : ∀ z : X, ∃ g : G, g • x = z)
    (hstab : MulAction.stabilizer G x = MulAction.stabilizer G y) :
    ∃ f : X → Y, f x = y ∧ Function.Injective f ∧
      ∀ (g : G) (z : X), f (g • z) = g • f z := by
  classical
  have hsame (g h : G) : g • x = h • x ↔ g • y = h • y := by
    rw [← smul_left_cancel_iff h⁻¹, ← mul_smul, inv_smul_smul,
      ← MulAction.mem_stabilizer_iff, hstab, MulAction.mem_stabilizer_iff,
      mul_smul, inv_smul_eq_iff]
  let f : X → Y := fun z => (htrans z).choose • y
  have hf (g : G) : f (g • x) = g • y :=
    (hsame _ g).mp (htrans (g • x)).choose_spec
  refine ⟨f, ?_, ?_, ?_⟩
  · simpa only [one_smul] using hf 1
  · intro a b hab
    obtain ⟨g, rfl⟩ := htrans a
    obtain ⟨h, rfl⟩ := htrans b
    rw [hf, hf] at hab
    exact (hsame g h).mpr hab
  · intro g z
    obtain ⟨h, rfl⟩ := htrans z
    rw [← mul_smul, hf, hf, mul_smul]

end Dubon2026.SourceFunctionField.MarkedChart

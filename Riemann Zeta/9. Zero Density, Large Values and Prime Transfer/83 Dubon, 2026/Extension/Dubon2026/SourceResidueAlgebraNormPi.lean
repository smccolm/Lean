import Dubon2026.SourceResidueAlgebraNorm
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fin.Tuple.Basic

/-! DUB-17/18 -> Weil reciprocity -> norm on a residue fiber -> the
native Chinese remainder product. Mathlib already constructs the full
ramified-factor decomposition. This finite-product norm calculation lets
that result replace a separate induction on ad hoc fiber ideals. -/
namespace Dubon2026
noncomputable section

private theorem algebra_norm_fin_pi (K : Type*) [Field K] (n : ℕ) :
    ∀ (A : Fin n → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
      [∀ i, FiniteDimensional K (A i)] (x : ∀ i, A i),
      Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  classical
  induction n with
  | zero =>
    intro A _ _ _ x
    rw [algebra_norm_subsingleton]
    simp
  | succ n ih =>
    intro A _ _ _ x
    let ee : (∀ i, A i) ≃ₐ[K] A 0 × (∀ i : Fin n, A i.succ) :=
      { (Fin.consEquiv A).symm with
        map_mul' _ _ := rfl
        map_add' _ _ := rfl
        commutes' _ := rfl }
    rw [← Algebra.norm_eq_of_algEquiv ee x, algebra_norm_product]
    change Algebra.norm K (x 0) * Algebra.norm K (fun i : Fin n => x i.succ) = _
    rw [ih, Fin.prod_univ_succ]

theorem algebra_norm_finite_pi (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, FiniteDimensional K (A i)] (x : ∀ i, A i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let ee := AlgEquiv.piCongrLeft K A e
  rw [← Algebra.norm_eq_of_algEquiv ee.symm x, algebra_norm_fin_pi]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end
end Dubon2026

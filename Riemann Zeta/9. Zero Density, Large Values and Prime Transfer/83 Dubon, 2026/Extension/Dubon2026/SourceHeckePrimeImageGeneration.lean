import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! The generator reduction required for the original rank-two Tate
consumer: a surjective integral word presentation lets the prime images
generate the same coefficient algebra as the full integral Hecke image. -/
namespace Dubon2026
noncomputable section

theorem primeImage_adjoin_eq_top {K A T I : Type*} [CommRing K] [Ring A] [Algebra ℤ A]
    [CommRing T] [Algebra K T] (w : FreeAlgebra ℤ I →ₐ[ℤ] A)
    (hw : Function.Surjective w) (φ : A →+* T)
    (hφ : Algebra.adjoin K (Set.range φ) = ⊤) :
    Algebra.adjoin K (Set.range fun i => φ (w (FreeAlgebra.ι ℤ i))) = ⊤ := by
  apply top_unique
  rw [← hφ]
  apply Algebra.adjoin_le
  rintro _ ⟨a, rfl⟩
  obtain ⟨a, rfl⟩ := hw a
  induction a using FreeAlgebra.induction with
  | grade0 z =>
      have hz : φ (w (algebraMap ℤ (FreeAlgebra ℤ I) z)) = (z : T) := by
        rw [AlgHom.commutes]
        exact (congrArg φ (map_intCast (algebraMap ℤ A) z)).trans (map_intCast φ z)
      rw [hz]
      exact (Algebra.adjoin K _).intCast_mem z
  | grade1 i => exact Algebra.subset_adjoin ⟨i, rfl⟩
  | add a b ha hb => simpa only [map_add] using (Algebra.adjoin K _).add_mem ha hb
  | mul a b ha hb => simpa only [map_mul] using (Algebra.adjoin K _).mul_mem ha hb

end
end Dubon2026

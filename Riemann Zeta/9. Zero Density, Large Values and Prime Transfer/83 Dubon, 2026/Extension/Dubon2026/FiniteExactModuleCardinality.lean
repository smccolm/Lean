import Dubon2026.FinitePeriodicHomologyCardinality

/-! # Finiteness and cardinal identities from actual exact module maps -/

namespace Dubon2026
noncomputable section

variable {R A B C D : Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- Finite actual kernel and image force the original domain to be finite. -/
theorem linearMap_finite_of_finite_kernel_range (f : A →ₗ[R] B)
    [Finite f.ker] [Finite f.range] : Finite A := by
  have h : 0 < Nat.card A := by
    rw [linearMap_card_eq_kernel_mul_range f]
    exact Nat.mul_pos Nat.card_pos Nat.card_pos
  exact (Nat.card_pos_iff.mp h).2

/-- A middle module is finite when the literal kernel is the actual image
of a finite module and its next coefficient module is finite. -/
theorem finite_exact_module_middle [Finite A] [Finite C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : f.range = g.ker) : Finite B := by
  haveI : Finite f.range := Finite.of_surjective f.rangeRestrict f.surjective_rangeRestrict
  haveI : Finite g.ker := Finite.of_equiv f.range (LinearEquiv.ofEq _ _ hfg).toEquiv
  exact linearMap_finite_of_finite_kernel_range g

/-- Count a genuine four-term exact sequence through its original kernel
and image, retaining both endpoints and all three original maps. -/
theorem exact_four_module_cardinality
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D)
    (hf : Function.Injective f) (hh : Function.Surjective h)
    (hfg : f.range = g.ker) (hgh : g.range = h.ker) :
    Nat.card B * Nat.card D = Nat.card A * Nat.card C := by
  have hA : Nat.card g.ker = Nat.card A := by
    rw [← hfg]
    exact Nat.card_congr (LinearEquiv.ofInjective f hf).symm.toEquiv
  have hD : Nat.card h.range = Nat.card D :=
    Nat.card_congr (LinearEquiv.ofTop h.range (LinearMap.range_eq_top.mpr hh)).toEquiv
  rw [linearMap_card_eq_kernel_mul_range g,
    linearMap_card_eq_kernel_mul_range h, hA, hD, ← hgh]
  ac_rfl

end
end Dubon2026

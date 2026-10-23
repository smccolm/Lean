import Dubon2026.SourceHeckeWordTransport

/-! DUB-17/18 -> rational Hecke descent -> comparing the actual Q and C
character actions. The existing integral-word intertwiner has an integral
source module; this version permits the required Q-linear source and
C-linear target while retaining the same additive coefficient inclusion.
The proof is the same free-algebra induction, using only integer scalars.
-/
namespace Dubon2026
noncomputable section

private theorem integral_word_cast {ι A : Type*} [Ring A] (t : ι → A) (r : ℤ) :
    FreeAlgebra.lift ℤ t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

theorem sourceHeckeWord_intertwine_addHom {ι R S M V : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module S V]
    (t : ι → Module.End R M) (u : ι → Module.End S V) (Φ : M →+ V)
    (hΦ : ∀ i x, Φ (t i x) = u i (Φ x)) (a : FreeAlgebra ℤ ι) (x : M) :
    Φ (FreeAlgebra.lift ℤ t a x) = FreeAlgebra.lift ℤ u a (Φ x) := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 r =>
    rw [integral_word_cast, integral_word_cast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hΦ]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

end
end Dubon2026

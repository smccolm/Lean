import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Cardinality of the two homologies of an actual finite periodic module -/

namespace Dubon2026
noncomputable section

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The first isomorphism theorem counts the actual kernel and image of
the displayed linear map, including the original quotient representatives. -/
theorem linearMap_card_eq_kernel_mul_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card f.ker * Nat.card f.range := by
  rw [Submodule.card_eq_card_quotient_mul_card f.ker]
  congr 1
  exact Nat.card_congr f.quotKerEquivRange.toEquiv

/-- The literal homology of two original composable endomorphisms. -/
def linearPeriodicHomology (f g : M →ₗ[R] M) (hgf : g.comp f = 0) : Type :=
  g.ker ⧸ (f.codRestrict g.ker (fun x => by
    change g (f x) = 0
    exact LinearMap.congr_fun hgf x)).range

/-- For a finite original module, the two periodic homologies have equal
cardinality, by counting the actual kernels, images and quotients. -/
theorem finite_periodic_homology_card_eq [Finite M]
    (f g : M →ₗ[R] M) (hgf : g.comp f = 0) (hfg : f.comp g = 0) :
    Nat.card (linearPeriodicHomology f g hgf) =
      Nat.card (linearPeriodicHomology g f hfg) := by
  let ff := f.codRestrict g.ker (fun x => by
    change g (f x) = 0
    exact LinearMap.congr_fun hgf x)
  let gg := g.codRestrict f.ker (fun x => by
    change f (g x) = 0
    exact LinearMap.congr_fun hfg x)
  have hf : Nat.card M = Nat.card f.ker * Nat.card ff.range := by
    simpa only [ff, LinearMap.ker_codRestrict] using linearMap_card_eq_kernel_mul_range ff
  have hg : Nat.card M = Nat.card g.ker * Nat.card gg.range := by
    simpa only [gg, LinearMap.ker_codRestrict] using linearMap_card_eq_kernel_mul_range gg
  have hqf : Nat.card g.ker = Nat.card ff.range *
      Nat.card (linearPeriodicHomology f g hgf) :=
    Submodule.card_eq_card_quotient_mul_card ff.range
  have hqg : Nat.card f.ker = Nat.card gg.range *
      Nat.card (linearPeriodicHomology g f hfg) :=
    Submodule.card_eq_card_quotient_mul_card gg.range
  have hp : 0 < Nat.card ff.range * Nat.card gg.range :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hp
  calc
    (Nat.card ff.range * Nat.card gg.range) *
        Nat.card (linearPeriodicHomology f g hgf) = Nat.card g.ker * Nat.card gg.range := by
      rw [hqf]
      ac_rfl
    _ = Nat.card M := hg.symm
    _ = Nat.card f.ker * Nat.card ff.range := hf
    _ = (Nat.card ff.range * Nat.card gg.range) *
        Nat.card (linearPeriodicHomology g f hfg) := by
      rw [hqg]
      ac_rfl

end
end Dubon2026

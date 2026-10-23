import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Equiv

/-! The exact quotient comparison needed to identify the original lattice
and cusp integral Hecke algebras. Surjective word evaluations with the
same proved relations induce a ring equivalence; native quotient lifting
preserves multiplication and the common word values. -/
namespace Dubon2026
noncomputable section
variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
    (f : A →+* B) (g : A →+* C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hr : ∀ a b, f a = f b ↔ g a = g b)

include hr in
theorem commonHeckeWord_kernel_le : RingHom.ker f ≤ RingHom.ker g := by
  intro a ha
  have h : f a = f 0 := (RingHom.mem_ker.mp ha).trans (map_zero f).symm
  exact RingHom.mem_ker.mpr ((hr a 0).mp h |>.trans (map_zero g))

/-- The ring homomorphism determined by identical integral word relations. -/
def commonHeckeWordRingHom : B →+* C :=
  f.liftOfSurjective hf ⟨g, commonHeckeWord_kernel_le f g hr⟩

theorem commonHeckeWordRingHom_apply (a : A) :
    commonHeckeWordRingHom f g hf hr (f a) = g a :=
  RingHom.liftOfSurjective_comp_apply f hf ⟨g, commonHeckeWord_kernel_le f g hr⟩ a

include hg in
theorem commonHeckeWordRingHom_bijective : Function.Bijective (commonHeckeWordRingHom f g hf hr) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [commonHeckeWordRingHom_apply, commonHeckeWordRingHom_apply] at h
    exact (hr a b).mpr h
  · intro y
    obtain ⟨a, rfl⟩ := hg y
    exact ⟨f a, commonHeckeWordRingHom_apply f g hf hr a⟩

/-- The faithful equivalence of the two actual integral operator quotients. -/
def commonHeckeWordRingEquiv : B ≃+* C :=
  RingEquiv.ofBijective (commonHeckeWordRingHom f g hf hr)
    (commonHeckeWordRingHom_bijective f g hf hg hr)

theorem commonHeckeWordRingEquiv_apply (a : A) :
    commonHeckeWordRingEquiv f g hf hg hr (f a) = g a :=
  commonHeckeWordRingHom_apply f g hf hr a

end
end Dubon2026

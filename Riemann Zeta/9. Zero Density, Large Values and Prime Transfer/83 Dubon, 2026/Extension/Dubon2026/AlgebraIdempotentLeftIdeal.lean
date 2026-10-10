import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # The actual left ideal cut out by an original algebra idempotent -/

namespace Dubon2026
noncomputable section

variable {S A : Type*} [CommRing S] [Ring A] [Algebra S A]

/-- The genuine left ideal is the image of right multiplication by the original algebra element. -/
def algebraIdempotentLeftIdeal (e : A) : Submodule S A :=
  (LinearMap.mulRight S e).range

/-- For the original idempotent, its actual left ideal consists precisely of its right-multiplication fixed points. -/
theorem mem_algebraIdempotentLeftIdeal_iff (e : A) (he : e ^ 2 = e) (x : A) :
    x ∈ algebraIdempotentLeftIdeal (S := S) e ↔ x * e = x := by
  constructor
  · rintro ⟨y, rfl⟩
    change y * e * e = y * e
    rw [mul_assoc, ← pow_two, he]
  · intro hx
    exact ⟨x, hx⟩

/-- Actual left multiplication preserves the original left ideal. -/
theorem mul_mem_algebraIdempotentLeftIdeal (e : A) (a x : A)
    (hx : x ∈ algebraIdempotentLeftIdeal (S := S) e) :
    a * x ∈ algebraIdempotentLeftIdeal (S := S) e := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨a * y, mul_assoc a y e⟩

/-- The same original left ideal is finite whenever its actual ambient coefficient algebra is finite. -/
theorem algebraIdempotentLeftIdeal_finite [Module.Finite S A] (e : A) :
    Module.Finite S (algebraIdempotentLeftIdeal (S := S) e) :=
  Module.Finite.range (LinearMap.mulRight S e)

/-- An original left-ideal element lying in the coefficient-ideal multiple of the whole algebra already lies in that coefficient-ideal multiple of the same left ideal. -/
theorem algebraIdempotentLeftIdeal_mem_ideal_smul (I : Ideal S)
    (e : A) (he : e ^ 2 = e) (x : algebraIdempotentLeftIdeal (S := S) e)
    (hx : (x : A) ∈ I • (⊤ : Submodule S A)) :
    x ∈ I • (⊤ : Submodule S (algebraIdempotentLeftIdeal (S := S) e)) := by
  rw [Submodule.mem_smul_top_iff]
  have hfix := (mem_algebraIdempotentLeftIdeal_iff e he x).mp x.property
  have hm : (x : A) ∈ (I • (⊤ : Submodule S A)).map (LinearMap.mulRight S e) :=
    ⟨x, hx, hfix⟩
  simpa only [Submodule.map_smul'', Submodule.map_top, algebraIdempotentLeftIdeal] using hm

end
end Dubon2026

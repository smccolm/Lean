import Dubon2026.NumberFieldAdelicLatticeBound
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Finite freeness of the actual attached adelic lattice

The original lattice is injected into a finite product of the original
ring of integers by the denominator derived from its adelic matrix.
Noetherianity and torsion freeness then give a finite free integral
module. Full rank and the uniform trace determinant are separate DUB-17
arithmetic double-coset obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Scaling by an actual denominator maps the attached lattice into integral vectors. -/
def numberFieldAdelicLatticeIntegralMap
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) (d : 𝓞 K)
    (hint : ∀ x ∈ numberFieldAdelicLattice K ι g, ∀ i, IsIntegral ℤ ((d : K) * x i)) :
    numberFieldAdelicLattice K ι g →ₗ[ℤ] (ι → 𝓞 K) :=
    { toFun := fun x i => ⟨(d : K) * x.val i, hint x.val x.property i⟩
      map_add' := by
        intro x y
        ext i
        change (d : K) * (x.val i + y.val i) = (d : K) * x.val i + (d : K) * y.val i
        exact mul_add _ _ _
      map_smul' := by
        intro n x
        ext i
        change (d : K) * (n • x.val i) = n • ((d : K) * x.val i)
        simpa only [zsmul_eq_mul] using mul_left_comm (d : K) (n : K) (x.val i) }
/-- Scaling by a nonzero actual denominator is injective on the attached lattice. -/
theorem numberFieldAdelicLatticeIntegralMap_injective
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) (d : 𝓞 K)
    (hint : ∀ x ∈ numberFieldAdelicLattice K ι g, ∀ i, IsIntegral ℤ ((d : K) * x i))
    (hd : d ≠ 0) : Function.Injective (numberFieldAdelicLatticeIntegralMap K ι g d hint) := by
  intro x y h
  apply Subtype.ext
  funext i
  have he : (d : K) * x.val i = (d : K) * y.val i :=
    congrArg (fun z : ι → 𝓞 K => (z i : K)) h
  have hdK : (d : K) ≠ 0 := by
    intro hz
    exact hd (Subtype.ext hz)
  exact mul_left_cancel₀ hdK he

/-- The lattice attached to an actual adelic matrix is finite over the rational integers. -/
theorem numberFieldAdelicLattice_finite
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Module.Finite ℤ (numberFieldAdelicLattice K ι g) := by
  obtain ⟨d, hd, hint⟩ := numberFieldAdelicLattice_exists_denominator K ι g
  exact Module.Finite.of_injective (numberFieldAdelicLatticeIntegralMap K ι g d hint)
    (numberFieldAdelicLatticeIntegralMap_injective K ι g d hint hd)

/-- The actual attached lattice is free over the rational integers. -/
theorem numberFieldAdelicLattice_free
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K)) :
    Module.Free ℤ (numberFieldAdelicLattice K ι g) := by
  letI := numberFieldAdelicLattice_finite K ι g
  infer_instance

end
end Dubon2026

import Dubon2026.CMAdelicPairingDualContainment
import Dubon2026.CMHermitianPositiveMatrix

/-! # Uniform containment of the actual trace-dual lattices

For the fixed source matrix and fixed positive integral trace scaling,
one positive integer sends every attached trace-dual lattice into its
original lattice. It is obtained from the original trace-dual basis and
inverse matrix, independently of the adelic unitary element. This is
the uniform arithmetic input to DUB-17's Gram determinant bound.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single positive integer sends every original trace-dual lattice into its attached lattice. -/
theorem cmAdelicTraceDual_uniform_containment (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) (d : ℤ) (hd : 0 < d) :
    ∃ m : ℤ, 0 < m ∧ ∀ (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K),
      (∀ y : numberFieldAdelicLattice K ι g.val,
        IsIntegral ℤ (d • cmHermitianRationalTraceForm K H x y.val)) →
      m • x ∈ numberFieldAdelicLattice K ι g.val := by
  obtain ⟨U, hU⟩ := cmHermitianPositiveMatrix_isUnit K H hH
  let J : Matrix ι ι K := (U⁻¹).val
  have hHJ : H * J = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  obtain ⟨k, hk, hJ⟩ := numberField_exists_positive_integral_multiple
    (fun ij : ι × ι => J ij.1 ij.2)
  obtain ⟨c, hc, hpair⟩ := cmAdelicTraceDual_exists_uniform_pairing_denominator K (ι := ι)
  refine ⟨k * (c * d), mul_pos hk (mul_pos hc hd), ?_⟩
  intro g x hx
  exact cmAdelicPairing_scaled_dual_mem K H J hHJ k (fun i j => hJ (i, j))
    (c * d) g x (hpair H d g x hx)

end
end Dubon2026

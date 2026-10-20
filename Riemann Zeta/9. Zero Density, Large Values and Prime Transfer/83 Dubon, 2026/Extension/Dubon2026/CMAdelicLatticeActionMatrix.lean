import Dubon2026.CMAdelicLatticeScalarBound
import Dubon2026.IntegralBilinearCoordinates
import Dubon2026.IntegralBilinearFiniteSublevel

/-! # Finite original CM scalar-action matrices at a fixed trace Gram matrix

Every column is an actual integral scalar multiple of a lattice basis
vector. Its trace-form value has the same bound for all adelic lattices
and all bases with the specified Gram matrix. Finite sublevel sets then
give finitely many such matrices, advancing DUB-17's compatible CM
action finiteness without an assumed bound on their coefficients.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The integral matrix of the original ring-of-integers scalar action in a specified lattice basis. -/
def cmAdelicLatticeActionMatrix (H : Matrix ι ι K)
    (g : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)) (a : 𝓞 K) : Matrix κ κ ℤ :=
  fun i j => b.repr (a • b j) i

/-- At a fixed original trace Gram matrix, a fixed original integral scalar has only finitely many action matrices. -/
theorem cmAdelicLatticeActionMatrix_finite (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (d : ℤ) (hd : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (A : Matrix κ κ ℤ) (a : 𝓞 K) :
    {M : Matrix κ κ ℤ | ∃ (g : cmFiniteAdelicUnitaryGroup K H)
      (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)),
      toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) = A ∧
        M = cmAdelicLatticeActionMatrix K H g b a}.Finite := by
  classical
  by_cases he : ∃ (g : cmFiniteAdelicUnitaryGroup K H)
      (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)),
      toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) = A
  · obtain ⟨g₀, b₀, hA⟩ := he
    have hsym : A.toBilin'.IsSymm := hA ▸ integralBilinForm_coordinates_isSymm
      (cmAdelicLatticeIntegralTraceForm K H d hIntegral g₀)
      (cmAdelicLatticeIntegralTraceForm_isSymm K H
        (cmHermitianPositiveMatrix_isHermitian K H hH) d hIntegral g₀) b₀
    have hpos : A.toBilin'.toQuadraticMap.PosDef := hA ▸ integralBilinForm_coordinates_posDef
      (cmAdelicLatticeIntegralTraceForm K H d hIntegral g₀)
      (cmAdelicLatticeIntegralTraceForm_posDef K H hH d hd hIntegral g₀) b₀
    obtain ⟨c, _, hc⟩ := cmAdelicLattice_scalar_bound K H hH d hd hIntegral a
    have hs (j : κ) : {v : κ → ℤ | A.toBilin' v v ≤ c * A j j}.Finite :=
      integralBilinForm_finite_sublevel A.toBilin' hsym hpos (c * A j j)
    refine (Set.Finite.preimage Matrix.transpose_injective.injOn
      (Set.Finite.pi' hs)).subset ?_
    rintro M ⟨g, b, hb, rfl⟩ j
    have heq : A.toBilin' (fun i => b.repr (a • b j) i) (fun i => b.repr (a • b j) i) =
        cmAdelicLatticeIntegralTraceForm K H d hIntegral g (a • b j) (a • b j) := by
      rw [← hb, integralBilinForm_coordinates_apply]
      change cmAdelicLatticeIntegralTraceForm K H d hIntegral g
        (b.equivFun.symm (b.equivFun (a • b j)))
        (b.equivFun.symm (b.equivFun (a • b j))) = _
      rw [LinearEquiv.symm_apply_apply]
    change A.toBilin' (fun i => b.repr (a • b j) i) (fun i => b.repr (a • b j) i) ≤ c * A j j
    rw [heq, ← hb, toMatrix_apply]
    exact hc g (b j)
  · apply Set.finite_empty.subset
    rintro M ⟨g, b, hb, _⟩
    exact (he ⟨g, b, hb⟩).elim

end
end Dubon2026

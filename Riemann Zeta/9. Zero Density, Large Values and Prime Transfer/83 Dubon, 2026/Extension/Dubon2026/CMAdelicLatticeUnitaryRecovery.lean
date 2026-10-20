import Dubon2026.CMAdelicLatticeHermitianIsometry

/-! # The original rational unitary matrix recovered from equal invariants

The native equivalence between invertible matrices and linear maps
turns the recovered original Hermitian isometry into an element of the
specified rational CM unitary group. It maps the actual attached
lattices onto one another. The remaining DUB-17 recovery step is the
integral adelic level comparison using the proved lattice closure.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Equal original Gram and action invariants give an original rational unitary matrix taking one attached lattice onto the other. -/
theorem cmAdelicLattice_exists_unitary_of_invariants (H : Matrix ι ι K)
    (d : ℤ) (hd : d ≠ 0) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (hGram : toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) =
      toMatrix c (cmAdelicLatticeIntegralTraceForm K H d hIntegral h))
    (hAct : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c) :
    ∃ U : cmHermitianUnitaryGroup H,
      U.val.val.mulVec '' (numberFieldAdelicLattice K ι g.val : Set (ι → K)) =
        numberFieldAdelicLattice K ι h.val := by
  let e := cmAdelicLatticeFieldEquiv K H g h b c hAct
  let U := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hu (x : ι → K) : U.val.mulVec x = e x := by
    change U.val.mulVecLin x = e x
    rw [← Matrix.GeneralLinearGroup.toLin_apply]
    simp only [U, MulEquiv.apply_symm_apply, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv]
  have hU : U ∈ cmHermitianUnitaryGroup H := by
    change star U.val * H * U.val = H
    ext i j
    have hi := cmAdelicLatticeFieldEquiv_hermitian K H d hd hIntegral g h b c hGram hAct
      (Pi.single i 1) (Pi.single j 1)
    rw [← hu, ← hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec] at hi
    simpa only [← Pi.single_star, star_one, single_dotProduct, one_mul,
      mulVec_single_one] using hi
  refine ⟨⟨U, hU⟩, ?_⟩
  have he : U.val.mulVec = numberFieldAdelicLatticeRationalEquiv K g.val h.val b c :=
    funext hu
  rw [he]
  exact numberFieldAdelicLatticeRationalEquiv_image K g.val h.val b c

end
end Dubon2026

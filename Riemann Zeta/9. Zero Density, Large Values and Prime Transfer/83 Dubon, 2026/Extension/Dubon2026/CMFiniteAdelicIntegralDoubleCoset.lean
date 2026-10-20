import Dubon2026.CMAdelicLatticeUnitaryRecovery
import Dubon2026.NumberFieldAdelicLatticeLevelRecovery
import Dubon2026.CMFiniteAdelicIntegralLevel
import Mathlib.GroupTheory.DoubleCoset

/-! # Recovering the original unitary integral-level double coset

Equal original Gram and CM action invariants recover a rational unitary
matrix between the attached lattices. The proved level recovery puts
the relative adelic element in the actual integral unitary level. Thus
the joint invariants separate the original arithmetic double cosets,
the missing injectivity input in DUB-17's class-finiteness argument.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Equality of original Gram and action invariants recovers equality of original unitary integral-level double cosets. -/
theorem cmFiniteAdelicIntegralDoubleCoset_eq_of_invariants (H : Matrix ι ι K)
    (d : ℤ) (hd : d ≠ 0) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (hGram : toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) =
      toMatrix c (cmAdelicLatticeIntegralTraceForm K H d hIntegral h))
    (hAct : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c) :
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
      (cmFiniteAdelicUnitaryGroup_principal K H)).range
    DoubleCoset.mk Γ (cmFiniteAdelicIntegralLevel K H) g =
      DoubleCoset.mk Γ (cmFiniteAdelicIntegralLevel K H) h := by
  let φ := (cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
    (cmFiniteAdelicUnitaryGroup_principal K H)
  obtain ⟨U, hU⟩ := cmAdelicLattice_exists_unitary_of_invariants K H d hd hIntegral
    g h b c hGram hAct
  let k := h⁻¹ * φ U * g
  have hk : k ∈ cmFiniteAdelicIntegralLevel K H := by
    exact numberFieldAdelicLattice_level_recovery K ι U.val g.val h.val hU
  apply (DoubleCoset.eq φ.range (cmFiniteAdelicIntegralLevel K H) g h).mpr
  refine ⟨φ U, ⟨U, rfl⟩, k⁻¹, (cmFiniteAdelicIntegralLevel K H).inv_mem hk, ?_⟩
  simp only [k, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

end
end Dubon2026

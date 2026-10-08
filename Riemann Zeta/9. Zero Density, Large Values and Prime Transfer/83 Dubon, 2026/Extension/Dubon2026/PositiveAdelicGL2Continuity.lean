import Dubon2026.PositiveAdelicGL2CuspLift

/-! # Continuity and faithfulness of the original positive-real finite adelic GL2 cusp lift -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology

/-- Open level cosets give genuine continuity of the original cusp function on positive real times finite adelic GL2. -/
theorem positiveAdelicGL2CuspLift_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Continuous (fun p : GL(2, ℝ)⁺ × Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
      positiveAdelicGL2CuspLift N k f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨u, hu⟩ := positiveAdelicGL2Representative_spec N p.2
  let r := positiveAdelicGL2Representative N p.2
  have hc : Continuous (fun q : GL(2, ℝ)⁺ × Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
      realPositiveUnitaryLift k f ((rationalPositiveGL2ToReal r)⁻¹ * q.1)) :=
    (realPositiveUnitaryLift_continuous k (ModularFormClass.continuous f)).comp (continuous_const.mul continuous_fst)
  apply hc.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : GL(2, ℝ)⁺ × Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) in 𝓝 p,
      p.2⁻¹ * q.2 ∈ finiteAdeleGL2Gamma0 N :=
    (continuous_const.mul continuous_snd).continuousAt.eventually
      ((finiteAdeleGL2Gamma0_isOpen N).mem_nhds (by simp))
  filter_upwards [hnear] with q hq
  let v : finiteAdeleGL2Gamma0 N := ⟨p.2⁻¹ * q.2, hq⟩
  have hqf : q.2 = rationalPositiveGL2ToFinite r * (u * v).val := by
    change q.2 = rationalPositiveGL2ToFinite r * (u.val * (p.2⁻¹ * q.2))
    rw [← mul_assoc, ← hu, mul_inv_cancel_left]
  exact positiveAdelicGL2CuspLift_of_decomposition N f q.1 q.2 r (u * v) hqf

/-- The actual finite adelic construction retains the entire original classical cusp form. -/
theorem positiveAdelicGL2CuspLift_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fun f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k =>
      positiveAdelicGL2CuspLift N k f) := by
  intro f h he
  have hr : realPositiveUnitaryLift k (f : ℍ → ℂ) = realPositiveUnitaryLift k (h : ℍ → ℂ) := by
    funext g
    have ht := congrFun (congrFun he g) 1
    simpa only [positiveAdelicGL2CuspLift_one] using ht
  have hf := realPositiveUnitaryLift_injective k hr
  exact DFunLike.ext' hf

end
end Dubon2026

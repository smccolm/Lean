import Dubon2026.FiniteAdelicSL2CuspLift

/-! # Continuity and faithfulness of the original finite adelic cusp lift -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology

/-- Open level cosets give genuine continuity of the original cusp function on real times finite adelic SL2. -/
theorem finiteAdelicSL2CuspLift_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Continuous (fun p : SL(2, ℝ) × SL(2, FiniteAdeleRing ℤ ℚ) =>
      finiteAdelicSL2CuspLift N k f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨u, hu⟩ := finiteAdelicSL2Representative_spec N p.2
  let r := finiteAdelicSL2Representative N p.2
  have hc : Continuous (fun q : SL(2, ℝ) × SL(2, FiniteAdeleRing ℤ ℚ) =>
      realWeightLift k f ((rationalSL2ToReal r)⁻¹ * q.1)) :=
    (realWeightLift_continuous k (ModularFormClass.continuous f)).comp (continuous_const.mul continuous_fst)
  apply hc.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : SL(2, ℝ) × SL(2, FiniteAdeleRing ℤ ℚ) in 𝓝 p,
      p.2⁻¹ * q.2 ∈ finiteAdeleGamma0 N :=
    (continuous_const.mul continuous_snd).continuousAt.eventually
      ((finiteAdeleGamma0_isOpen N).mem_nhds (by simp))
  filter_upwards [hnear] with q hq
  let v : finiteAdeleGamma0 N := ⟨p.2⁻¹ * q.2, hq⟩
  have hqf : q.2 = rationalSL2ToFinite r * (u * v).val := by
    change q.2 = rationalSL2ToFinite r * (u.val * (p.2⁻¹ * q.2))
    rw [← mul_assoc, ← hu, mul_inv_cancel_left]
  exact finiteAdelicSL2CuspLift_of_decomposition N f q.1 q.2 r (u * v) hqf

/-- The actual finite adelic construction retains the entire original classical cusp form. -/
theorem finiteAdelicSL2CuspLift_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fun f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k =>
      finiteAdelicSL2CuspLift N k f) := by
  intro f h he
  have hr : realWeightLift k (f : ℍ → ℂ) = realWeightLift k (h : ℍ → ℂ) := by
    funext g
    have ht := congrFun (congrFun he g) 1
    simpa only [finiteAdelicSL2CuspLift_one] using ht
  have hf := realWeightLift_injective k hr
  exact DFunLike.ext' hf

end
end Dubon2026

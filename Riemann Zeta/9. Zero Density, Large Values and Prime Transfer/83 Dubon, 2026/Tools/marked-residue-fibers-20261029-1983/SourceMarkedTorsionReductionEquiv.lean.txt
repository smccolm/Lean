import Dubon2026.SourceEllipticSpecializationTorsionRange

/-! DUB-17/18 -> reverse genus -> actual finite elliptic fibers.
The native injective reduction on all N-torsion restricts to a bijection
on points of exact order N. Its surjectivity is proved from the actual
N-squared source torsion count and the native elliptic torsion theorem.
The resulting formula keeps the literal reduction map in downstream use. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticReduction

theorem exists_exactOrder_reduction_equiv
    {G K : Type*} [AddCommGroup G] [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ E₀.toAffine.Point) (hθ : Function.Injective θ)
    (hcard : Nat.card {P : G // N • P = 0} = N ^ 2) :
    ∃ ψ : {P : G // addOrderOf P = N} ≃ {Q : E₀.toAffine.Point // addOrderOf Q = N},
      ∀ P (T : Submodule.torsionBy ℤ G (N : ℤ)), T.val = P.val → (ψ P).val = θ T := by
  let t (P : {P : G // addOrderOf P = N}) : Submodule.torsionBy ℤ G (N : ℤ) :=
    ⟨P.val, by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      simpa only [P.property] using addOrderOf_nsmul_eq_zero P.val⟩
  have ht (T : Submodule.torsionBy ℤ G (N : ℤ)) : addOrderOf (θ T) = addOrderOf T.val :=
    (addOrderOf_injective θ hθ T).trans
      (addOrderOf_injective (Submodule.torsionBy ℤ G (N : ℤ)).subtype.toAddMonoidHom
        Subtype.val_injective T).symm
  let g : {P : G // addOrderOf P = N} → {Q : E₀.toAffine.Point // addOrderOf Q = N} :=
    fun P => ⟨θ (t P), (ht (t P)).trans P.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro P Q h
      have htPQ := congrArg (fun T : Submodule.torsionBy ℤ G (N : ℤ) => T.val)
        (hθ (congrArg Subtype.val h))
      exact Subtype.ext htPQ
    · intro Q
      have hkill : N • Q.val = 0 := by
        simpa only [Q.property] using addOrderOf_nsmul_eq_zero Q.val
      obtain ⟨T, hT⟩ := torsion_mem_specialization_range E₀ N hNK θ hθ hcard Q.val hkill
      have hord : addOrderOf T.val = N := (ht T).symm.trans ((congrArg addOrderOf hT).trans Q.property)
      refine ⟨⟨T.val, hord⟩, Subtype.ext ?_⟩
      exact hT
  refine ⟨Equiv.ofBijective g hg, ?_⟩
  intro P T hT
  change θ (t P) = θ T
  exact congrArg θ (Subtype.ext hT.symm)

end
end Dubon2026.SourceFunctionField.MarkedChart

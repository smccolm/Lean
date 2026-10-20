import Dubon2026.CMFiniteAdelicIntegralDoubleCoset

/-! # Finiteness of the original definite CM unitary arithmetic double cosets

Choose the proved finite joint Gram and CM action invariant for each
original double-coset representative. The proved recovery theorem makes
that assignment injective, so the original rational unitary group has
finitely many double cosets modulo the actual integral adelic level.
This removes the integral-level class-finiteness premise in DUB-17's
arithmetic auxiliary-module chain. Prescribed smaller open levels still
require the compact finite-index transfer.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual definite CM unitary arithmetic double-coset quotient at the original integral level is finite. -/
theorem cmFiniteAdelicIntegralDoubleCoset_finite (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) :
    Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
      ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
        (cmFiniteAdelicUnitaryGroup_principal K H)).range
      (cmFiniteAdelicIntegralLevel K H)) := by
  classical
  let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
    (cmFiniteAdelicUnitaryGroup_principal K H)).range
  let V := cmFiniteAdelicIntegralLevel K H
  obtain ⟨d, hd, hIntegral, T, hT⟩ := cmAdelicTraceAction_finite_invariants K H hH
  let b (g : cmFiniteAdelicUnitaryGroup K H) := Classical.choose (hT g)
  have hb (g : cmFiniteAdelicUnitaryGroup K H) :
      (toMatrix (b g) (cmAdelicLatticeIntegralTraceForm K H d hIntegral g),
        cmAdelicLatticeIntegralActions K H g (b g)) ∈ T := Classical.choose_spec (hT g)
  let f : DoubleCoset.Quotient Γ V → T := fun q =>
    ⟨(toMatrix (b q.out) (cmAdelicLatticeIntegralTraceForm K H d hIntegral q.out),
      cmAdelicLatticeIntegralActions K H q.out (b q.out)), hb q.out⟩
  apply Finite.of_injective f
  intro q r he
  have hp := congrArg Subtype.val he
  have hGram := congrArg Prod.fst hp
  have hAct := congrArg Prod.snd hp
  have hqr := cmFiniteAdelicIntegralDoubleCoset_eq_of_invariants K H d hd.ne' hIntegral
    q.out r.out (b q.out) (b r.out) hGram hAct
  exact (DoubleCoset.out_eq' Γ V q).symm.trans (hqr.trans (DoubleCoset.out_eq' Γ V r))

end
end Dubon2026

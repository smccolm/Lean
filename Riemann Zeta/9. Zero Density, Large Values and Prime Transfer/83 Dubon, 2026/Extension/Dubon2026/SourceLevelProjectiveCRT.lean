import Dubon2026.SourceLevelProjectiveLine

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> matching period dimension bounds -> original level index and genus numerics.
Selected from anthropics/fermats-last-theorem (Apache-2.0), commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the solutions
S_ModularCurve_card_projectiveLine_zmod, S_ModularCurve_dedekindPsi_prime_pow
and S_ModularCurve_dedekindPsi_mul_of_coprime. Only the necessary finite-ring
and arithmetic-function proofs are retained; the unrelated modular-polynomial
and function-field developments in the source files are omitted.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section
open Finset Nat Finset.Nat

section CRT

private def crtFst (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod M :=
  (RingHom.fst (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private def crtSnd (M N : ℕ) (h : M.Coprime N) : ZMod (M * N) →+* ZMod N :=
  (RingHom.snd (ZMod M) (ZMod N)).comp (ZMod.chineseRemainder h).toRingHom

private theorem crtFst_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtFst M N h z = (ZMod.chineseRemainder h z).1 :=
  rfl

private theorem crtSnd_apply (M N : ℕ) (h : M.Coprime N) (z : ZMod (M * N)) :
    crtSnd M N h z = (ZMod.chineseRemainder h z).2 :=
  rfl

theorem card_projectiveLine_mul (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) :
    Nat.card (ProjectiveLine (ZMod (M * N))) =
      Nat.card (ProjectiveLine (ZMod M)) * Nat.card (ProjectiveLine (ZMod N)) := by
  haveI : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  set e := ZMod.chineseRemainder h with he

  let F : ProjectiveLine (ZMod (M * N)) → ProjectiveLine (ZMod M) × ProjectiveLine (ZMod N) :=
    fun q => (ProjectiveLine.map (crtFst M N h) q, ProjectiveLine.map (crtSnd M N h) q)
  have hbij : Function.Bijective F := by
    constructor
    ·
      intro q q'
      refine Quotient.inductionOn₂ q q' ?_
      intro v w hvw
      obtain ⟨hM, hN⟩ := Prod.mk.injEq .. ▸ hvw
      obtain ⟨u₁, h1M, h2M⟩ := Quotient.exact hM
      obtain ⟨u₂, h1N, h2N⟩ := Quotient.exact hN
      have h1M' : (u₁ : ZMod M) * crtFst M N h v.1.1 = crtFst M N h w.1.1 := h1M
      have h2M' : (u₁ : ZMod M) * crtFst M N h v.1.2 = crtFst M N h w.1.2 := h2M
      have h1N' : (u₂ : ZMod N) * crtSnd M N h v.1.1 = crtSnd M N h w.1.1 := h1N
      have h2N' : (u₂ : ZMod N) * crtSnd M N h v.1.2 = crtSnd M N h w.1.2 := h2N

      have hUmul : e.symm (↑u₁, ↑u₂) * e.symm (↑u₁⁻¹, ↑u₂⁻¹) = 1 := by
        rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv]
        exact map_one e.symm
      have hUmul' : e.symm (↑u₁⁻¹, ↑u₂⁻¹) * e.symm (↑u₁, ↑u₂) = 1 :=
        (mul_comm _ _).trans hUmul

      have key : ∀ z z' : ZMod (M * N), (u₁ : ZMod M) * (e z).1 = (e z').1 →
          (u₂ : ZMod N) * (e z).2 = (e z').2 →
          e.symm (↑u₁, ↑u₂) * z = z' := by
        intro z z' hz1 hz2
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply]
        calc (((u₁ : ZMod M), (u₂ : ZMod N)) : ZMod M × ZMod N) * e z
            = (↑u₁ * (e z).1, ↑u₂ * (e z).2) := Prod.mk_mul_mk ..
          _ = ((e z').1, (e z').2) := by rw [hz1, hz2]
          _ = e z' := rfl
      exact Quotient.sound ⟨⟨e.symm (↑u₁, ↑u₂), e.symm (↑u₁⁻¹, ↑u₂⁻¹), hUmul, hUmul'⟩,
        key v.1.1 w.1.1 h1M' h1N', key v.1.2 w.1.2 h2M' h2N'⟩
    ·
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      obtain ⟨xa, ya, hab⟩ := a.2
      obtain ⟨xb, yb, hbb⟩ := b.2

      have hglue : IsCoprime (e.symm (a.1.1, b.1.1)) (e.symm (a.1.2, b.1.2)) := by
        refine ⟨e.symm (xa, xb), e.symm (ya, yb), ?_⟩
        rw [← map_mul, ← map_mul, ← map_add, Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_add_mk,
          hab, hbb]
        exact map_one e.symm
      refine ⟨⟦⟨(e.symm (a.1.1, b.1.1), e.symm (a.1.2, b.1.2)), hglue⟩⟧, ?_⟩
      have e1 : crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e2 : crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2 := by
        rw [crtFst_apply, RingEquiv.apply_symm_apply]
      have e3 : crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      have e4 : crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2 := by
        rw [crtSnd_apply, RingEquiv.apply_symm_apply]
      refine congrArg₂ Prod.mk (Quotient.sound ⟨1, ?_, ?_⟩) (Quotient.sound ⟨1, ?_, ?_⟩)
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.1, b.1.1)) = a.1.1
        rw [one_mul, e1]
      · show (1 : ZMod M) * crtFst M N h (e.symm (a.1.2, b.1.2)) = a.1.2
        rw [one_mul, e2]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.1, b.1.1)) = b.1.1
        rw [one_mul, e3]
      · show (1 : ZMod N) * crtSnd M N h (e.symm (a.1.2, b.1.2)) = b.1.2
        rw [one_mul, e4]
  rw [Nat.card_eq_of_bijective F hbij, Nat.card_prod]

end CRT


end
end Dubon2026.SourceLevelProjective

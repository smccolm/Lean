import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
namespace P2MW.S_ModularCurve_heckeAlg_smul_comm_of_forall_gen

open ModularCurve

theorem solution {J J' : Type*} [AddCommGroup J] [AddCommGroup J']
    [Module ModularCurve.HeckeAlg J] [Module ModularCurve.HeckeAlg J'] (sp : J →+ J')
    (hgen : ∀ (q : Nat.Primes) (x : J), sp (ModularCurve.heckeGen q • x) = ModularCurve.heckeGen q • sp x)
    (T : ModularCurve.HeckeAlg) (x : J) : sp (T • x) = T • sp x := by
  induction T using MvPolynomial.induction_on generalizing x with
  | C z =>
      have hz : (MvPolynomial.C z : HeckeAlg) = (z : HeckeAlg) :=
        eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg) z
      rw [hz]
      simp only [Int.cast_smul_eq_zsmul]
      exact map_zsmul sp z x
  | add T₁ T₂ ih₁ ih₂ =>
      rw [add_smul, add_smul, map_add, ih₁, ih₂]
  | mul_X T q ih =>
      rw [show (T * MvPolynomial.X q : HeckeAlg) = T * heckeGen q from rfl, mul_smul,
        mul_smul, ih, hgen]

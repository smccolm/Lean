import Dubon2026.RationalTraceExceptionalReverseLocalization

/-! The actual trace-dual Selmer condition and its exact local obstruction.
The proved original localization theorem is consumed for a specified
subspace of the genuine exceptional local H1 product. This is the
local-condition duality input to DUB-17's arithmetic patching chain;
realizing the required deformation conditions remains a separate step. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  (L : Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ))

/-- Original global dual classes whose actual restrictions annihilate the specified local condition. -/
def rationalArithmeticTraceDualSelmer :
    Submodule (ZMod q) (RationalArithmeticTraceDualH1 a q hqa σ hσ) :=
  L.dualAnnihilator.comap ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
    (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ))

/-- The original exceptional pairing restricted to the genuine dual Selmer classes. -/
def rationalArithmeticTraceDualSelmerPairing :
    rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L →ₗ[ZMod q]
      Module.Dual (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
  ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
    (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)).domRestrict
      (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L)

/-- The actual local obstruction against all original dual Selmer classes. -/
def rationalArithmeticTraceSelmerObstruction :
    RationalArithmeticExceptionalTraceH1 a q ha σ hσ →ₗ[ZMod q]
      Module.Dual (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L) :=
  (rationalArithmeticTraceDualSelmerPairing a q hqa ha σ hσ L).flip

/-- Membership retains the literal original local-pairing condition. -/
theorem rationalArithmeticTraceDualSelmer_mem_iff
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) :
    x ∈ rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L ↔
      ∀ y ∈ L, rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x) y = 0 := by
  change _ ∈ L.dualAnnihilator ↔ _
  exact Submodule.mem_dualAnnihilator _

/-- The Selmer obstruction is the original global-dual obstruction on the same global class. -/
theorem rationalArithmeticTraceSelmerObstruction_apply
    (x : RationalArithmeticExceptionalTraceH1 a q ha σ hσ)
    (d : rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L) :
    rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L x d =
      rationalArithmeticTraceH1GlobalObstruction a q hqa ha σ hσ x d.val := rfl

variable (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)
include hq2 hn

/-- The actual dual Selmer pairing image is exactly the annihilator of
the sum of the original global image and the specified local condition. -/
theorem rationalArithmeticTraceDualSelmerPairing_range :
    LinearMap.range (rationalArithmeticTraceDualSelmerPairing a q hqa ha σ hσ L) =
      (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ⊔ L).dualAnnihilator := by
  rw [rationalArithmeticTraceDualSelmerPairing, LinearMap.range_domRestrict,
    rationalArithmeticTraceDualSelmer, Submodule.map_comap_eq,
    rationalArithmeticTraceDualLocalization_range_eq_annihilator a ha q σ hn hσ hqa hq2,
    Submodule.dualAnnihilator_sup_eq]

/-- The genuine local obstruction vanishes exactly on the original
global image plus the specified local condition. No arithmetic exactness premise is supplied. -/
theorem rationalArithmeticTraceSelmerObstruction_ker :
    LinearMap.ker (rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L) =
      LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ⊔ L := by
  calc
    LinearMap.ker (rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L) =
        (LinearMap.range (rationalArithmeticTraceDualSelmerPairing a q hqa ha σ hσ L)).dualCoannihilator :=
      (LinearMap.dualCoannihilator_range_eq_ker_flip _).symm
    _ = (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ⊔ L).dualAnnihilator.dualCoannihilator :=
      congrArg Submodule.dualCoannihilator
        (rationalArithmeticTraceDualSelmerPairing_range a q hqa ha σ hσ L hq2 hn)
    _ = LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) ⊔ L :=
      Subspace.dualAnnihilator_dualCoannihilator_eq

end
end Dubon2026

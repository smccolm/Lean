import GafniTao.FordLemma63Abel

/-!
# Monotonicity of Ford's complete Vinogradov moment

The source variables for `J_{s,k}(Q)` range over `1, ..., Q`.  Inclusion of
that range into `1, ..., M` gives an injection of every zero-displacement
solution when `Q ≤ M`.  This file records that literal finite injection.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordVinogradovTupleInclude
    {s Q M : ℕ} (hQM : Q ≤ M) (x : FordVinogradovTuple s Q) :
    FordVinogradovTuple s M :=
  fun i => ⟨x i, lt_of_lt_of_le (x i).isLt hQM⟩

theorem fordVinogradovTupleInclude_injective
    {s Q M : ℕ} (hQM : Q ≤ M) :
    Function.Injective (fordVinogradovTupleInclude (s := s) hQM) := by
  intro x y hxy
  funext i
  exact Fin.ext (congrArg (fun z => (z i : ℕ)) hxy)

theorem fordVinogradovPowerVector_include
    {s k Q M : ℕ} (hQM : Q ≤ M) (x : FordVinogradovTuple s Q) :
    fordVinogradovPowerVector s k M (fordVinogradovTupleInclude hQM x) =
      fordVinogradovPowerVector s k Q x := by
  ext j
  simp only [fordVinogradovPowerVector, fordVinogradovTupleInclude]

theorem fordVinogradovMomentNat_mono
    (s k : ℕ) {Q M : ℕ} (hQM : Q ≤ M) :
    fordVinogradovMomentNat s k Q ≤ fordVinogradovMomentNat s k M := by
  let e : FordVinogradovTuple s Q → FordVinogradovTuple s M :=
    fordVinogradovTupleInclude hQM
  let F : FordVinogradovTuple s Q × FordVinogradovTuple s Q →
      FordVinogradovTuple s M × FordVinogradovTuple s M :=
    fun xy => (e xy.1, e xy.2)
  unfold fordVinogradovMomentNat fordVinogradovShiftedCountNat
    fordRepresentationCount
  apply Finset.card_le_card_of_injOn F
  · intro xy hxy
    have hxy' : fordVinogradovPowerVector s k Q xy.1 -
        fordVinogradovPowerVector s k Q xy.2 = 0 := by
      simpa using hxy
    simpa [F, e, fordVinogradovPowerVector_include hQM] using hxy'
  · intro x _hx y _hy hF
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [F, Prod.mk.injEq] at hF
    have he := fordVinogradovTupleInclude_injective (s := s) hQM
    exact Prod.ext (he hF.1) (he hF.2)

#print axioms fordVinogradovTupleInclude_injective
#print axioms fordVinogradovPowerVector_include
#print axioms fordVinogradovMomentNat_mono

end

end GafniTao

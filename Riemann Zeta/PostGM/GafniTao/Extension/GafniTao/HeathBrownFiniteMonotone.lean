import GafniTao.ClassicalBinaryHeathBrownPowered

/-!
# Monotonicity for finite Heath--Brown shapes

The powered energy packet produces subfamilies of a translated detector
colour and dyadic lengths differing by fixed factors.  These lemmas perform
the exact monotone replacements needed before exponent bookkeeping.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem approximateAdditiveQuadruples_mono_family
    {eta : Real} {W W' : Finset Real} (hWW' : W ⊆ W') :
    approximateAdditiveQuadruples eta W ⊆
      approximateAdditiveQuadruples eta W' := by
  intro q hq
  simp only [approximateAdditiveQuadruples, Finset.mem_filter,
    Finset.mem_product] at hq ⊢
  exact ⟨⟨⟨hWW' hq.1.1.1, hWW' hq.1.1.2⟩,
    ⟨hWW' hq.1.2.1, hWW' hq.1.2.2⟩⟩, hq.2⟩

theorem approxAddEnergy_mono_family
    {eta : Real} {W W' : Finset Real} (hWW' : W ⊆ W') :
    ApproxAddEnergy eta W ≤ ApproxAddEnergy eta W' :=
  Finset.card_le_card (approximateAdditiveQuadruples_mono_family hWW')

theorem heathBrownSecondMomentShape_mono
    {B : Real} {M M' : Nat} {W W' : Finset Real}
    (hB : 0 ≤ B) (hM : M ≤ M') (hW : W.card ≤ W'.card) :
    heathBrownSecondMomentShape B M W ≤
      heathBrownSecondMomentShape B M' W' := by
  unfold heathBrownSecondMomentShape
  have hCard : (W.card : Real) ≤ (W'.card : Real) := by exact_mod_cast hW
  have hMCast : (M : Real) ≤ (M' : Real) := by exact_mod_cast hM
  have hBRoot : 0 ≤ B ^ (1 / 2 : Real) := Real.rpow_nonneg hB _
  have hCardPow : (W.card : Real) ^ (5 / 4 : Real) ≤
      (W'.card : Real) ^ (5 / 4 : Real) :=
    Real.rpow_le_rpow (by positivity) hCard (by norm_num)
  gcongr

theorem heathBrownFourthMomentShape_mono
    {B : Real} {M M' : Nat} {W W' : Finset Real}
    (hB : 0 ≤ B) (hM : M ≤ M') (hW : W.card ≤ W'.card)
    (hE : ApproxAddEnergy 1 W ≤ ApproxAddEnergy 1 W') :
    heathBrownFourthMomentShape B M W ≤
      heathBrownFourthMomentShape B M' W' := by
  unfold heathBrownFourthMomentShape
  have hCard : (W.card : Real) ≤ (W'.card : Real) := by exact_mod_cast hW
  have hMCast : (M : Real) ≤ (M' : Real) := by exact_mod_cast hM
  have hECast : (ApproxAddEnergy 1 W : Real) ≤
      (ApproxAddEnergy 1 W' : Real) := by exact_mod_cast hE
  have hEPow : (ApproxAddEnergy 1 W : Real) ^ (3 / 4 : Real) ≤
      (ApproxAddEnergy 1 W' : Real) ^ (3 / 4 : Real) :=
    Real.rpow_le_rpow (by positivity) hECast (by norm_num)
  have hBRoot : 0 ≤ B ^ (1 / 2 : Real) := Real.rpow_nonneg hB _
  gcongr

theorem heathBrownFiniteFamilyBound_mono
    {epsilon C0 C2 C4 B V : Real} {M M' : Nat}
    {W W' : Finset Real}
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (hB : 0 ≤ B) (hM : M ≤ M') (hW : W.card ≤ W'.card)
    (hE : ApproxAddEnergy 1 W ≤ ApproxAddEnergy 1 W') :
    heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W ≤
      heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M' W' := by
  unfold heathBrownFiniteFamilyBound
  apply div_le_div_of_nonneg_right _ (sq_nonneg V)
  have hPow : 0 ≤ B ^ (epsilon / 2) := Real.rpow_nonneg hB _
  have hSecond := heathBrownSecondMomentShape_mono hB hM hW
  have hFourth := heathBrownFourthMomentShape_mono hB hM hW hE
  have hSecondNonneg := heathBrownSecondMomentShape_nonneg B M W hB
  have hFourthNonneg := heathBrownFourthMomentShape_nonneg B M W hB
  have hSecond'Nonneg := heathBrownSecondMomentShape_nonneg B M' W' hB
  have hFourth'Nonneg := heathBrownFourthMomentShape_nonneg B M' W' hB
  gcongr

#print axioms approxAddEnergy_mono_family
#print axioms heathBrownFiniteFamilyBound_mono

end

end GafniTao

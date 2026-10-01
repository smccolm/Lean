import TaoTrudgianYang2025.ParabolaBilinearLocalization
open Set TaoTrudgianYang2025
open scoped BigOperators
namespace HuxleyMatrixActionScratch

private theorem mobius_upper_right_large_action_comparison
    {a b c d x y lambda H : ℝ}
    (hlambda : 0 ≤ lambda)
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x| ∧ |x| ≤ H) (hy : lambda ≤ |y| ∧ |y| ≤ H)
    (hlarge : 8*H ≤ |c| *lambda^2) :
    |c| *lambda^2/2 ≤ |b| ∧ |b| ≤ (3/2)*|c| *H^2 := by
  let t := c*x+d
  have ht : 0 < t := by dsimp only [t]; linarith only [htl]
  have hH : 0 ≤ H := (abs_nonneg x).trans hx.2
  have he := (div_eq_iff ht.ne').mp hmap
  have ha : a=c*y+1/t := by
    have hid : (a-c*y)*t=1 := by
      dsimp only [t]
      nlinarith only [hdet,congrArg (fun z : ℝ => c*z) he]
    have hh : a-c*y=1/t := (eq_div_iff ht.ne').mpr hid
    linarith only [hh]
  have herrorId : b+c*x*y=t*y-x/t := by
    rw [ha] at he
    change (c*y+1/t)*x+b=y*t at he
    linear_combination he
  have htInv : 1/t ≤ 2 := by
    apply (div_le_iff₀ ht).mpr
    change (1:ℝ)/2 ≤ t at htl
    linarith only [htl]
  have herror : |b+c*x*y| ≤ 4*H := by
    rw [herrorId]
    calc
      _ ≤ |t*y|+|x/t| := abs_sub _ _
      _ = t*|y|+(1/t)*|x| := by
        rw [abs_mul,abs_div,abs_of_pos ht]
        ring
      _ ≤ 2*H+2*H := add_le_add
        (mul_le_mul htu hy.2 (abs_nonneg y) (by norm_num))
        (mul_le_mul htInv hx.2 (abs_nonneg x) (by norm_num))
      _ = _ := by ring
  have hprod : |c*x*y|=|c| *|x| *|y| := by rw [abs_mul,abs_mul]
  have hlo : |c| *lambda^2 ≤ |c*x*y| := by
    rw [hprod]
    have hh := mul_le_mul hx.1 hy.1 hlambda (abs_nonneg x)
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hhi : |c*x*y| ≤ |c| *H^2 := by
    rw [hprod]
    have hh := mul_le_mul hx.2 hy.2 (abs_nonneg y) hH
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hlowTri : |c*x*y| ≤ |b+c*x*y|+|b| := by
    calc
      _ = |(b+c*x*y)-b| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hhighTri : |b| ≤ |b+c*x*y|+|c*x*y| := by
    calc
      _ = |(b+c*x*y)-(c*x*y)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  constructor
  · nlinarith only [hlo,hlowTri,herror,hlarge]
  · nlinarith only [hlo,hhi,hhighTri,herror,hlarge]

private theorem mobius_reciprocal_entry_bounds
    {a b c d x y lambda : ℝ}
    (hlambda : 0 < lambda)
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x|) (hy : lambda ≤ |y|)
    (hnumlo : (1:ℝ)/2 ≤ (a*x+b)/x)
    (hnumhi : (a*x+b)/x ≤ 2) :
    |a| ≤ |b|/lambda+2 ∧ |d| ≤ |b|/lambda+2 := by
  have hx0 : x ≠ 0 := abs_pos.mp (hlambda.trans_le hx)
  have hy0 : y ≠ 0 := abs_pos.mp (hlambda.trans_le hy)
  have he := (div_eq_iff ht).mp hmap
  have hden : b*(1/x)+a=(a*x+b)/x := by
    field_simp [hx0]
    ring
  have hdenp : 0 < b*(1/x)+a := by rw [hden]; linarith only [hnumlo]
  have hrmap : (d*(1/x)+c)/(b*(1/x)+a)=1/y := by
    apply (div_eq_iff hdenp.ne').mpr
    field_simp [hx0,hy0]
    nlinarith only [he]
  have hrx : |1/x| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hx
  have hry : |1/y| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hy
  have hh := bourgain_mobius_entry_bounds
    (a:=d) (b:=c) (c:=b) (d:=a) (x:=1/x) (y:=1/y)
    (by nlinarith only [hdet]) (by rw [hden]; exact hnumlo)
    (by rw [hden]; exact hnumhi) hrmap hrx hry
  constructor
  · simpa only [mul_one_div] using hh.2
  · simpa only [mul_one_div] using hh.1

private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_contra! hbad
  have hgap : 0 < Z-K := sub_pos.mpr hbad
  let W := (K*Gamma+1)/(Z-K)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hh := bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]



private theorem cubic_reciprocal_majorant {K c Gamma : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcap : c ≤ Gamma) :
    (K/c)^((3:ℝ)⁻¹) ≤ K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = K^((3:ℝ)⁻¹)*c^(1-(3:ℝ)⁻¹) := by
      rw [Real.div_rpow hK hc.le,Real.rpow_sub hc,Real.rpow_one]
      ring
    _ ≤ K^((3:ℝ)⁻¹)*Gamma^(1-(3:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcap (by norm_num))
        (Real.rpow_nonneg hK _)
    _ = _ := by norm_num

private theorem resonance_matrix_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {Vbound Gamma A K B : ℝ}
    (hV : 0 ≤ Vbound) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*Vbound+5)^2)*(A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  have hw := resonance_matrix_reciprocal_sum S hV hGamma hdet hc ha hd
  have hp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
    abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
  let C := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hGamma _)) hB
  calc
    _ ≤ ∑ Mat∈S,C*(1/|(Mat 2:ℝ)|) := by
      apply Finset.sum_le_sum
      intro Mat hMat
      have hh := mul_le_mul_of_nonneg_left
        (cubic_reciprocal_majorant hK (hp Mat hMat) (hc Mat hMat).2) hA
      dsimp only [C]
      calc
        _ ≤ A*(K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/|(Mat 2:ℝ)|)+B/|(Mat 2:ℝ)| :=
          add_le_add hh le_rfl
        _ = _ := by ring
    _ = C*(∑ Mat∈S,1/|(Mat 2:ℝ)|) := (Finset.mul_sum S _ _).symm
    _ ≤ C*((2*Gamma+1)*(2*Vbound+5)^2) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by dsimp only [C]; ring



private theorem resonance_matrix_reciprocal_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma Theta A K B : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hTheta : 0 ≤ Theta)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0)
    (hb : ∀ Mat∈S, Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ Gamma)
    (hcompare : ∀ Mat∈S, |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)|)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 1:ℝ)| *X+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 1:ℝ)| *X+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*X+5)^2)*
        (A*(Theta*K)^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+Theta*B) := by
  classical
  let flip := fun Mat : Fin 4 → ℤ => (![Mat 3,Mat 2,Mat 1,Mat 0] : Fin 4 → ℤ)
  have hflip Mat : flip (flip Mat)=Mat := by
    funext i
    fin_cases i <;> rfl
  have hinj : Function.Injective flip := by
    intro Mat Mat' he
    have hh := congrArg flip he
    rw [hflip,hflip] at hh
    exact hh
  have hw := resonance_matrix_cubic_weight_sum (S.image flip)
    hX hGamma hA (mul_nonneg hTheta hK) (mul_nonneg hTheta hB)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      change Mat 3*Mat 0-Mat 2*Mat 1=1
      nlinarith only [hdet Mat hMat])
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hb Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hd Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact ha Mat hMat)
  rw [Finset.sum_image hinj.injOn] at hw
  apply le_trans _ hw
  apply Finset.sum_le_sum
  intro Mat hMat
  have hcp : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc Mat hMat)
  have hbp : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast (hb Mat hMat).1)
  have hKbound : K/|(Mat 2:ℝ)| ≤ (Theta*K)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hK]
  have hBbound : B/|(Mat 2:ℝ)| ≤ (Theta*B)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hB]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hK hcp.le) hKbound (by norm_num)) hA) hBbound

private theorem resonance_matrix_curvature_band_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ)
    {lambda H Gamma A K B : ℝ}
    (hlambda : 0 < lambda) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hx : ∀ Mat∈S, lambda ≤ |x Mat| ∧ |x Mat| ≤ H)
    (hy : ∀ Mat∈S, lambda ≤ |y Mat| ∧ |y Mat| ≤ H)
    (ht : ∀ Mat∈S, (1:ℝ)/2 ≤ (Mat 2:ℝ)*x Mat+Mat 3 ∧
      (Mat 2:ℝ)*x Mat+Mat 3 ≤ 2)
    (hmap : ∀ Mat∈S, ((Mat 0:ℝ)*x Mat+Mat 1)/
      ((Mat 2:ℝ)*x Mat+Mat 3)=y Mat)
    (hnum : ∀ Mat∈S, (1:ℝ)/2 ≤ ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ∧
      ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ≤ 2)
    (hlarge : ∀ Mat∈S, 8*H ≤ |(Mat 2:ℝ)| *lambda^2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      588*(H/lambda)^2*H^2*Gamma*
        (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  classical
  let E := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFactor {g v : ℝ} (hg : 1 ≤ g) (hv : 1 ≤ v) :
      (2*g+1)*(2*v+5)^2 ≤ 147*g*v^2 := by
    have hg0 : 0 ≤ g := zero_le_one.trans hg
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hgl : 2*g+1 ≤ 3*g := by linarith only [hg]
    have hvl : 2*v+5 ≤ 7*v := by linarith only [hv]
    have hvp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*v+5) hvl 2
    have hh := mul_le_mul hgl hvp (sq_nonneg _) (by positivity : 0 ≤ 3*g)
    nlinarith only [hh]
  by_cases hS : S.Nonempty
  · obtain ⟨Mat₀,hMat₀⟩ := hS
    have hLH : lambda ≤ H := (hx Mat₀ hMat₀).1.trans (hx Mat₀ hMat₀).2
    have hH : 0 < H := hlambda.trans_le hLH
    have hGammaOne : 1 ≤ Gamma :=
      (show (1:ℝ) ≤ |(Mat₀ 2:ℝ)| by exact_mod_cast Int.one_le_abs (hc Mat₀ hMat₀).1).trans
        (hc Mat₀ hMat₀).2
    have hcp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
      abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
    have hdetR Mat (hMat : Mat∈S) :
        (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet Mat hMat
    by_cases hWide : 1 ≤ H
    · have hentries Mat (hMat : Mat∈S) :=
        bourgain_mobius_entry_bounds (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2
          (hmap Mat hMat) (hx Mat hMat).2 (hy Mat hMat).2
      have hw := resonance_matrix_cubic_weight_sum S hH.le hGamma hA hK hB hdet hc
        (fun Mat hMat => (hentries Mat hMat).1) (fun Mat hMat => (hentries Mat hMat).2)
      have hratio : 1 ≤ H/lambda := (le_div_iff₀ hlambda).mpr (by simpa using hLH)
      have hsquare : 1 ≤ (H/lambda)^2 := by nlinarith only [hratio,sq_nonneg (H/lambda-1)]
      have hscale := mul_le_mul_of_nonneg_right hsquare (sq_nonneg H)
      have hmul := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 147*Gamma by positivity)
      have hpos : 0 ≤ (H/lambda)^2*H^2*Gamma := by positivity
      have hfac : 147*Gamma*H^2 ≤ 588*(H/lambda)^2*H^2*Gamma := by
        nlinarith only [hmul,hpos]
      exact hw.trans ((mul_le_mul_of_nonneg_right (hFactor hGammaOne hWide) hE).trans
        (mul_le_mul_of_nonneg_right hfac hE))
    · let Theta := 2*H^2
      let G := Theta*Gamma
      have hTheta : 0 < Theta := by dsimp only [Theta]; positivity
      have hG : 0 ≤ G := mul_nonneg hTheta.le hGamma
      have hcompare Mat (hMat : Mat∈S) : |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)| := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hp := mul_nonneg (abs_nonneg (Mat 2:ℝ)) (sq_nonneg H)
        dsimp only [Theta]
        nlinarith only [hh.2,hp]
      have hb Mat (hMat : Mat∈S) : Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ G := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hcpos := hcp Mat hMat
        have hp : 0 < |(Mat 1:ℝ)| :=
          (show 0 < |(Mat 2:ℝ)| *lambda^2/2 by positivity).trans_le hh.1
        refine ⟨?_,(hcompare Mat hMat).trans
          (mul_le_mul_of_nonneg_left (hc Mat hMat).2 hTheta.le)⟩
        exact_mod_cast abs_pos.mp hp
      have hentries Mat (hMat : Mat∈S) :=
        mobius_reciprocal_entry_bounds hlambda (hdetR Mat hMat)
          (show (Mat 2:ℝ)*x Mat+Mat 3 ≠ 0 by linarith only [(ht Mat hMat).1])
          (hmap Mat hMat) (hx Mat hMat).1 (hy Mat hMat).1
          (hnum Mat hMat).1 (hnum Mat hMat).2
      have hw := resonance_matrix_reciprocal_cubic_weight_sum S
        (show 0 ≤ 1/lambda by positivity) hG hTheta.le hA hK hB hdet
        (fun Mat hMat => (hc Mat hMat).1) hb hcompare
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).1)
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).2)
      have hGOne : 1 ≤ G :=
        (show (1:ℝ) ≤ |(Mat₀ 1:ℝ)| by exact_mod_cast Int.one_le_abs (hb Mat₀ hMat₀).1).trans
          (hb Mat₀ hMat₀).2
      have hInv : 1 ≤ 1/lambda := (le_div_iff₀ hlambda).mpr
        (by linarith only [hLH,le_of_not_ge hWide])
      have hpow : Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3)=Theta := by
        rw [←Real.rpow_add hTheta]
        norm_num
      have he : A*(Theta*K)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+Theta*B=Theta*E := by
        dsimp only [G,E]
        rw [Real.mul_rpow hTheta.le hK,Real.mul_rpow hTheta.le hGamma]
        calc
          _ = (Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3))*
              (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3))+Theta*B := by ring
          _ = _ := by rw [hpow]; ring
      rw [he] at hw
      calc
        _ ≤ ((2*G+1)*(2*(1/lambda)+5)^2)*(Theta*E) := hw
        _ ≤ (147*G*(1/lambda)^2)*(Theta*E) :=
          mul_le_mul_of_nonneg_right (hFactor hGOne hInv) (mul_nonneg hTheta.le hE)
        _ = _ := by dsimp only [Theta,G,E]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    change 0 ≤ 588*(H/lambda)^2*H^2*Gamma*E
    positivity

example
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ)
    {lambda H Gamma A K B : ℝ}
    (hlambda : 0 < lambda) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hx : ∀ Mat∈S, lambda ≤ |x Mat| ∧ |x Mat| ≤ H)
    (hy : ∀ Mat∈S, lambda ≤ |y Mat| ∧ |y Mat| ≤ H)
    (ht : ∀ Mat∈S, (1:ℝ)/2 ≤ (Mat 2:ℝ)*x Mat+Mat 3 ∧
      (Mat 2:ℝ)*x Mat+Mat 3 ≤ 2)
    (hmap : ∀ Mat∈S, ((Mat 0:ℝ)*x Mat+Mat 1)/
      ((Mat 2:ℝ)*x Mat+Mat 3)=y Mat)
    (hnum : ∀ Mat∈S, (1:ℝ)/2 ≤ ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ∧
      ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ≤ 2)
    (hlarge : ∀ Mat∈S, 8*H ≤ |(Mat 2:ℝ)| *lambda^2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      588*(H/lambda)^2*H^2*Gamma*
        (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) :=
  HuxleyMatrixActionScratch.resonance_matrix_curvature_band_cubic_weight_sum S x y (lambda:=lambda) (H:=H) (Gamma:=Gamma) (A:=A) (K:=K) (B:=B) hlambda hGamma hA hK hB hdet hc hx hy ht hmap hnum hlarge



private theorem cubic_matrix_source_scale
    {Z k b m U V G : ℝ}
    (hZ : 0 < Z) (hk : 0 ≤ k) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hU : 0 < U) (hV : 1 ≤ V) (hG : 0 ≤ G) (hcap : G ≤ Z/V) :
    G*(4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G) ≤
      m*Z^2*((4*k^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+b/(U*V)) := by
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hratio : 0 ≤ Z/V := (div_pos hZ hVp).le
  have hcoeff : 0 ≤ 4*m*(k*Z)^((3:ℝ)⁻¹) := by positivity
  have hinner :
      4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G ≤
      4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V) := by
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hG hcap (by norm_num)) hcoeff) le_rfl)
      (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hproduct : (k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
      k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3) := by
    rw [Real.mul_rpow hk hZ.le,Real.div_rpow hZ.le hVp.le]
    have hpow : Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3)=Z := by
      rw [←Real.rpow_add hZ]
      norm_num
    calc
      _ = k^((3:ℝ)⁻¹)*(Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3))/V^((2:ℝ)/3) := by ring
      _ = _ := by rw [hpow]
  have hVpow : V*V^((2:ℝ)/3)=V^((5:ℝ)/3) := by
    calc
      _ = V^(1:ℝ)*V^((2:ℝ)/3) := by rw [Real.rpow_one]
      _ = V^((1:ℝ)+2/3) := (Real.rpow_add hVp _ _).symm
      _ = _ := by norm_num
  have hsquare : V^((5:ℝ)/3) ≤ V^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (5:ℝ)/3 ≤ 2)
    simpa only [Real.rpow_two] using hh
  have htail : 2/V^2 ≤ 2/V^((5:ℝ)/3) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hVp _) hsquare
  calc
    _ ≤ (Z/V)*(4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V)) :=
      mul_le_mul hcap hinner (by positivity) hratio
    _ = m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^2) := by
      have he : 4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
          4*m*(k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3)) := by rw [←hproduct]; ring
      rw [he,←hVpow]
      ring
    _ ≤ m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^((5:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by ring

private theorem matrix_physical_source_scale
    {R N L U V Cfirst Cpack Cgap m H lambda : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hL : 0 < L) (hU : 0 < U) (hV : 1 ≤ V)
    (hCf : 0 ≤ Cfirst) (hCp : 0 ≤ Cpack) (hCg : 0 ≤ Cgap) (hm : 0 ≤ m) :
    let G := R^4/(6*N^2*V)
    let K := 2*Cfirst*R^4/(L^3*N^2)
    let B := 4*m*Cpack*R^4/(L^2*N^2*U)+m*Cgap*R^4/(N^2*U)+2*m*G
    588*(H/lambda)^2*H^2*G*(4*m*K^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+B) ≤
      588*m*(H/lambda)^2*H^2*(R^8/N^4)*
        ((4*(2*Cfirst/L^3)^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+
          (4*Cpack/L^2+Cgap)/(U*V)) := by
  intro G K B
  let Z := R^4/N^2
  let k := 2*Cfirst/L^3
  let b := 4*Cpack/L^2+Cgap
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hcap : G ≤ Z/V := by
    calc
      G = Z/(6*V) := by dsimp only [G,Z]; ring
      _ ≤ Z/V := div_le_div_of_nonneg_left hZ.le hVp (by linarith only [hVp])
  have hh := cubic_matrix_source_scale hZ hk hb hm hU hV hG hcap
  have hK : K=k*Z := by dsimp only [K,k,Z]; ring
  have hB : B=m*b*Z/U+2*m*G := by dsimp only [B,b,Z]; ring
  have hZsquare : Z^2=R^8/N^4 := by dsimp only [Z]; ring
  have hs := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 588*(H/lambda)^2*H^2 by positivity)
  rw [hK,hB]
  convert hs using 1
  · ring
  · rw [hZsquare]
    dsimp only [k,b]
    ring

#print axioms matrix_physical_source_scale
#print axioms cubic_matrix_source_scale
#print axioms resonance_matrix_curvature_band_cubic_weight_sum
#print axioms resonance_matrix_reciprocal_sum
#print axioms cubic_reciprocal_majorant
#print axioms resonance_matrix_cubic_weight_sum
#print axioms resonance_matrix_reciprocal_cubic_weight_sum

#print axioms mobius_reciprocal_entry_bounds
#print axioms mobius_upper_right_large_action_comparison
end HuxleyMatrixActionScratch

import TaoTrudgianYang2025.SargosDProcessGeometry
noncomputable section
namespace TaoTrudgianYang2025

/-- The new analytic beta line removes the old curvature-sign obstruction.
The assumptions are only numerical fallthroughs from genuine proved beta
bounds and the actual D scale; no analytic conclusion is assumed. -/
theorem sargosD_refined_fallthrough_curvature
    {k l a b h : ℝ}
    (hk : 0≤k) (hl : 1/2≤l)
    (ha : 1/4<a) (ha' : a<5/12)
    (hh : (4*a-1)/6≤h) (hb : b=(4*a+1+2*h)/8)
    (hD : ((2*k+4*l)*a-l)/(2+5*k+3*l)≤h)
    (hP : b<k+(l-k)*a)
    (hB : b<l-1/2+(k-l+1)*a)
    (hnew : 2/5<a →
      b < max (1/12+2*a/3) (241/1164+425*a/1164)) :
    0<1-3*a+2*h := by
  have hd : 0<2+5*k+3*l := by linarith only [hk,hl]
  have hbudget := (div_le_iff₀ hd).mp hD
  have hs : 3/4+h/2<k+l := by rw [hb] at hP hB; linarith only [hP,hB]
  by_contra hbad
  have hmu : 1-3*a+2*h≤0 := le_of_not_gt hbad
  have ha40 : 2/5≤a := by linarith only [hh,hmu]
  have hh0 : 0≤h := by linarith only [hh,ha]
  have hcoef : 0<2*a-5*h := by linarith only [hmu,ha']
  have hdelta : 0≤2*a-1+2*h := by linarith only [hh,ha40]
  have hsum := mul_lt_mul_of_pos_left hs hcoef
  have hlower := mul_le_mul_of_nonneg_left hl hdelta
  have hpoly : (5/2)*a-1/2+(a-19/4)*h-(5/2)*h^2<0 := by
    nlinarith only [hbudget,hsum,hlower]
  have hlinear : a/2-3/32<h := by
    by_contra hn
    have hlin : h≤a/2-3/32 := le_of_not_gt hn
    have hlin0 : 0≤a/2-3/32 := hh0.trans hlin
    have hsq := pow_le_pow_left₀ hh0 hlin 2
    have hprod := mul_le_mul_of_nonpos_left hlin
      (show a-19/4≤0 by linarith only [ha'])
    have hupper : a≤5/12 := ha'.le
    have hasq := pow_le_pow_left₀ (show 0≤a by linarith only [ha40]) hupper 2
    nlinarith only [hpoly,hprod,hsq,hasq,ha40]
  have hanew : 2/5<a := by linarith only [hlinear,hmu]
  have hsecondary : 1/12+2*a/3≤b := by rw [hb]; linarith only [hh]
  have hline : b<241/1164+425*a/1164 := by
    have hhnew := hnew hanew
    rcases lt_max_iff.mp hhnew with hc|hc
    · exact False.elim ((not_lt_of_ge hsecondary) hc)
    · exact hc
  rw [hb] at hline
  linarith only [hline,hlinear,hmu]

#print axioms sargosD_refined_fallthrough_curvature
end TaoTrudgianYang2025

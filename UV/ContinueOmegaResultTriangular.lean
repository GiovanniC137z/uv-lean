import UV.ContinueOmegaResultContactTheta
import UV.FurtherCurvatureLine

/-! The triangular depth law of the Wilson comparison, tested at a local
curvature contact with the actual four-dimensional spherical cutoff. -/

noncomputable section
open MeasureTheory Set UV.FurtherCurvatureShell UV.FurtherCurvatureLine UV.RevisionCurvatureDeterminant

namespace UV

def contactTriangle (L z : ℝ) := ∫ t in (0:ℝ)..L, (2/L)*(1-t/L)*Real.exp (-t*z)

theorem contact_triangle_exact {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    contactTriangle L z = 2*(L*z-1+Real.exp (-L*z))/(L*z)^2 := by
  let F := fun t : ℝ => (2/L)*((t/L-1)/z+1/(L*z^2))*Real.exp (-t*z)
  have hF (t : ℝ) : HasDerivAt F ((2/L)*(1-t/L)*Real.exp (-t*z)) t := by
    dsimp [F]
    convert (((((hasDerivAt_id t).div_const L).sub_const 1).div_const z).add_const (1/(L*z^2))
      |>.const_mul (2/L) |>.mul (((hasDerivAt_id t).neg.mul_const z).exp)) using 1
    dsimp
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((by fun_prop : Continuous (fun t : ℝ => (2/L)*(1-t/L)*Real.exp (-t*z))).intervalIntegrable 0 L)
  change _ = _ at he
  unfold contactTriangle
  rw [he]
  dsimp [F]
  simp [hL.ne']
  field_simp
  ring

private theorem contact_triangle_antitone {L : ℝ} (hL : 0 < L) : Antitone (contactTriangle L) := by
  intro a b h
  apply intervalIntegral.integral_mono_on hL.le ((by fun_prop : Continuous _).intervalIntegrable ..)
    ((by fun_prop : Continuous _).intervalIntegrable ..)
  intro t ht
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (neg_nonpos.mpr ht.1))) _
  exact mul_nonneg (by positivity) (sub_nonneg.mpr ((div_le_one hL).mpr ht.2))

theorem contact_triangle_bounds {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    contactTriangle L z ≤ 2/(L*z) ∧ (2 ≤ L*z → 1/(L*z) ≤ contactTriangle L z) := by
  rw [contact_triangle_exact hL hz]
  have hx := mul_pos hL hz
  have he : Real.exp (-L*z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos hx) hx).mpr
    nlinarith [mul_le_mul_of_nonneg_right he hx.le]
  · intro h
    apply (div_le_div_iff₀ hx (sq_pos_of_pos hx)).mpr
    nlinarith [mul_nonneg hx.le (Real.exp_pos (-L*z)).le, mul_nonneg hx.le (sub_nonneg.mpr h)]

def contactTriangularBudget (L R : ℝ) := (3/2:ℝ)*
  ∑ k ∈ sphericalModes R, contactTriangle L ((latticeFrequency k)^2)

/-- The cutoff cost grows quadratically with the physical spherical radius
at every fixed positive depth width. The constants are uniform in L once
the cutoff reaches L R² ≥ 2. -/
theorem contact_triangle_spherical_growth :
    ∃ C > 0, ∀ {L R : ℝ}, 0 < L → 2 ≤ R → 2 ≤ L*R^2 →
      (3/512:ℝ)*R^2/L ≤ contactTriangularBudget L R ∧
      contactTriangularBudget L R ≤ C*R^2/L := by
  obtain ⟨A,hA,hbound⟩ := spherical_weighted_line_bound (s := 0) (by norm_num)
  refine ⟨24*A,by positivity,?_⟩
  intro L R hL hR hLR
  have hRp : 0 < R := by linarith
  let S := sphericalModes R
  have hk k (hh : k ∈ S) : 0 < latticeFrequency k := by
    have hp := (mem_sphericalModes.mp hh).1
    exact (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (latticeHeight_ne_zero hp))).trans_le (latticeHeight_le_latticeFrequency k)
  have hcard := lattice_ball_card_lower S hR (fun _ h1 h2 => mem_sphericalModes.mpr ⟨h1,h2⟩)
  have hlo k (hh : k ∈ S) : 1/(L*R^2) ≤ contactTriangle L ((latticeFrequency k)^2) := by
    apply ((contact_triangle_bounds hL (sq_pos_of_pos hRp)).2 hLR).trans
    apply contact_triangle_antitone hL
    exact pow_le_pow_left₀ (hk k hh).le (mem_sphericalModes.mp hh).2 2
  have hhi k (hh : k ∈ S) : contactTriangle L ((latticeFrequency k)^2) ≤ 4/L*weightedLine 0 0 k := by
    apply ((contact_triangle_bounds hL (sq_pos_of_pos (hk k hh))).1).trans_eq
    simp [weightedLine,curvatureLine,curvatureCovariance]
    field_simp
    ring
  constructor
  · unfold contactTriangularBudget
    apply le_trans _ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlo) (by norm_num : (0:ℝ) ≤ 3/2))
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
    nlinarith
  · have hu := hbound (Λ := R) (ℓ := (0:ℝ)) hRp.le (by norm_num)
    simp [effectiveRadius] at hu
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hhi) (by norm_num : (0:ℝ) ≤ 3/2)).trans
    rw [←Finset.mul_sum]
    apply (le_div_iff₀ hL).mpr
    field_simp
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr (show 1 ≤ R^2 by nlinarith [sq_nonneg (R-1)])),
      mul_nonneg hA.le (sub_nonneg.mpr (show 0 ≤ 3*R^2-2*R-1 by nlinarith [sq_nonneg (R-1)]))]

end UV

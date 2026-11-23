import UV.ContinueSourceReviewDirac
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Upper and lower logarithmic cutoff growth on a genuine spatial cone for
the four-component static Dirac density described after the filled-sea test. -/

noncomputable section
open MeasureTheory Filter Set UV.FurtherOptical UV.SectorPlane
open scoped RealInnerProductSpace Topology

namespace UV

/-- The static radial density after both temporal orderings is at most a
constant times `1/r`, uniformly in the unit direction. -/
theorem sea_dirac_radial_upper {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (hmr : m ≤ r)
    (p : Spatial) (hp : 2*‖p‖ ≤ r) (n : UnitVector Spatial) :
    let k := r • (n:Spatial)
    r^2*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k)) ≤ 16*‖p‖^2/r := by
  let k := r • (n:Spatial)
  let B := energy m (k+p)*energy m k
  let A := m^2+⟪k+p,k⟫
  have hk : ‖k‖ = r := by simp [k,norm_smul,n.property,abs_of_pos hr]
  have hk' : r/2 ≤ ‖k+p‖ := by
    have h := norm_sub_le (k+p) p
    rw [add_sub_cancel_right,hk] at h
    linarith
  have hE (v : Spatial) : ‖v‖ ≤ energy m v := by
    nlinarith [energy_sq m v,energy_pos hm v,norm_nonneg v,sq_nonneg m]
  have he : r ≤ energy m k := hk ▸ hE k
  have hf : r/2 ≤ energy m (k+p) := hk'.trans (hE _)
  have hb : r^2/2 ≤ B := by
    have h := mul_le_mul hf he hr.le (energy_pos hm _).le
    dsimp only [B]; linarith
  have hB : 0 < B := mul_pos (energy_pos hm _) (energy_pos hm _)
  have hAp : 0 ≤ A := by
    have hdot := (neg_le_abs ⟪p,k⟫).trans (abs_real_inner_le_norm p k)
    rw [hk] at hdot
    dsimp only [A]
    rw [inner_add_left,real_inner_self_eq_norm_sq,hk]
    nlinarith [mul_le_mul_of_nonneg_right hp hr.le,sq_nonneg m]
  have hD : r^4/4 ≤ B*(B+A) := by
    calc r^4/4 = (r^2/2)*(r^2/2) := by ring
         _ ≤ B*(B+A) := mul_le_mul hb (by linarith) (by positivity) hB.le
  have hN : B^2-A^2 ≤ 2*r^2*‖p‖^2 := by
    have hg : B^2-A^2 = m^2*‖p‖^2+r^2*(‖p‖^2-⟪(n:Spatial),p⟫^2) := sea_dirac_gram n p
    rw [hg]
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg ⟪(n:Spatial),p⟫),
      mul_le_mul_of_nonneg_right ((sq_le_sq₀ hm.le hr.le).2 hmr) (sq_nonneg ‖p‖)]
  have hW : pairWeight m 0 p k ≤ 8*‖p‖^2/r^2 := by
    rw [sea_dirac_spin_trace hm]
    change 1-A/B ≤ _
    have hplus : 0 < B+A := by positivity
    have heq : 1-A/B=(B^2-A^2)/(B*(B+A)) := by field_simp [hB.ne',hplus.ne']; ring
    rw [heq,div_le_div_iff₀ (mul_pos hB hplus) (sq_pos_of_pos hr)]
    calc (B^2-A^2)*r^2 ≤ (2*r^2*‖p‖^2)*r^2 := by gcongr
         _ = (8*‖p‖^2)*(r^4/4) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  change r^2*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k)) ≤ _
  have hsum := add_pos (energy_pos hm (k+p)) (energy_pos hm k)
  rw [mul_div_assoc',div_le_div_iff₀ hsum hr]
  have hu := (le_div_iff₀ (sq_pos_of_pos hr)).mp hW
  nlinarith only [mul_le_mul_of_nonneg_right hu (show 0 ≤ 2*r by positivity),
    mul_le_mul_of_nonneg_left (he.trans (le_add_of_nonneg_left (energy_pos hm (k+p)).le))
      (show 0 ≤ 16*‖p‖^2 by positivity)]

/-- Two-sided cutoff bounds on any closed angular cone where the transverse
squared momentum exceeds `b > 0`. Both constants are independent of direction
and of the upper radius, which establishes logarithmic ultraviolet order. -/
theorem sea_dirac_cutoff_log_bounds {m R L b : ℝ} (hm : 0 < m) (hR : 0 < R) (hmR : m ≤ R)
    (hL : R ≤ L) (p : Spatial) (hp : 2*‖p‖ ≤ R) (n : UnitVector Spatial) (hb : 0 < b)
    (hcone : b ≤ ‖p‖^2-⟪(n:Spatial),p⟫^2) :
    let density (r : ℝ) := let k := r • (n:Spatial)
      r^2*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k))
    b/135*Real.log (L/R) ≤ (∫ r in R..L, density r)
    ∧ (∫ r in R..L, density r) ≤ (16*‖p‖^2)*Real.log (L/R) := by
  let density (r : ℝ) := let k := r • (n:Spatial)
    r^2*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k))
  have hd : Continuous density := by
    simp only [density,sea_dirac_spin_trace hm]
    have he : Continuous (energy m) := by unfold energy; fun_prop
    fun_prop (disch := first | exact fun _ => (mul_pos (energy_pos hm _) (energy_pos hm _)).ne' | exact fun _ => (add_pos (energy_pos hm _) (energy_pos hm _)).ne')
  have ht : 0 ∉ uIcc R L := by rw [uIcc_of_le hL]; exact fun h => (not_lt_of_ge h.1) hR
  have hi : IntervalIntegrable (fun r : ℝ => r⁻¹) volume R L :=
    (continuousOn_inv₀.mono (by simpa only [subset_compl_singleton_iff] using ht)).intervalIntegrable
  have hlog (C : ℝ) : (∫ u in R..L, C*u⁻¹) = C*Real.log (L/R) := by
    rw [intervalIntegral.integral_const_mul,integral_inv ht]
  change b/135*Real.log (L/R) ≤ (∫ r in R..L, density r)
    ∧ (∫ r in R..L, density r) ≤ (16*‖p‖^2)*Real.log (L/R)
  rw [←hlog,←hlog (16*‖p‖^2)]
  constructor
  · apply intervalIntegral.integral_mono_on hL (hi.const_mul _) (hd.intervalIntegrable _ _)
    intro r hr
    have h := sea_dirac_radial_lower hm (hR.trans_le hr.1) (hmR.trans hr.1) p
      (show ‖p‖ ≤ r by linarith [norm_nonneg p,hr.1]) n hb hcone
    simpa only [density,div_eq_mul_inv,mul_inv_rev, mul_assoc,mul_left_comm,mul_comm] using h
  · apply intervalIntegral.integral_mono_on hL (hd.intervalIntegrable _ _) (hi.const_mul _)
    intro r hr
    exact sea_dirac_radial_upper hm (hR.trans_le hr.1) (hmR.trans hr.1) p (hp.trans hr.1) n

end UV

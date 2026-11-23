import UV.FurtherOpticalProjector
import UV.ContinuationSectorPlane
import UV.NextOpticalCone
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Static reference density of the ordinary massive four-component Dirac sea,
expanded manuscript lines 43816–43834. The spatial direction is a genuine
unit vector on the locked carrier. The coefficient here is Euclidean. -/

noncomputable section
open MeasureTheory Filter Set UV.FurtherOptical UV.SectorPlane
open scoped RealInnerProductSpace Topology ENNReal

namespace UV

private theorem sea_dirac_diagonal {m : ℝ} (hm : 0 < m) (k : ChargeSpatialMomentum) :
    diagonal m 0 k = m := by
  simp [FurtherOptical.diagonal,energy_sq,attenuation,Real.sqrt_sq hm.le]

private theorem sea_dirac_inner {m : ℝ} (hm : 0 < m) (l k : ChargeSpatialMomentum) :
    ⟪coefficients m 0 l, coefficients m 0 k⟫ =
      (m^2+⟪l,k⟫)/(energy m l * energy m k) := by
  have h0 (v : ChargeSpatialMomentum) : coefficients m 0 v 0 = m/energy m v :=
    by change diagonal m 0 v / _ = _; rw [sea_dirac_diagonal hm]
  have hs (v : ChargeSpatialMomentum) (i : Fin 3) : coefficients m 0 v i.succ = v i / energy m v :=
    by change attenuation 0 v * _ / _ = _; simp [attenuation]
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp only [RCLike.inner_apply,conj_trivial,h0,hs]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,add_div,Finset.sum_div]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem sea_dirac_spin_trace {m : ℝ} (hm : 0 < m) (p k : ChargeSpatialMomentum) :
    pairWeight m 0 p k =
      1-(m^2+⟪k+p,k⟫)/(energy m (k+p)*energy m k) := by
  rw [pairWeight_eq_coefficientDistance hm le_rfl,norm_sub_sq_real,
    coefficients_norm_sq hm le_rfl,coefficients_norm_sq hm le_rfl,sea_dirac_inner hm]
  ring

theorem sea_dirac_gram {m r : ℝ} (n : UnitVector Spatial) (p : Spatial) :
    let k := r • (n:Spatial)
    let B := energy m (k+p) * energy m k
    let A := m^2+⟪k+p,k⟫
    B^2-A^2 = m^2*‖p‖^2 + r^2*(‖p‖^2-⟪(n:Spatial),p⟫^2) := by
  dsimp only
  rw [mul_pow,energy_sq,energy_sq,norm_add_sq_real,inner_add_left,
    real_inner_self_eq_norm_sq,real_inner_smul_left,real_inner_smul_right,
    real_inner_comm p (n:Spatial)]
  simp only [norm_smul,Real.norm_eq_abs,n.property,mul_one,sq_abs]
  ring

/-- Uniform lower bound on any closed angular cone whose transverse squared
momentum stays above a positive constant. The two static temporal orderings
and the spatial radial Jacobian are included. -/
theorem sea_dirac_radial_lower {m r b : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hmb : m ≤ r) (p : Spatial) (hp : ‖p‖ ≤ r) (n : UnitVector Spatial)
    (hb : 0 < b) (hcone : b ≤ ‖p‖^2-⟪(n:Spatial),p⟫^2) :
    let k := r • (n:Spatial)
    b/(135*r) ≤ r^2 * (2*pairWeight m 0 p k / (energy m (k+p)+energy m k)) := by
  let k := r • (n:Spatial)
  let a := m^2+⟪k+p,k⟫
  let e := energy m k
  let f := energy m (k+p)
  let B := f*e
  have hk : ‖k‖=r := by simp [k,norm_smul,abs_of_pos hr,n.property]
  have hkp : ‖k+p‖ ≤ 2*r := by linarith [norm_add_le k p]
  have he := energy_pos hm k
  have hf := energy_pos hm (k+p)
  have he2 : e ≤ 2*r := by
    have h := energy_sq m k
    rw [hk] at h
    have hms := sq_le_sq₀ hm.le hr.le |>.2 hmb
    dsimp only [e]; nlinarith [sq_nonneg r]
  have hf3 : f ≤ 3*r := by
    have h := energy_sq m (k+p)
    have hms := sq_le_sq₀ hm.le hr.le |>.2 hmb
    have hp2 := sq_le_sq₀ (norm_nonneg (k+p)) (by positivity : 0 ≤ 2*r) |>.2 hkp
    dsimp only [f]; nlinarith [sq_nonneg r]
  have hB : 0 < B := mul_pos hf he
  have hB6 : B ≤ 6*r^2 := by
    calc f*e ≤ (3*r)*(2*r) := mul_le_mul hf3 he2 he.le (by positivity)
         _ = _ := by ring
  have ha : a ≤ 3*r^2 := by
    have hs := real_inner_le_norm (k+p) k
    rw [hk] at hs
    dsimp only [a]
    nlinarith [mul_le_mul_of_nonneg_right hkp hr.le,(sq_le_sq₀ hm.le hr.le).2 hmb]
  have hg : B^2 - a^2 = m^2*‖p‖^2 + r^2*(‖p‖^2-⟪(n:Spatial),p⟫^2) :=
    sea_dirac_gram n p
  have hgram : r^2*b ≤ B^2-a^2 := by
    rw [hg]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg ‖p‖),mul_le_mul_of_nonneg_left hcone (sq_nonneg r)]
  have hplus : 0 < B+a := by
    by_contra! hh
    have hh' : a ≤ -B := by linarith
    nlinarith [sq_le_sq₀ hB.le (show 0 ≤ -a by linarith) |>.2 (show B ≤ -a by linarith),
      mul_pos (sq_pos_of_pos hr) hb]
  have hden : B*(B+a) ≤ 54*r^4 := by
    calc B*(B+a) ≤ (6*r^2)*(9*r^2) := mul_le_mul hB6 (by linarith) hplus.le (by positivity)
         _ = _ := by ring
  have hrat : pairWeight m 0 p k = (B^2-a^2)/(B*(B+a)) := by
    rw [sea_dirac_spin_trace hm]
    change 1-a/B = _
    field_simp [hB.ne',hplus.ne']; ring
  have hW : b/(54*r^2) ≤ pairWeight m 0 p k := by
    rw [hrat]
    apply (div_le_div_iff₀ (by positivity) (mul_pos hB hplus)).2
    calc b*(B*(B+a)) ≤ b*(54*r^4) := mul_le_mul_of_nonneg_left hden hb.le
         _ = (r^2*b)*(54*r^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hgram (by positivity)
  change b/(135*r) ≤ r^2*(2*pairWeight m 0 p k/(f+e))
  rw [mul_div_assoc',div_le_div_iff₀ (by positivity) (add_pos hf he)]
  have hW' := (div_le_iff₀ (by positivity : 0 < 54*r^2)).1 hW
  calc b*(f+e) ≤ b*(5*r) := mul_le_mul_of_nonneg_left (by linarith) hb.le
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hW' (show 0 ≤ 5*r by positivity)]

/-- The bare, unnormalized static response in the ordinary Dirac sea is
ultraviolet divergent for each nonzero spatial transfer and nonzero charge
readout. Its angular set has positive surface measure on the physical sphere. -/
theorem sea_dirac_static_response_diverges {m g : ℝ} (hm : 0 < m) (hg : 0 < g)
    {p : Spatial} (hp : p ≠ 0) :
    (∫⁻ k : Spatial, ENNReal.ofReal (g*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k)))) = ∞ := by
  let F (k : Spatial) := g*(2*pairWeight m 0 p k/(energy m (k+p)+energy m k))
  have hF : Measurable F := by
    simp only [F,sea_dirac_spin_trace hm,energy]
    fun_prop
  let R := max m ‖p‖
  let b := ‖p‖^2/2
  have hR : 0 < R := hm.trans_le (le_max_left _ _)
  have hb : 0 < b := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hp)) (by norm_num)
  have hc : 0 < g*b/135 := by positivity
  have hrad (n) (hn : n ∈ NextOpticalRadial.exteriorCone p) :
      (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^2)*ENNReal.ofReal (F (r • (n:Spatial)))) = ∞ := by
    let u : UnitVector Spatial := ⟨n.val,temporalRayDirection_norm n⟩
    have hang : b ≤ ‖p‖^2-⟪(u:Spatial),p⟫^2 := by
      change |⟪(u:Spatial),p⟫| < ‖p‖/2 at hn
      have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ‖p‖/2)).2 hn.le
      rw [sq_abs] at hs
      dsimp only [b]; nlinarith [sq_nonneg ‖p‖]
    apply top_unique
    calc ∞ = ENNReal.ofReal (g*b/135) * ∫⁻ r in Ioi R, ENNReal.ofReal r⁻¹ := by
           rw [temporal_lintegral_radial_inv_eq_top hR,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
         _ = ∫⁻ r in Ioi R, ENNReal.ofReal (g*b/135)*ENNReal.ofReal r⁻¹ :=
           (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
         _ ≤ ∫⁻ r in Ioi R, ENNReal.ofReal (r^2)*ENNReal.ofReal (F (r • (n:Spatial))) := by
           apply lintegral_mono_ae
           filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
           have h := sea_dirac_radial_lower hm (hR.trans hr) ((le_max_left _ _).trans hr.le)
             p ((le_max_right _ _).trans hr.le) u hb hang
           rw [← ENNReal.ofReal_mul hc.le,← ENNReal.ofReal_mul (sq_nonneg r)]
           apply ENNReal.ofReal_le_ofReal
           calc g*b/135*r⁻¹ = g*(b/(135*r)) := by ring
                _ ≤ _ := by simpa only [F,u,mul_left_comm,mul_comm,mul_assoc] using mul_le_mul_of_nonneg_left h hg.le
         _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hR.le)
  change (∫⁻ k, ENNReal.ofReal (F k)) = ∞
  rw [temporal_lintegral_spatial_polar _ hF.ennreal_ofReal]
  apply top_unique
  calc ∞ = ∫⁻ _ in NextOpticalRadial.exteriorCone p, (∞ : ℝ≥0∞) ∂(volume : Measure Spatial).toSphere := by
         rw [lintegral_const,Measure.restrict_apply_univ,ENNReal.top_mul (NextOpticalRadial.exteriorCone_positive hp)]
       _ ≤ ∫⁻ n in NextOpticalRadial.exteriorCone p, (∫⁻ r in Ioi (0:ℝ),
             ENNReal.ofReal (r^2)*ENNReal.ofReal (F (r • (n:Spatial)))) ∂(volume : Measure Spatial).toSphere := by
         apply lintegral_mono_ae
         filter_upwards [ae_restrict_mem (NextOpticalRadial.exteriorCone_measurable p)] with n hn
         exact (hrad n hn).ge
       _ ≤ _ := setLIntegral_le_lintegral _ _

/-- Exact leading spin-trace coefficient on each fixed physical spatial ray.
It also covers the parallel directions, where this leading coefficient is zero. -/
theorem sea_dirac_spin_ray_limit {m : ℝ} (hm : 0 < m) (p : Spatial) (n : UnitVector Spatial) :
    Tendsto (fun r : ℝ => r^2*pairWeight m 0 p (r • (n:Spatial))) atTop
      (𝓝 ((‖p‖^2-⟪(n:Spatial),p⟫^2)/2)) := by
  let c := ⟪(n:Spatial),p⟫
  let U (t : ℝ) := Real.sqrt (1+m^2*t^2)
  let V (t : ℝ) := Real.sqrt (1+2*c*t+(m^2+‖p‖^2)*t^2)
  let A (t : ℝ) := 1+c*t+m^2*t^2
  let B (t : ℝ) := U t * V t
  let G (t : ℝ) := (m^2*‖p‖^2*t^2+‖p‖^2-c^2)/(B t*(B t+A t))
  have cont : ContinuousAt G 0 := by
    dsimp only [G,B,A,U,V]
    fun_prop (disch := norm_num)
  have hlim := cont.tendsto.comp (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have hEq : (fun r : ℝ => G r⁻¹) =ᶠ[atTop] fun r => r^2*pairWeight m 0 p (r • (n:Spatial)) := by
    filter_upwards [eventually_gt_atTop (max 0 ‖p‖)] with r hr
    have hr' : 0 < r := (le_max_left _ _).trans_lt hr
    have hp' : ‖p‖ ≤ r := (le_max_right _ _).trans hr.le
    let k := r • (n:Spatial)
    let d := m^2 + ⟪k+p,k⟫
    let z := energy m (k+p)*energy m k
    have hk : ‖k‖ = r := by simp [k,norm_smul,abs_of_pos hr',n.property]
    have hdot : ⟪k+p,k⟫ = r^2 + r*c := by
      rw [inner_add_left,real_inner_self_eq_norm_sq,hk]
      change _+⟪p,r • (n:Spatial)⟫ = _
      rw [real_inner_smul_right,real_inner_comm (n:Spatial) p]
    have hkq : ‖k+p‖^2 = r^2+2*r*c+‖p‖^2 := by
      rw [norm_add_sq_real,hk]
      change _+2*⟪r • (n:Spatial),p⟫+_ = _
      rw [real_inner_smul_left]; ring
    have hu : U r⁻¹ = energy m k / r := by
      apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (energy_pos hm _) hr')).2
      field_simp [hr'.ne']; nlinarith [energy_sq m k]
    have hv : V r⁻¹ = energy m (k+p)/r := by
      apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos (energy_pos hm _) hr')).2
      field_simp [hr'.ne']; nlinarith [energy_sq m (k+p)]
    have hB : B r⁻¹ = z/r^2 := by dsimp only [B]; rw [hu,hv]; unfold z; ring
    have hA : A r⁻¹ = d/r^2 := by dsimp only [A,d]; rw [hdot]; field_simp; ring
    have hcz : 0 ≤ d := by
      dsimp only [d]; rw [hdot]
      have hc : -c ≤ ‖p‖ := by
        have h := abs_real_inner_le_norm (n:Spatial) p
        rw [n.property,one_mul] at h
        exact (neg_le_abs c).trans h
      nlinarith [mul_nonneg hr'.le (show 0 ≤ r+c by linarith),sq_nonneg m]
    have hz : 0 < z := mul_pos (energy_pos hm _) (energy_pos hm _)
    have hs : z+d ≠ 0 := (add_pos_of_pos_of_nonneg hz hcz).ne'
    have hg : z^2-d^2 = m^2*‖p‖^2 +r^2*(‖p‖^2-c^2) := sea_dirac_gram n p
    change G r⁻¹ = r^2*pairWeight m 0 p k
    rw [sea_dirac_spin_trace hm]
    change G r⁻¹ = r^2*(1-d/z)
    dsimp only [G]; rw [hB,hA,←add_div]
    field_simp [hr'.ne',hs,hz.ne']
    nlinarith only [hg]
  norm_num [G,B,U,V,A,c] at hlim ⊢
  exact hlim.congr' hEq

end UV

import UV.ContinueWilsonPolygonCurrent
import UV.ContinueWilsonLinkMarks
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The directional soft limit on the unit sphere, the two-incidence
cancellation of the Maxwell pole, and its bound on actual shell polygons. -/

noncomputable section

open MeasureTheory Set Filter Finset UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

theorem wilson_edge_soft_derivative (u : UnitVector ThinCurrentPlane) (x d : ThinCurrentPlane) :
    HasDerivAt (fun r : ℝ => wilsonEdgeWave (r • u.val) x d)
      (Complex.I*(⟪u.val,x+(1/2:ℝ) • d⟫:ℂ)) 0 := by
  let phase := fun s : ℝ => ⟪u.val,x+s • d⟫
  let a := fun s : ℝ => Complex.I*(phase s:ℂ)
  let F := fun r s : ℝ => Complex.exp ((r:ℂ)*a s)
  let μ := (volume : Measure ℝ).restrict (Ioc 0 1)
  have ha : Continuous a := by dsimp [a,phase]; fun_prop
  have hF (r : ℝ) : Continuous (F r) := Complex.continuous_exp.comp (continuous_const.mul ha)
  have hd (s r : ℝ) : HasDerivAt (fun t : ℝ => F t s) (F r s*a s) r := by
    simpa only [one_mul] using (((hasDerivAt_id (r:ℂ)).mul_const (a s)).cexp).comp_ofReal
  have hn (r s : ℝ) : ‖F r s‖ = 1 := by simp [F,a,Complex.norm_exp,Complex.mul_re]
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (μ := μ) (x₀ := 0)
    (F' := fun r s => F r s*a s) (bound := fun s => ‖a s‖) (ε := 1) zero_lt_one
    (Eventually.of_forall (fun r => (hF r).aestronglyMeasurable))
    ((hF 0).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (((hF 0).mul ha).aestronglyMeasurable)
    (Eventually.of_forall (fun s r _ => by rw [norm_mul,hn,one_mul]))
    (ha.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall (fun s r _ => hd s r))
  have he (r : ℝ) : wilsonEdgeWave (r • u.val) x d = ∫ s, F r s ∂μ := by
    unfold wilsonEdgeWave
    rw [intervalIntegral.integral_of_le zero_le_one]
    congr 1
    funext s
    simp only [thinPlaneWave,F,a,phase,real_inner_smul_left,Complex.ofReal_mul]
    congr 1
    ring
  have hval : (∫ s, F 0 s*a s ∂μ) = Complex.I*(⟪u.val,x+(1/2:ℝ) • d⟫:ℂ) := by
    simp only [F,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul]
    change (∫ s in Ioc (0:ℝ) 1, Complex.I * (phase s:ℂ)) = _
    rw [← intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
    have hpath : phase = fun s => ⟪u.val,x⟫+s*⟪u.val,d⟫ := by funext s; simp [phase,inner_add_right,real_inner_smul_right]
    have hsplit : (∫ s in (0:ℝ)..1, phase s) = (∫ _ in (0:ℝ)..1, ⟪u.val,x⟫) + ∫ s in (0:ℝ)..1, s*⟪u.val,d⟫ := by
      rw [hpath]
      exact intervalIntegral.integral_add ((continuous_const (y := ⟪u.val,x⟫)).intervalIntegrable (μ := volume) 0 1)
        ((continuous_id.mul (continuous_const (y := ⟪u.val,d⟫))).intervalIntegrable (μ := volume) 0 1)
    rw [hsplit,intervalIntegral.integral_mul_const]
    simp [integral_id,inner_add_right,real_inner_smul_right]
  rw [funext he,←hval]
  exact hi.2

/-- The finite polygon has a first-order soft limit along every unit
momentum direction. The coefficient uses the actual segment midpoints. -/
theorem wilson_polygon_soft_directional (u : UnitVector ThinCurrentPlane) (d : ℕ → ThinCurrentPlane)
    (N : ℕ) (closed : wilsonPolygonStart d N = 0) (j : Fin 4) :
    Tendsto (fun r : ℝ => wilsonPolygonCurrent d N (r • u.val) j/(r:ℂ)) (𝓝[≠] 0)
      (𝓝 (∑ k ∈ range N, (Complex.I*(⟪u.val,wilsonPolygonStart d k+(1/2:ℝ) • d k⟫:ℂ))*(d k j:ℂ))) := by
  have he (r : ℝ) := wilson_polygon_coordinate d N (r • u.val) j
  have hd : HasDerivAt (fun r : ℝ => wilsonPolygonCurrent d N (r • u.val) j)
      (∑ k ∈ range N, (Complex.I*(⟪u.val,wilsonPolygonStart d k+(1/2:ℝ) • d k⟫:ℂ))*(d k j:ℂ)) 0 := by
    rw [funext he]
    exact HasDerivAt.fun_sum (u := range N) (fun k _ => (wilson_edge_soft_derivative u (wilsonPolygonStart d k) (d k)).mul_const (d k j:ℂ))
  have hlim := hasDerivAt_iff_tendsto_slope.mp hd
  apply hlim.congr'
  filter_upwards with r
  simp only [slope,zero_smul,wilson_polygon_zero d N closed,PiLp.zero_apply,vsub_eq_sub,sub_zero,
    Complex.real_smul, Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

/-- On an ordinary transverse Maxwell edge, the two incident polygon
currents each supply one power of the same photon momentum. -/
theorem wilson_two_current_soft_photon (d e : ℕ → ThinCurrentPlane) (N M : ℕ)
    (hd : wilsonPolygonStart d N = 0) (he : wilsonPolygonStart e M = 0) (p : ThinCurrentPlane) :
    ‖wilsonPolygonCurrent d N p‖ * ‖wilsonPolygonCurrent e M (-p)‖ / ‖p‖^2 ≤
      wilsonPerimeter d N ^ 2 * wilsonPerimeter e M ^ 2 := by
  by_cases hp : p = 0
  · simp [hp]
    positivity
  · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hp))).mpr
    have h₁ := wilson_polygon_soft_bound d N p hd
    have h₂ := wilson_polygon_soft_bound e M (-p) he
    rw [norm_neg] at h₂
    calc
      _ ≤ (‖p‖*wilsonPerimeter d N^2)*(‖p‖*wilsonPerimeter e M^2) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = _ := by ring

theorem wilson_two_mark_polygon_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (Y : ℕ → WilsonBallSpace ι × WilsonBallSpace ι)
    (N : ℕ) (hy : ∀ k < N, ‖(Y k).1‖ ≤ 1 ∧ ‖(Y k).2‖ ≤ 1)
    (closed : wilsonPolygonStart (fun k => wilsonPairDisplacement L T (Y k)) N = 0) (p : ThinCurrentPlane) :
    ‖wilsonPolygonCurrent (fun k => wilsonPairDisplacement L T (Y k)) N p‖ ≤ min (2*L*N) (‖p‖*(2*L*N)^2) :=
  wilson_polygon_shell_bound _ N (fun k hk => wilson_pair_displacement_bound hL T _ (hy k hk).1 (hy k hk).2) closed p

end UV

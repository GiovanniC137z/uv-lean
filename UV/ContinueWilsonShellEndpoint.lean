import UV.ContinueWilsonShellSpin
import UV.ContinueWilsonSpinMatrix
import UV.ContinueWilsonNonrealPoles
import UV.ContinueWilsonChargedRim

/-! The charged pole test for the manuscript's two-mark Wilson source at
zero background, zero spatial momentum and the specified hopping weight. -/

noncomputable section

open MeasureTheory Set Filter UV.SectorPlane
open scoped Topology Matrix RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

private theorem wilson_pair_band {L : ℝ} (hL : 0 < L) (v : UnitVector (WilsonBallSpace ι)) :
    ∀ᵐ y ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)), |wilsonTimeDisplacement L v y| ≤ 2*L :=
  (ae_map_iff (wilsonTimeDisplacement_continuous L v).measurable.aemeasurable
    (measurableSet_le measurable_abs measurable_const)).mp (wilson_marginal_band hL v)

private theorem wilson_phase_bound {L : ℝ} (hL : 0 < L) (u : UnitVector (WilsonBallSpace ι)) (z : ℂ) :
    ∀ᵐ y ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)),
      ‖Complex.exp (-z*(wilsonTimeDisplacement L u y:ℂ))‖ ≤ Real.exp (‖z‖*(2*L)) := by
  filter_upwards [wilson_pair_band hL u] with y hy
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg z)

/-- Each of the sixteen integrated entries carries the same full
`I - γ·s/(2L)` and the same oscillatory continuation of the hop. -/
def wilsonShellHop (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (z : ℂ) : DiracMatrix :=
  fun i j => ∫ y, Complex.exp (-z*(wilsonTimeDisplacement L (wilsonReadoutUnit T 0) y:ℂ)) *
    ((1:DiracMatrix) i j - (1/(2*(L:ℂ))) * ∑ k : Fin 4,
      (wilsonTimeDisplacement L (wilsonReadoutUnit T k) y : ℂ) * euclideanGamma k i j)
    ∂((wilsonBallMeasure ι).prod (wilsonBallMeasure ι))

theorem wilson_shell_hop_matrix {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (z : ℂ) :
    let D := wilsonShellRestLaw hL (wilsonReadoutUnit T 0)
    wilsonShellHop L T z = D.complexMoment 0 z • 1 +
      ((1/(2*(L:ℂ))) * D.complexMoment 1 z) • chordGammaParallel := by
  let μ := (wilsonBallMeasure ι).prod (wilsonBallMeasure ι)
  let u := wilsonReadoutUnit T
  let D := wilsonShellRestLaw hL (u 0)
  let d := fun k y => (wilsonTimeDisplacement L (u k) y:ℂ)
  let F := fun y => Complex.exp (-z*d 0 y)
  have hd (k : Fin 4) : Continuous (d k) := Complex.continuous_ofReal.comp (wilsonTimeDisplacement_continuous L (u k))
  have hF : Continuous F := Complex.continuous_exp.comp (continuous_const.mul (hd 0))
  have hi : Integrable F μ :=
    (integrable_const (Real.exp (‖z‖*(2*L)))).mono' hF.aestronglyMeasurable (wilson_phase_bound hL _ z)
  have hki (k : Fin 4) : Integrable (fun y => d k y * F y) μ := by
    apply (integrable_const (2*L*Real.exp (‖z‖*(2*L)))).mono' ((hd k).mul hF).aestronglyMeasurable
    filter_upwards [wilson_pair_band hL (u k),wilson_phase_bound hL (u 0) z] with y hy hf
    rw [norm_mul]
    exact mul_le_mul (by simpa only [d,Complex.norm_real,Real.norm_eq_abs] using hy) hf (norm_nonneg _) (by positivity)
  have I₀ : (∫ y, F y ∂μ) = D.complexMoment 0 z := by
    simpa only [pow_zero,one_mul] using wilson_shell_complex_moment hL (u 0) 0 z
  have I₁ : (∫ y, d 0 y * F y ∂μ) = -D.complexMoment 1 z := by
    simpa only [pow_one,neg_one_mul] using wilson_shell_complex_moment hL (u 0) 1 z
  have Is (k : Fin 3) : (∫ y, d k.succ y * F y ∂μ) = 0 :=
    wilson_spatial_spin_zero L _ _ (wilson_readout_orthogonal T (Fin.succ_ne_zero k)) z
  ext i j
  let c := fun k : Fin 4 => (1/(2*(L:ℂ))) * euclideanGamma k i j
  change (∫ y, F y * ((1:DiracMatrix) i j - (1/(2*(L:ℂ)))*∑ k, d k y * euclideanGamma k i j) ∂μ) = _
  have hsum (y) : F y * ((1:DiracMatrix) i j - (1/(2*(L:ℂ)))*∑ k, d k y * euclideanGamma k i j) =
      F y * (1:DiracMatrix) i j - ∑ k, (d k y*F y)*c k := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    dsimp [c]
    ring
  simp only [hsum]
  have hterm (k : Fin 4) : Integrable (fun y => (d k y*F y)*c k) μ := (hki k).mul_const _
  rw [integral_sub (hi.mul_const _) (integrable_finset_sum _ (fun k _ => hterm k)),
    integral_finset_sum _ (fun k _ => hterm k),integral_mul_const,I₀]
  simp_rw [integral_mul_const]
  rw [Fin.sum_univ_succ,I₁]
  simp only [Is,zero_mul,Finset.sum_const_zero,add_zero,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  dsimp [D,u,c,chordGammaParallel]
  ring

set_option maxHeartbeats 1000000 in
/-- Direct evaluation of the inverse of the integrated Wilson matrix. -/
theorem wilson_shell_time_ordered_endpoint {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (lam : ℝ) (z : ℂ) :
    let D := wilsonShellRestLaw hL (wilsonReadoutUnit T 0)
    D.restDenominator lam 1 z ≠ 0 → D.restDenominator lam (-1) z ≠ 0 →
    ((L:ℂ)⁻¹ • ((1:DiracMatrix)-(lam:ℂ) • wilsonShellHop L T z))⁻¹ * chordGammaParallel =
      wilsonSpinMatrix (D.restEndpoint lam 1 z) (D.restEndpoint lam (-1) z) := by
  intro D hp hq
  let evaluate := fun H : DiracMatrix => ((L:ℂ)⁻¹ • ((1:DiracMatrix)-(lam:ℂ) • H))⁻¹ * chordGammaParallel
  exact (congrArg evaluate (wilson_shell_hop_matrix hL T z)).trans (D.rest_dirac_inverse_gamma lam z hp hq)

theorem wilson_shell_charged_spectrum {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    let D := wilsonShellRestLaw hL (wilsonReadoutUnit T 0)
    (∃ Mplus Mminus Zplus Zminus : ℝ, 0 < Mplus ∧ Mplus < Mminus ∧ 0 < Zplus ∧ Zminus < 0 ∧
      (∀ x : ℝ, D.restDenominator (1/4) 1 (x:ℂ) = 0 ↔ x = Mplus ∨ x = -Mminus) ∧
      (∀ x : ℝ, D.restDenominator (1/4) (-1) (x:ℂ) = 0 ↔ x = Mminus ∨ x = -Mplus) ∧
      Tendsto (fun z : ℂ => ((Mplus:ℂ)-z)*D.restEndpoint (1/4) 1 z) (𝓝[≠] (Mplus:ℂ)) (𝓝 (Zplus:ℂ)) ∧
      Tendsto (fun z : ℂ => ((Mminus:ℂ)-z)*D.restEndpoint (1/4) (-1) z) (𝓝[≠] (Mminus:ℂ)) (𝓝 (Zminus:ℂ))) ∧
    ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      {z : ℂ | z.im ≠ 0 ∧ D.restDenominator (1/4) σ z = 0 ∧
        Tendsto (D.restEndpoint (1/4) σ) (𝓝[≠] z) (Bornology.cobounded ℂ)}.Infinite := by
  intro D
  exact ⟨D.rest_poles_opposite_weights (by norm_num) (by norm_num),fun σ hs =>
    D.infinitely_many_nonreal_poles (by norm_num) (by norm_num) hs (wilson_marginal_absolutely_continuous hL _)⟩

end UV

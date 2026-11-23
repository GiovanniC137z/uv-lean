import UV.ContinueVisitSmoothTaylor
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The literal midpoint heat cost for the squared density of a smooth
normal state with a first nonzero Taylor jet. -/

noncomputable section

open MeasureTheory Set Filter Metric Asymptotics
open scoped ENNReal Topology Nat

namespace UV.ContinueVisitSmoothMidpoint

open UV.VerifyVisitCodimension UV.ContinueVisitNormalPolar
  UV.ContinueVisitTaylorDensity UV.ContinueVisitSmoothTaylor

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
def normalStateLaw (n : ℕ) (ψ : NormalCoordinates n → F) : Measure (NormalCoordinates n) :=
  (volume : Measure (NormalCoordinates n)).withDensity (fun x => ENNReal.ofReal (‖ψ x‖ ^ (2 : ℕ)))

omit [NormedSpace ℝ F] in
theorem normal_state_law_local_inverse_moment (n : ℕ) {ψ : NormalCoordinates n → F}
    (hψ : Continuous ψ) :
    (∫⁻ x in closedBall (0 : NormalCoordinates n) 1, inverseNormalPower n x ∂normalStateLaw n ψ)
        ≠ ⊤ ↔ IntegrableOn (normalTaylorWeight n ψ) (closedBall 0 1) := by
  have hI : Measurable (inverseNormalPower n) := by unfold inverseNormalPower; fun_prop
  have hD : Measurable (fun x => ENNReal.ofReal (‖ψ x‖ ^ (2 : ℕ))) :=
    (hψ.norm.pow _).measurable.ennreal_ofReal
  have hW : Measurable (normalTaylorWeight n ψ) := by unfold normalTaylorWeight; fun_prop
  unfold normalStateLaw
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hD hI isClosed_closedBall.measurableSet]
  have he (x : NormalCoordinates n) :
      (fun z => ENNReal.ofReal (‖ψ z‖ ^ (2 : ℕ))) x * inverseNormalPower n x =
        ENNReal.ofReal (normalTaylorWeight n ψ x) := by
    unfold inverseNormalPower normalTaylorWeight
    rw [← ENNReal.ofReal_mul (sq_nonneg _), div_eq_mul_inv]
  simp only [Pi.mul_apply, he]
  exact lintegral_ofReal_ne_top_iff_integrable hW.aestronglyMeasurable
    (Eventually.of_forall fun x => by unfold normalTaylorWeight; positivity)

omit [NormedSpace ℝ F] in
private theorem local_weight_integrable_on_unit_ball (n : ℕ) {ψ : NormalCoordinates n → F}
    (hψ : Continuous ψ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    IntegrableOn (normalTaylorWeight n ψ) (closedBall 0 1) ↔
      IntegrableOn (normalTaylorWeight n ψ) (ball 0 ρ) := by
  constructor
  · intro h
    exact h.mono_set (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ1))
  · intro h
    let A : Set (NormalCoordinates n) := closedBall 0 1 \ ball 0 ρ
    have hA : IsCompact A := (isCompact_closedBall (0 : NormalCoordinates n) 1).diff isOpen_ball
    have hco : ContinuousOn (normalTaylorWeight n ψ) A := by
      unfold normalTaylorWeight
      refine (hψ.norm.pow 2).continuousOn.div (continuous_norm.pow _).continuousOn ?_
      intro x hx
      have hx0 : x ≠ 0 := fun he => hx.2 (he ▸ mem_ball_self hρ)
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx0)
    refine (h.union (hco.integrableOn_compact hA)).mono_set ?_
    intro x hx
    by_cases hb : x ∈ ball (0 : NormalCoordinates n) ρ
    · exact Or.inl hb
    · exact Or.inr ⟨hx, hb⟩

/-- The codimension-b midpoint cost itself is finite precisely when
the first nonzero normal Taylor jet has degree strictly above b/2. -/
theorem smooth_normal_midpoint_finiteness_iff (n j : ℕ) {T : ℝ} (hT : 0 < T)
    {ψ : NormalCoordinates n → F} (hψ : ContDiff ℝ (j + 1 : ℕ) ψ)
    (hzero : ∀ k < j, iteratedFDeriv ℝ k ψ 0 = 0)
    (hnz : ∃ u : NormalUnit n, normalTaylorJet n j ψ u ≠ 0)
    [IsFiniteMeasure (normalStateLaw n ψ)] :
    integratedGaussianMidpoint n T (normalStateLaw n ψ) ≠ ⊤ ↔ n + 1 < 2 * j := by
  rw [gaussian_midpoint_finiteness_iff n hT, normal_state_law_local_inverse_moment n hψ.continuous]
  have ha : normalStateLaw n ψ {0} = 0 := by
    unfold normalStateLaw
    exact withDensity_absolutelyContinuous _ _ (measure_singleton _)
  simp only [ha, eq_self, true_and]
  obtain ⟨_, R, hR, hcriterion⟩ := smooth_normal_taylor_inverse_moment_iff n j hψ hzero hnz
  let ρ := min R 1
  have hρ : 0 < ρ := lt_min hR one_pos
  rw [local_weight_integrable_on_unit_ball n hψ.continuous hρ (min_le_right _ _)]
  exact hcriterion ρ hρ (min_le_left _ _)

end UV.ContinueVisitSmoothMidpoint

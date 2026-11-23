import UV.SectorPlaneStablePinch

/-! Uniform subtractions for a product of two stable-half numerators at
one simple pole. The height is common, while the two numerators and the
tested denominator may approach on different prescribed sides. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.pole_norm_independent_of_side (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height) (w : ℝ) :
    ‖diamond.poleCoefficient ε₁ h w‖ = ‖diamond.poleCoefficient ε₂ h w‖ := by
  have hn (ε : Evolution) : ‖diamond.shiftedShellCoefficient ε h w‖^2 = w^2+(h:ℝ)^2 := by
    rw [Complex.sq_norm]
    simp only [Plane.shiftedShellCoefficient,Complex.normSq_apply,Complex.add_re,Complex.I_mul_re,
      Complex.ofReal_re,Complex.ofReal_im,neg_zero,add_zero,Complex.add_im,Complex.I_mul_im,zero_add]
    linear_combination (h:ℝ)^2 * diamond.eta_sq ε
  rw [diamond.pole_coefficient_eq_inv,diamond.pole_coefficient_eq_inv,norm_inv,norm_inv]
  exact congrArg Inv.inv ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ((hn ε₁).trans (hn ε₂).symm))

/-- At the tip subtract the unit pole; at positive mass subtract exactly
the numerator at the same height and at that mass. -/
def Plane.stableShellSubtraction (diamond : Plane E) (ε : Evolution) (a m : ℝ) (h : Height) : ℂ :=
  if m = 0 then 1 else diamond.stableHalfCoefficient ε a (m^2) h

def stableSubtractionBound (a m w : ℝ) : ℝ :=
  let b := m^2/4
  if m = 0 then a * inverseRootAbs w else max (a/(2*Real.sqrt b)) (2/b)

theorem Plane.stable_subtracted_pole_bound (diamond : Plane E) (ε κ : Evolution)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (h : Height) (w : ℝ) (hne : w-m^2 ≠ 0) :
    ‖(diamond.stableHalfCoefficient ε a w h - diamond.stableShellSubtraction ε a m h) *
      diamond.poleCoefficient κ h (w-m^2)‖ ≤ stableSubtractionBound a m w := by
  rw [norm_mul,diamond.pole_norm_independent_of_side κ ε,← norm_mul]
  rcases hm.eq_or_lt with rfl | hpos
  · have hw : w ≠ 0 := by simpa using hne
    simpa [Plane.stableShellSubtraction,stableSubtractionBound,Plane.stableHalfRegular,h.property] using
      diamond.stable_half_regular_norm_bound ε ha hw h.property
  · have hb : 0 < m^2/4 := by positivity
    have hbm : 2*(m^2/4) ≤ m^2 := by nlinarith [sq_nonneg m]
    simpa only [Plane.stableShellSubtraction,stableSubtractionBound,if_neg hpos.ne',
      Plane.massiveStableRemainder,dif_pos h.property] using
      diamond.massive_stable_remainder_norm_bound ε ha hb hbm h.property w

theorem Plane.stable_subtraction_limit (diamond : Plane E) (ε : Evolution) (a m : ℝ) :
    Tendsto (diamond.stableShellSubtraction ε a m) poleBoundaryHeights (𝓝 (stableSideValue (diamond.eta ε) a (m^2))) := by
  by_cases hm : m = 0
  · subst m
    have he : stableSideValue (diamond.eta ε) a ((0:ℝ)^2) = 1 := by simp [stableSideValue,stableShellBoundaryRoot]
    rw [he]
    exact (tendsto_const_nhds (x := (1:ℂ)) (f := poleBoundaryHeights)).congr
      fun h => by simp [Plane.stableShellSubtraction]
  · have H := Complex.continuous_exp.continuousAt.tendsto.comp
        ((diamond.stable_shell_root_tendsto ε (m^2)).const_mul (-(a:ℂ)))
    apply H.congr
    intro h
    simp [Plane.stableShellSubtraction,hm,Plane.stableHalfCoefficient,h.property,
      diamond.stable_half_numerator_characters,Plane.stableShellRoot]

private theorem norm_product_subtraction (x y x₀ y₀ P : ℂ) {A B : ℝ}
    (hx : ‖x‖ ≤ 1) (hy₀ : ‖y₀‖ ≤ 1) (h₁ : ‖(x-x₀)*P‖ ≤ A) (h₂ : ‖(y-y₀)*P‖ ≤ B) :
    ‖(x*y-x₀*y₀)*P‖ ≤ A+B := by
  rw [show (x*y-x₀*y₀)*P = (x-x₀)*P*y₀ + x*((y-y₀)*P) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul _ y₀,norm_mul x]
  exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hy₀).trans h₁)
    ((mul_le_of_le_one_left (norm_nonneg _) hx).trans h₂)

theorem Plane.stable_product_subtraction_bound (diamond : Plane E) (ε₁ ε₂ κ : Evolution) {a b m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 ≤ m) (h : Height) (w : ℝ) (hne : w-m^2 ≠ 0) :
    ‖(diamond.stableHalfCoefficient ε₁ a w h * diamond.stableHalfCoefficient ε₂ b w h -
      diamond.stableShellSubtraction ε₁ a m h * diamond.stableShellSubtraction ε₂ b m h) *
      diamond.poleCoefficient κ h (w-m^2)‖ ≤ stableSubtractionBound a m w + stableSubtractionBound b m w := by
  apply norm_product_subtraction _ _ _ _ _ (diamond.stable_half_coefficient_norm_le_one ε₁ ha h.property)
    _ (diamond.stable_subtracted_pole_bound ε₁ κ ha hm h w hne) (diamond.stable_subtracted_pole_bound ε₂ κ hb hm h w hne)
  unfold Plane.stableShellSubtraction
  split_ifs
  · simp
  · exact diamond.stable_half_coefficient_norm_le_one ε₂ hb h.property

theorem stable_subtraction_test_integrable (a m : ℝ) {f : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q => ‖f q‖ * stableSubtractionBound a m (shellSquare q.1 q.2)) := by
  by_cases hm : m = 0
  · subst m
    obtain ⟨R,hR,hout⟩ := exists_cone_test_box hs.norm
    let S := Icc (-R) R ×ˢ Metric.closedBall (0 : Spatial) R
    have hS : MeasurableSet S := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
    have hbounded := hf.bounded_above_of_compact_support hs
    obtain ⟨C,hC⟩ := hbounded
    have hi : IntegrableOn (fun q : MassiveMomentum => ‖f q‖ * (a * inverseRootAbs (shellSquare q.1 q.2))) S := by
      apply ((integrableOn_inverse_root_shell_box hR).const_mul a).bdd_mul' hf.norm.aestronglyMeasurable
      exact Eventually.of_forall fun q => by simpa using hC q
    apply ((integrable_indicator_iff hS).mpr hi).congr
    refine Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ S
    · simp [hq,stableSubtractionBound]
    · simp [hq,stableSubtractionBound,hout q hq]
  · simpa only [stableSubtractionBound,if_neg hm] using
      (hf.integrable_of_hasCompactSupport hs).norm.mul_const (max (a/(2*Real.sqrt (m^2/4))) (2/(m^2/4)))

end UV.SectorPlane

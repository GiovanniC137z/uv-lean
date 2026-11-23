import UV.SectorPlaneStableProduct
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A smooth extension of the stable-half numerator from a neighborhood
of a positive mass shell. On the rest of momentum space its difference
from the prescribed branch is tested against a bounded squared pole. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

private theorem positive_square_chart {m : ℝ} (hm : 0 < m) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ (∀ w, 0 < v w) ∧
      (∀ w, |w-m^2| ≤ m^2/4 → v w = w) := by
  let β : ContDiffBump (m^2) := ⟨m^2/4,m^2/2,by positivity,by nlinarith [sq_pos_of_pos hm]⟩
  let v (w : ℝ) := β w * w + (1-β w) * m^2
  refine ⟨v,(β.contDiff.mul contDiff_id).add ((contDiff_const.sub β.contDiff).mul contDiff_const),?_,?_⟩
  · intro w
    by_cases h : β w = 0
    · simpa [v,h] using (sq_pos_of_pos hm)
    · have hd : w ∈ Metric.ball (m^2) β.rOut := β.support_eq ▸ h
      have hw : 0 < w := by
        change dist w (m^2) < m^2/2 at hd
        rw [Real.dist_eq,abs_lt] at hd
        nlinarith [sq_pos_of_pos hm,hd.1]
      exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne β.nonneg (Ne.symm h)) hw)
        (mul_nonneg (sub_nonneg.mpr β.le_one) (sq_nonneg _))
  · intro w hw
    have he := β.one_of_mem_closedBall (show w ∈ Metric.closedBall (m^2) β.rIn from by simpa only [Metric.mem_closedBall,Real.dist_eq] using hw)
    simp [v,he]

/-- The global comparison agrees with the actual positive-height branch
throughout a fixed open shell tube. Its value at all other momenta is
the stable numerator at a smooth, strictly positive invariant. -/
theorem Plane.stable_pair_massive_chart (diamond : Plane E) (ε₁ ε₂ : Evolution) (a b : ℝ)
    {m : ℝ} (hm : 0 < m) :
    ∃ (v : ℝ → ℝ) (U : ℝ → MassiveMomentum → ℂ), ContDiff ℝ 2 v ∧
      (∀ w, |w-m^2| ≤ m^2/4 → v w = w) ∧ ContDiff ℝ 2 (Function.uncurry U) ∧
      ∀ (h : Height) q, U h q = diamond.stablePairWeight ε₁ ε₂ a b h (v (shellSquare q.1 q.2)) := by
  obtain ⟨v,hv,hpos,he⟩ := positive_square_chart hm
  let Z (ε : Evolution) (x : ℝ × MassiveMomentum) :=
    ((v (shellSquare x.2.1 x.2.2) : ℝ) : ℂ) + Complex.I * ((diamond.eta ε*x.1 : ℝ) : ℂ)
  let F (ε : Evolution) (a : ℝ) (x : ℝ × MassiveMomentum) :=
    Complex.exp ((Complex.I * ((diamond.eta ε*a : ℝ):ℂ)) * principalSqrt (Z ε x))
  have hw : ContDiff ℝ 2 (fun q : MassiveMomentum => shellSquare q.1 q.2) :=
    (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  have hZ (ε : Evolution) : ContDiff ℝ 2 (Z ε) :=
    (Complex.ofRealCLM.contDiff.comp (hv.comp (hw.comp contDiff_snd))).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  have hF (ε : Evolution) (a : ℝ) : ContDiff ℝ 2 (F ε a) := by
    have hr : ContDiff ℝ 2 (fun x => principalSqrt (Z ε x)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      have hp : 0 < (Z ε x).re := by simpa [Z] using hpos (shellSquare x.2.1 x.2.2)
      exact ((principalSqrt_analyticOnNhd_rightHalfPlane (Z ε x) hp).contDiffAt.restrict_scalars ℝ).comp x (hZ ε).contDiffAt
    exact (Complex.contDiff_exp : ContDiff ℝ 2 Complex.exp).comp (contDiff_const.mul hr)
  refine ⟨v,(fun t q => F ε₁ a (t,q) * F ε₂ b (t,q)),hv,he,(hF ε₁ a).mul (hF ε₂ b),?_⟩
  intro h q
  simp only [Plane.stablePairWeight,diamond.stable_half_analytic_form,Plane.shiftedShellCoefficient,F,Z]

private theorem pole_norm_away (diamond : Plane E) (ε : Evolution) (h : Height)
    {D δ : ℝ} (hδ : 0 < δ) (hD : δ ≤ |D|) : ‖diamond.poleCoefficient ε h D‖ ≤ δ⁻¹ := by
  have hZ : |D| ≤ ‖diamond.shiftedShellCoefficient ε h D‖ := by
    simpa [Plane.shiftedShellCoefficient] using Complex.abs_re_le_norm (diamond.shiftedShellCoefficient ε h D)
  rw [diamond.pole_coefficient_eq_inv,norm_inv]
  exact inv_anti₀ hδ (hD.trans hZ)

/-- The difference from the chart has an ordinary dominated limit. This
keeps the original stable branch on and across the light cone away from
the positive-mass pole. -/
theorem Plane.stable_square_chart_remainder (diamond : Plane E) (ε : Evolution) {a b m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m) (v : ℝ → ℝ) (hv : Continuous v)
    (he : ∀ w, |w-m^2| ≤ m^2/4 → v w = w) {f : MassiveMomentum → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    let K := diamond.stablePairWeight ε ε a b
    let F := stablePairSide (diamond.eta ε) (diamond.eta ε) a b
    let w := fun q : MassiveMomentum => shellSquare q.1 q.2
    Tendsto (fun h : Height => ∫ q, f q * ((K h (w q) - K h (v (w q))) * (diamond.poleCoefficient ε h (massiveD m q))^2))
      poleBoundaryHeights (𝓝 (∫ q, f q * ((F (w q) - F (v (w q))) * ((massiveD m q : ℂ)⁻¹)^2))) := by
  intro K F w
  let δ := m^2/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hK (h : Height) (x : ℝ) : ‖K h x‖ ≤ 1 := by
    change ‖diamond.stableHalfCoefficient ε a x h * diamond.stableHalfCoefficient ε b x h‖ ≤ _
    rw [norm_mul]
    exact mul_le_one₀ (diamond.stable_half_coefficient_norm_le_one ε ha h.property) (norm_nonneg _)
      (diamond.stable_half_coefficient_norm_le_one ε hb h.property)
  have hi (h : Height) : Integrable (fun q => f q * ((K h (w q) - K h (v (w q))) * P h q ^ 2)) := by
    have hkc := diamond.stable_pair_weight_continuous ε ε a b h
    exact (hf.mul (((hkc.comp shellSquare_continuous).sub (hkc.comp (hv.comp shellSquare_continuous))).mul
      (((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)).pow 2))).integrable_of_hasCompactSupport hs.mul_right
  apply tendsto_integral_filter_of_dominated_convergence (fun q => ‖f q‖ * (2*(δ⁻¹)^2))
    (Eventually.of_forall (fun h => (hi h).aestronglyMeasurable)) _ ((hf.integrable_of_hasCompactSupport hs).norm.mul_const _)
  · exact (massiveD_nonzero_ae m).mono fun q hn => (((diamond.stable_pair_side_limit ε ε a b _).sub
      (diamond.stable_pair_side_limit ε ε a b _)).mul ((diamond.pole_coefficient_off_shell_limit ε hn).pow 2)).const_mul _
  · refine Eventually.of_forall fun h => Eventually.of_forall fun q => ?_
    by_cases hq : |w q - m^2| ≤ δ
    · rw [he _ hq]; simp; positivity
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [norm_mul,norm_pow]
      exact mul_le_mul ((norm_sub_le _ _).trans (by linarith [hK h (w q),hK h (v (w q))]))
        (pow_le_pow_left₀ (norm_nonneg _) (pole_norm_away diamond ε h hδ (le_of_not_ge hq)) 2) (by positivity) (by norm_num)

end UV.SectorPlane

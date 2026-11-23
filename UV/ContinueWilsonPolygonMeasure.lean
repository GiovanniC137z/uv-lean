import UV.ContinueWilsonPolygonInversion
import UV.ContinueWilsonGraphHopSum

/-! Relative displacement integrals for a closed charged polygon. The
closing density is evaluated at minus the sum of all its free steps.
Perimeter moments and the full ordered four-spinor trace are controlled
for every positive length, including the one-hop polygon. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators Matrix.Norms.L2Operator

namespace UV

variable {ι : Type*} [Fintype ι] {n : ℕ}

def wilsonReturnSteps (d : Fin n → OSFourSpace) : Fin (n+1) → OSFourSpace := Fin.cons (-(∑ j, d j)) d

theorem wilson_return_closed (d : Fin n → OSFourSpace) : ∑ j, wilsonReturnSteps d j = 0 := by
  rw [Fin.sum_univ_succ]
  simp [wilsonReturnSteps]

theorem wilson_return_step_continuous (j : Fin (n+1)) : Continuous (fun d => wilsonReturnSteps d j) := by
  cases j using Fin.cases with
  | zero => exact (continuous_finset_sum _ (fun j _ => continuous_apply j)).neg
  | succ j => exact continuous_apply j

def wilsonReturnPerimeter (d : Fin n → OSFourSpace) : ℝ := ∑ j, ‖wilsonReturnSteps d j‖

def wilsonReturnSpin (L : ℝ) (d : Fin n → OSFourSpace) : DiracMatrix :=
  (List.ofFn (fun j => wilsonSpinWeight L (wilsonReturnSteps d j))).prod

def wilsonReturnWeight (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (d : Fin n → OSFourSpace) : ℂ :=
  (wilsonContinuousDensity L T (-(∑ j, d j)) : ℂ) * (wilsonReturnSpin L d).trace

theorem wilson_return_weight_continuous {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Continuous (wilsonReturnWeight (n := n) L T) := by
  apply (Complex.continuous_ofReal.comp ((wilson_continuous_density_continuous hL T).comp
    (continuous_finset_sum _ (fun j _ => continuous_apply j)).neg)).mul
  apply (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.comp
  let A := fun (j : Fin (n+1)) (d : Fin n → OSFourSpace) => wilsonSpinWeight L (wilsonReturnSteps d j)
  have hm (s : List (Fin (n+1))) : Continuous (fun d => (s.map (fun j => A j d)).prod) := by
    induction s with
    | nil => exact continuous_const
    | cons j s ih => exact ((wilson_spin_weight_continuous L).comp (wilson_return_step_continuous j)).mul ih
  simpa only [wilsonReturnSpin,List.map_ofFn,Function.comp_def,A] using hm (List.ofFn id)

theorem wilson_return_perimeter_continuous : Continuous (wilsonReturnPerimeter (n := n)) :=
  continuous_finset_sum _ (fun j _ => (wilson_return_step_continuous j).norm)

/-- The pointwise bound is needed only if the closing density is nonzero.
The other steps are sampled from the two-mark law. -/
theorem wilson_return_moment_bound {L C : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (hC : 0 ≤ C) (hbound : ∀ x, wilsonContinuousDensity L T x ≤ C) (a n : ℕ) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T),
      ‖wilsonReturnWeight L T d‖ * (wilsonReturnPerimeter d)^a ≤ C * (4*2^(n+1)) * (2*L*(n+1))^a := by
  have ha (j : Fin n) := (measurePreserving_eval (fun _ : Fin n => wilsonDisplacementMeasure L T) j).quasiMeasurePreserving.ae
    (wilson_displacement_band hL.le T)
  filter_upwards [ae_all_iff.mpr ha] with d hd
  by_cases hc : 2*L < ‖-(∑ j, d j)‖
  · rw [wilsonReturnWeight,wilson_continuous_density_support hL T hc,Complex.ofReal_zero,zero_mul,norm_zero,zero_mul]
    positivity
  have hb (j : Fin (n+1)) : ‖wilsonReturnSteps d j‖ ≤ 2*L := Fin.cases (le_of_not_gt hc) hd j
  have hs : ‖wilsonReturnSpin L d‖ ≤ 2^(n+1) := by
    apply (List.norm_prod_le _).trans
    simp only [List.map_ofFn,Fin.prod_ofFn,Function.comp_apply]
    apply (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => wilson_spin_weight_opnorm hL (hb j))).trans_eq
    simp
  have hp : wilsonReturnPerimeter d ≤ 2*L*(n+1) := by
    apply (Finset.sum_le_sum (fun j _ => hb j)).trans_eq
    simp [mul_comm]
  have hw : ‖wilsonReturnWeight L T d‖ ≤ C * (4*2^(n+1)) := by
    rw [wilsonReturnWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (wilson_continuous_density_nonneg _ _ _)]
    exact mul_le_mul (hbound _) ((wilson_trace_le_opnorm _).trans (mul_le_mul_of_nonneg_left hs (by norm_num)))
      (norm_nonneg _) hC
  exact mul_le_mul hw (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hp _)
    (pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _) (by positivity)

theorem wilson_return_moment_integral {L C : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (hC : 0 ≤ C) (hbound : ∀ x, wilsonContinuousDensity L T x ≤ C) (a n : ℕ) :
    let ν := Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T)
    let f := fun d : Fin n → OSFourSpace => ‖wilsonReturnWeight L T d‖ * (wilsonReturnPerimeter d)^a
    Integrable f ν ∧ (∫ d, f d ∂ν) ≤ C * (4*2^(n+1)) * (2*L*(n+1))^a := by
  dsimp only
  have h := wilson_return_moment_bound hL T hC hbound a n
  have hn (d : Fin n → OSFourSpace) : 0 ≤ ‖wilsonReturnWeight L T d‖*(wilsonReturnPerimeter d)^a :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _)
  have hInt := (integrable_const (μ := Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T))
    (C * (4*2^(n+1)) * (2*L*(n+1))^a)).mono'
    (((wilson_return_weight_continuous hL T).norm.mul (wilson_return_perimeter_continuous.pow a)).aestronglyMeasurable)
    (h.mono fun d hd => (Real.norm_of_nonneg (hn d)).le.trans hd)
  exact ⟨hInt,(integral_mono_ae hInt (integrable_const _) h).trans_eq (by simp)⟩

theorem wilson_return_all_lengths {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (a : ℕ) :
    Summable (fun n : ℕ => lam^(n+1) * ∫ d, ‖wilsonReturnWeight L T d‖ * (wilsonReturnPerimeter d)^a
      ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T)) := by
  obtain ⟨C,hC,hbound⟩ := wilson_continuous_density_bounded hL T
  have hs := (wilson_marked_hop_summable a hlam hl).mul_left (8*lam*C*(2*L)^a)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hlam _) (integral_nonneg fun d =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _))) _ hs
  intro n
  apply (mul_le_mul_of_nonneg_left (wilson_return_moment_integral hL T hC hbound a n).2 (pow_nonneg hlam _)).trans_eq
  simp only [pow_succ,mul_pow]
  ring

end UV

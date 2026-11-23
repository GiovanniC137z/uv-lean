import UV.ContinueWilsonSpinNorm

/-! The absolute integral of the ordered four-spinor trace around a
nonempty charged circulation, uniformly in every momentum transfer. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace UV

variable {ι : Type*} [Fintype ι]

theorem wilson_spin_matrix_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) : Integrable (wilsonSpinHopMatrix L T us) := by
  have he (p : OSFourSpace) : wilsonSpinHopMatrix L T us p =
      ∑ i : Fin 4, ∑ j : Fin 4, wilsonMarkedSpinHop L T us i j p • Matrix.single i j (1:ℂ) := by
    simp only [Matrix.smul_single,smul_eq_mul,mul_one,←wilson_spin_hop_entry hL T us p]
    exact Matrix.matrix_eq_sum_single _
  change Integrable (fun p => wilsonSpinHopMatrix L T us p)
  simp_rw [he]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (wilson_marked_spin_hop_integrable hL T us i j).smul_const _))

structure WilsonCirculationHop where
  marks : WilsonDirections
  transfer : OSFourSpace

def wilsonCirculationWord (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    List WilsonCirculationHop → OSFourSpace → DiracMatrix
  | [], _ => 1
  | h :: hs, p => wilsonSpinHopMatrix L T h.marks (p+h.transfer) * wilsonCirculationWord L T hs p

def wilsonCirculationCost (L : ℝ) : List WilsonCirculationHop → ℝ
  | [] => 1
  | h :: hs => (2*(2*L)^h.marks.length) * wilsonCirculationCost L hs

theorem wilson_circulation_cost {L : ℝ} (hs : List WilsonCirculationHop) :
    wilsonCirculationCost L hs = 2^hs.length * (2*L)^(hs.map (fun h => h.marks.length)).sum := by
  induction hs with
  | nil => simp [wilsonCirculationCost]
  | cons h hs ih => simp only [wilsonCirculationCost,ih,List.length_cons,List.map_cons,List.sum_cons,pow_succ,pow_add]; ring

theorem wilson_circulation_uniform {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (hs : List WilsonCirculationHop) (p : OSFourSpace) : ‖wilsonCirculationWord L T hs p‖ ≤ wilsonCirculationCost L hs := by
  induction hs with
  | nil => simp [wilsonCirculationWord,wilsonCirculationCost]
  | cons h hs ih =>
    apply (norm_mul_le _ _).trans
    exact mul_le_mul (wilson_spin_hop_opnorm hL T _ _) ih (norm_nonneg _) (by positivity)

private theorem wilson_shifted_matrix_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (h : WilsonCirculationHop) : Integrable (fun p => wilsonSpinHopMatrix L T h.marks (p+h.transfer)) :=
  ((measurePreserving_add_right (volume : Measure OSFourSpace) h.transfer).integrable_comp_emb
    (Homeomorph.addRight h.transfer).measurableEmbedding).mpr (wilson_spin_matrix_integrable hL T h.marks)

private theorem wilson_word_aemeasurable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (hs : List WilsonCirculationHop) : AEStronglyMeasurable (wilsonCirculationWord L T hs) volume := by
  induction hs with
  | nil => exact aestronglyMeasurable_const
  | cons h hs ih => exact (wilson_shifted_matrix_integrable hL T h).aestronglyMeasurable.mul ih

theorem wilson_circulation_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (h : WilsonCirculationHop) (hs : List WilsonCirculationHop) : Integrable (wilsonCirculationWord L T (h::hs)) := by
  apply ((wilson_shifted_matrix_integrable hL T h).norm.mul_const (wilsonCirculationCost L hs)).mono'
    (wilson_word_aemeasurable hL T _) (Eventually.of_forall fun p => ?_)
  apply (norm_mul_le _ _).trans
  exact mul_le_mul_of_nonneg_left (wilson_circulation_uniform hL T hs p) (norm_nonneg _)

theorem wilson_charged_trace_absolute_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (h : WilsonCirculationHop) (hs : List WilsonCirculationHop) :
    Integrable (fun p => (wilsonCirculationWord L T (h::hs) p).trace) ∧
      (∫ p, ‖(wilsonCirculationWord L T (h::hs) p).trace‖) ≤
        4 * (∫ p, ‖wilsonSpinHopMatrix L T h.marks p‖) * wilsonCirculationCost L hs := by
  have hi := wilson_circulation_integrable hL T h hs
  have htr := (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.integrable_comp hi
  refine ⟨htr,?_⟩
  have hmain := (wilson_shifted_matrix_integrable hL T h).norm
  calc
    _ ≤ ∫ p, 4 * (‖wilsonSpinHopMatrix L T h.marks (p+h.transfer)‖ * wilsonCirculationCost L hs) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ((hmain.mul_const _).const_mul 4)
      apply Eventually.of_forall
      intro p
      apply (wilson_trace_le_opnorm _).trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (norm_mul_le _ _).trans
      exact mul_le_mul_of_nonneg_left (wilson_circulation_uniform hL T hs p) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul,integral_mul_const,
        (measurePreserving_add_right (volume : Measure OSFourSpace) h.transfer).integral_comp
          (Homeomorph.addRight h.transfer).measurableEmbedding (fun p => ‖wilsonSpinHopMatrix L T h.marks p‖)]
      ring

end UV

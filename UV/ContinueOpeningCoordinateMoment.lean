import UV.ContinueOpeningCoordinatePVM
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The first spectral moment has exactly the maximal coordinate
multiplication domain. The reverse implication uses convergence in measure
and a subsequence converging almost everywhere. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem opening_coordinate_approx_error (t : ℝ) (n : ℕ) : |sourceCoordinateApprox n t-t| ≤ |t| := by
  have h := SimpleFunc.edist_approxOn_le measurable_id (mem_univ (0:ℝ)) t n
  have hh := ENNReal.toReal_mono (edist_ne_top _ _) h
  simpa only [sourceCoordinateApprox,←dist_edist,id_eq,Real.dist_eq,zero_sub,abs_neg] using hh

theorem opening_coordinate_approx_ae (w : X → ℝ) (hw : Measurable w) (n : ℕ) (ψ : Lp ℂ 2 μ) :
    (sourceSimpleSpectralIntegral (openingCoordinatePVM μ w hw) (sourceCoordinateApprox n) ψ : X → ℂ)
      =ᵐ[μ] fun u => (sourceCoordinateApprox n (w u):ℂ)*ψ u := by
  rw [←sourceBorel_simple (openingCoordinateBorel μ w hw)]
  exact opening_coordinate_action_ae μ w hw (sourceBoundedBorel_simple _) ψ

/-- Norm convergence of the simple spectral first moments is equivalent
to pointwise multiplication in L², with the maximal square-integrable
domain. This includes the Gaussian coordinate times any real scale. -/
theorem opening_coordinate_moment_iff (w : X → ℝ) (hw : Measurable w) (ψ η : Lp ℂ 2 μ) :
    Tendsto (fun n => sourceSimpleSpectralIntegral (openingCoordinatePVM μ w hw)
      (sourceCoordinateApprox n) ψ) atTop (𝓝 η) ↔
      (η : X → ℂ) =ᵐ[μ] fun u => (w u:ℂ)*ψ u := by
  let F := fun n => sourceSimpleSpectralIntegral (openingCoordinatePVM μ w hw) (sourceCoordinateApprox n) ψ
  let a := fun n u => (sourceCoordinateApprox n (w u):ℂ)*ψ u
  have he n : (F n : X → ℂ) =ᵐ[μ] a n := opening_coordinate_approx_ae μ w hw n ψ
  have ha u : Tendsto (fun n => a n u) atTop (𝓝 ((w u:ℂ)*ψ u)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (sourceCoordinateApprox_tendsto (w u))).mul_const _
  constructor
  · intro h
    obtain ⟨k,hk,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp h).exists_seq_tendsto_ae
    filter_upwards [hlim,ae_all_iff.mpr he] with u hu he'
    exact tendsto_nhds_unique hu ((ha u).comp hk.tendsto_atTop |>.congr (fun n => (he' (k n)).symm))
  · intro h
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable η)).mp (Lp.memLp η)
    apply opening_l2_dominated μ atTop F η a _ he h (fun u => ‖η u‖^2) hi
    · intro n
      filter_upwards [h] with u hu
      dsimp [a]
      rw [←sub_mul,hu,norm_mul,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_right (opening_coordinate_approx_error (w u) n) (norm_nonneg _)
    · exact ae_of_all _ ha

/-- The graph representation needed by SourceSpectralResolution holds at
every vector of the maximal domain, including for unbounded coordinates. -/
def openingCoordinateResolution (w : X → ℝ) (hw : Measurable w) :
    SourceSpectralResolution (sourceL2Multiplier μ (fun u => (w u:ℂ))) where
  measure := openingCoordinatePVM μ w hw
  calculus := openingCoordinateBorel μ w hw
  moment ψ η := by
    rw [opening_coordinate_moment_iff]
    let T := sourceL2Multiplier μ (fun u => (w u:ℂ))
    constructor
    · intro h
      obtain ⟨a,ha,hb⟩ := (T.mem_graph_iff).mp h
      have he := sourceL2Multiplier_coe μ (fun u => (w u:ℂ)) a
      change (a : Lp ℂ 2 μ) = ψ at ha
      change T a = η at hb
      rw [←ha,←hb]
      exact he
    · intro h
      have hm : ψ ∈ T.domain := MemLp.ae_eq h (Lp.memLp η)
      apply (T.mem_graph_iff).mpr
      refine ⟨⟨ψ,hm⟩,rfl,Lp.ext ?_⟩
      exact (sourceL2Multiplier_coe μ _ ⟨ψ,hm⟩).trans h.symm

end UV

import UV.UnboundedSourceBorel

/-! Bounded local spectral functions construct the actual domains of the
coordinate operator and its inverse. No cut-domain conclusion is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sourceResolution_moment {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K) (x y : H) :
    (x,y) ∈ K.graph ↔ Tendsto
      (fun n => R.calculus.operator (sourceCoordinateApprox n) x) atTop (𝓝 y) := by
  simpa only [sourceBorel_simple] using R.moment x y

/-- The moment-domain characterization and generic bounded-pointwise
normality derive local coordinate multiplication on its actual domain. -/
theorem sourceResolution_borel_graph {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K)
    (f : ℝ → ℝ) (hf : sourceBoundedBorel f)
    (huf : sourceBoundedBorel (fun u => u*f u)) (x : H) :
    (R.calculus.operator f x,R.calculus.operator (fun u => u*f u) x) ∈ K.graph := by
  obtain ⟨C,hC,hbound⟩ := huf.2
  have hlim := R.calculus.strong_limit (fun n u => sourceCoordinateApprox n u*f u)
    (fun u => u*f u) (2*C)
    (fun n => (sourceCoordinateApprox n).measurable.mul hf.1) huf.1 (by positivity)
    (fun n u => by
      calc
        |sourceCoordinateApprox n u*f u| = |sourceCoordinateApprox n u| * |f u| := abs_mul _ _
        _ ≤ (2* |u|)* |f u| := mul_le_mul_of_nonneg_right (sourceCoordinateApprox_bound n u) (abs_nonneg _)
        _ = 2* |u*f u| := by rw [abs_mul]; ring
        _ ≤ 2*C := mul_le_mul_of_nonneg_left (hbound u) (by norm_num))
    (fun u => (sourceCoordinateApprox_tendsto u).mul_const (f u)) x
  apply (sourceResolution_moment R _ _).mpr
  apply hlim.congr
  intro n
  rw [R.calculus.mul _ _ (sourceBoundedBorel_simple _) hf]
  rfl

def sourceCutCoordinate (n : ℕ) : ℝ → ℝ := (sourcePositiveSpectralCut n).indicator id

def sourceCutReciprocal (n : ℕ) : ℝ → ℝ :=
  (sourcePositiveSpectralCut n).indicator (fun u : ℝ => u⁻¹)

theorem sourceCutCoordinate_borel (n : ℕ) : sourceBoundedBorel (sourceCutCoordinate n) := by
  refine ⟨measurable_id.indicator (sourcePositiveSpectralCut_measurable n),
    (n : ℝ)+1,by positivity,fun u => ?_⟩
  by_cases hu : u ∈ sourcePositiveSpectralCut n
  · have hpos : 0 < u := (inv_pos.mpr (by positivity : 0 < (n : ℝ)+1)).trans_le hu.1
    simpa only [sourceCutCoordinate, indicator_of_mem hu, id_eq, abs_of_pos hpos] using hu.2
  · simp only [sourceCutCoordinate,indicator_of_notMem hu,abs_zero]
    positivity

theorem sourceCutReciprocal_borel (n : ℕ) : sourceBoundedBorel (sourceCutReciprocal n) := by
  refine ⟨measurable_inv.indicator (sourcePositiveSpectralCut_measurable n),
    (n : ℝ)+1,by positivity,fun u => ?_⟩
  by_cases hu : u ∈ sourcePositiveSpectralCut n
  · have hpos : 0 < u := (inv_pos.mpr (by positivity : 0 < (n : ℝ)+1)).trans_le hu.1
    simp only [sourceCutReciprocal,indicator_of_mem hu,abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_comm₀ hpos (by positivity)).mpr hu.1
  · simp only [sourceCutReciprocal,indicator_of_notMem hu,abs_zero]
    positivity

theorem sourceCut_coordinate_indicator (n : ℕ) :
    (fun u : ℝ => u*(sourcePositiveSpectralCut n).indicator (fun _ => (1 : ℝ)) u) =
      sourceCutCoordinate n := by
  funext u
  by_cases hu : u ∈ sourcePositiveSpectralCut n <;> simp [sourceCutCoordinate,hu]

theorem sourceCut_coordinate_reciprocal (n : ℕ) :
    (fun u : ℝ => u*sourceCutReciprocal n u) =
      (sourcePositiveSpectralCut n).indicator (fun _ => (1 : ℝ)) := by
  funext u
  by_cases hu : u ∈ sourcePositiveSpectralCut n
  · have hpos : 0 < u := (inv_pos.mpr (by positivity : 0 < (n : ℝ)+1)).trans_le hu.1
    simp [sourceCutReciprocal,hu,hpos.ne']
  · simp [sourceCutReciprocal,hu]

/-- Every bounded positive spectral cut lies in the actual unbounded
kinetic domain, with its bounded coordinate restriction explicitly built. -/
theorem sourceResolution_cut_graph {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K)
    (n : ℕ) (x : H) :
    (R.measure.projection (sourcePositiveSpectralCut n) x,
      R.calculus.operator (sourceCutCoordinate n) x) ∈ K.graph := by
  have hg := sourceResolution_borel_graph R
    ((sourcePositiveSpectralCut n).indicator (fun _ => (1 : ℝ)))
    (sourceBoundedBorel_indicator (sourcePositiveSpectralCut_measurable n))
    (by rw [sourceCut_coordinate_indicator]; exact sourceCutCoordinate_borel n) x
  simpa only [R.calculus.indicator _ (sourcePositiveSpectralCut_measurable n),
    sourceCut_coordinate_indicator] using hg

/-- The actual bounded reciprocal spectral integral is an inverse on each
cut; hence the cut lies in ran(K), including when K has no global gap. -/
theorem sourceResolution_reciprocal_graph {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K)
    (n : ℕ) (x : H) :
    (R.calculus.operator (sourceCutReciprocal n) x,
      R.measure.projection (sourcePositiveSpectralCut n) x) ∈ K.graph := by
  have hg := sourceResolution_borel_graph R (sourceCutReciprocal n) (sourceCutReciprocal_borel n)
    (by rw [sourceCut_coordinate_reciprocal];
        exact sourceBoundedBorel_indicator (sourcePositiveSpectralCut_measurable n)) x
  simpa only [sourceCut_coordinate_reciprocal,
    R.calculus.indicator _ (sourcePositiveSpectralCut_measurable n)] using hg

theorem sourceSimpleSpectralIntegral_commute_projection (P Q : SourcePVM H)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B → Commute (P.projection A) (Q.projection B))
    (f : SimpleFunc ℝ ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    Commute (sourceSimpleSpectralIntegral P f) (Q.projection s) := by
  unfold sourceSimpleSpectralIntegral
  apply Commute.sum_left
  intro v hv
  exact (hPQ _ _ (f.measurableSet_fiber v) hs).smul_left _

/-- The supplied resolution of bounded F recovers F by its actual finite
spectral moments. Projection commutation therefore transfers to F itself. -/
theorem sourceResolution_bounded_commutes_projection (F : H →L[ℂ] H)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (Q : SourcePVM H)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B →
      Commute (RF.measure.projection A) (Q.projection B))
    (s : Set ℝ) (hs : MeasurableSet s) : Commute F (Q.projection s) := by
  have hlim : ∀ x : H, Tendsto
      (fun n => sourceSimpleSpectralIntegral RF.measure (sourceCoordinateApprox n) x) atTop (𝓝 (F x)) := by
    intro x
    exact (RF.moment _ _).mp ((F.toLinearMap.toPMap ⊤).mem_graph ⟨x,Submodule.mem_top⟩)
  exact source_strongLimit_commute hlim
    (fun n => sourceSimpleSpectralIntegral_commute_projection RF.measure Q hPQ _ s hs)

theorem sourceResolution_graph_commutes_bounded {K : H →ₗ.[ℂ] H} (RK : SourceSpectralResolution K)
    (A : H →L[ℂ] H)
    (hA : ∀ s, MeasurableSet s → Commute (RK.measure.projection s) A) :
    sourceGraphCommutes K A := by
  apply source_graph_commutes_of_moment_limits K
    (fun n => sourceSimpleSpectralIntegral RK.measure (sourceCoordinateApprox n)) A RK.moment
  intro n
  unfold sourceSimpleSpectralIntegral
  apply Commute.sum_left
  intro v hv
  exact (hA _ ((sourceCoordinateApprox n).measurableSet_fiber v)).smul_left _

/-- The source's separate spectral-projection commutation derives actual
bounded-F/unbounded-K domain intertwining, not an assumed covariance law. -/
theorem sourceResolution_strong_commutes_graph (F : H →L[ℂ] H) {K : H →ₗ.[ℂ] H}
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
    (hPQ : ∀ A B, MeasurableSet A → MeasurableSet B →
      Commute (RF.measure.projection A) (RK.measure.projection B)) :
    sourceGraphCommutes K F :=
  sourceResolution_graph_commutes_bounded RK F (fun s hs =>
    (sourceResolution_bounded_commutes_projection F RF RK.measure hPQ s hs).symm)

end UV

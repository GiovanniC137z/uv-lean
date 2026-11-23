import UV.ContinueNaimarkColumns
import UV.ContinueClosingPositiveMoment

/-! Setwise equality of the given matrix measure with the compression of
the real-coordinate projection measure, including its off-diagonal complex
entries. -/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal InnerProductSpace ComplexConjugate Matrix

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The sesquilinear integral of two square-integrable weighted slot columns. -/
theorem closing_weighted_columns_integrable_pairing (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (i j : ι) (a w : ℝ → ℂ)
    (u η : Lp ℂ 2 (closingNaimarkMeasure M))
    (hu : (u : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] fun p => a p.2 * closingColumnValue M i p)
    (hη : (η : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] fun p => w p.2 * closingColumnValue M j p) :
    Integrable (fun x => (star (a x) * w x) * closingMatrixDensity M x i j) (closingControlMeasure M) ∧
    ⟪u, η⟫_ℂ =
      ∫ x, (star (a x) * w x) * closingMatrixDensity M x i j ∂closingControlMeasure M := by
  let F (p : ι × ℝ) := (star (a p.2) * w p.2) * (star (closingColumnValue M i p) * closingColumnValue M j p)
  have hae : (fun p => ⟪u p, η p⟫_ℂ) =ᵐ[closingNaimarkMeasure M] F := by
    filter_upwards [hu,hη] with p h₁ h₂
    rw [h₁,h₂,RCLike.inner_apply, map_mul]
    dsimp [F]
    ring
  have hF : Integrable F (closingNaimarkMeasure M) := (L2.integrable_inner u η).congr hae
  have hslice (k : ι) : Integrable (fun x => F (k,x)) (closingControlMeasure M) :=
    (Measure.ae_count_iff.mp hF.prod_right_ae) k
  have heq : (fun x => ∑ k, F (k,x)) =ᵐ[closingControlMeasure M]
      (fun x => (star (a x) * w x) * closingMatrixDensity M x i j) := by
    filter_upwards [closing_naimark_factor_gram M hM] with x hx
    change (∑ k, (star (a x) * w x) * (star (closingNaimarkFactor M x k i) * closingNaimarkFactor M x k j)) = _
    rw [← Finset.mul_sum, ← hx]
    rfl
  refine ⟨(integrable_finset_sum _ (fun k _ => hslice k)).congr heq, ?_⟩
  rw [L2.inner_def, integral_congr_ae hae]
  change (∫ p, F p ∂Measure.count.prod (closingControlMeasure M)) = _
  rw [integral_prod _ hF, integral_count, ← integral_finset_sum _ (fun k _ => hslice k)]
  exact integral_congr_ae heq

theorem closing_weighted_columns_pairing (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (i j : ι) (a w : ℝ → ℂ)
    (u η : Lp ℂ 2 (closingNaimarkMeasure M))
    (hu : (u : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] fun p => a p.2 * closingColumnValue M i p)
    (hη : (η : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] fun p => w p.2 * closingColumnValue M j p) :
    ⟪u, η⟫_ℂ =
      ∫ x, (star (a x) * w x) * closingMatrixDensity M x i j ∂closingControlMeasure M :=
  (closing_weighted_columns_integrable_pairing M hM i j a w u η hu hη).2

/-- A weighted column in L² has exactly the expected matrix-measure
pairing. The weight may be complex and need not be bounded. -/
theorem closing_column_weight_pairing (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (i j : ι) (w : ℝ → ℂ)
    (η : Lp ℂ 2 (closingNaimarkMeasure M))
    (hη : (η : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] fun p => w p.2 * closingColumnValue M j p) :
    ⟪closingNaimarkColumn M hM i, η⟫_ℂ =
      ∫ x, w x * closingMatrixDensity M x i j ∂closingControlMeasure M := by
  have hi : (closingNaimarkColumn M hM i : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M]
      (fun p => (1 : ℂ) * closingColumnValue M i p) := by simpa using closing_naimark_column_ae M hM i
  simpa only [star_one,one_mul] using
    closing_weighted_columns_pairing M hM i j (fun _ => 1) w _ η hi hη

def closingNaimarkPVM (M : Matrix ι ι (ComplexMeasure ℝ)) :=
  openingCoordinatePVM (closingNaimarkMeasure M) Prod.snd measurable_snd

theorem closing_column_projected_pairing (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (i j : ι) {s : Set ℝ} (hs : MeasurableSet s) :
    ⟪closingNaimarkColumn M hM i, (closingNaimarkPVM M).projection s (closingNaimarkColumn M hM j)⟫_ℂ =
      M i j s := by
  let b := closingNaimarkColumn M hM j
  let μ := closingNaimarkMeasure M
  let w := s.indicator (fun _ => (1 : ℂ))
  have he : ((closingNaimarkPVM M).projection s b : ι × ℝ → ℂ) =ᵐ[μ]
    fun p => w p.2 * closingColumnValue M j p := by
    filter_upwards [opening_coordinate_projection_ae μ Prod.snd measurable_snd hs b,
      closing_naimark_column_ae M hM j] with p hp hb
    change (closingNaimarkPVM M).projection s b p = (Prod.snd ⁻¹' s).indicator b p at hp
    rw [hp]
    by_cases h : p.2 ∈ s <;> simp [w, b, h,hb]
  rw [closing_column_weight_pairing M hM i j w _ he]
  have hw (x : ℝ) : w x * closingMatrixDensity M x i j =
      s.indicator (fun t => closingMatrixDensity M t i j) x := by
    by_cases h : x ∈ s <;> simp [w,h]
  simp_rw [hw]
  rw [integral_indicator hs, closing_density_entry_integral M i j hs]

theorem closing_columns_orthonormal (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M)
    (hn : (fun i j => M i j univ) = (1 : Matrix ι ι ℂ)) :
    Orthonormal ℂ (closingNaimarkColumn M hM) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have he := closing_column_projected_pairing M hM i j MeasurableSet.univ
  rw [(closingNaimarkPVM M).univ, ContinuousLinearMap.one_apply] at he
  exact he.trans (congrArg (fun A : Matrix ι ι ℂ => A i j) hn)

end UV.SectorPlane

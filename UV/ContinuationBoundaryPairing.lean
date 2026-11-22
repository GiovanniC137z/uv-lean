import UV.UnboundedSourcePVM
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The actual positive paired Hilbert–Schmidt coefficient on a fixed
momentum plane and its countable matrix-entry moment decomposition. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace UV.ContinuationBoundary

variable {V H I O : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup I] [InnerProductSpace ℂ I] [CompleteSpace I]
  [NormedAddCommGroup O] [InnerProductSpace ℂ O] [CompleteSpace O]

/-- Normalized, strongly countably additive orthogonal spectral projections
for the commuting displacement observable on the fixed plane. -/
structure DisplacementPVM (V H : Type*) [MeasurableSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  projection : Set V → H →L[ℂ] H
  empty : projection ∅ = 0
  univ : projection univ = 1
  selfAdjoint : ∀ s, MeasurableSet s → IsSelfAdjoint (projection s)
  inter : ∀ s t, MeasurableSet s → MeasurableSet t →
    projection (s ∩ t) = projection s * projection t
  countable : ∀ s : ℕ → Set V, (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ x : H,
    HasSum (fun n => projection (s n) x) (projection (⋃ n, s n) x)

/-- Scalar overlaps are actual complex measures, obtained by applying the
continuous inner functional to strong countable additivity of the PVM. -/
def overlapMeasure (P : DisplacementPVM V H) (y x : H) : ComplexMeasure V := by
  classical
  refine
    { measureOf' := fun s => if MeasurableSet s then ⟪y, P.projection s x⟫_ℂ else 0
      empty' := by simp [P.empty]
      not_measurable' := fun _ h => if_neg h
      m_iUnion' := ?_ }
  intro s hs hd
  simpa only [if_pos (MeasurableSet.iUnion hs), if_pos (hs _)] using
    (innerSL ℂ y).hasSum (P.countable s hs hd x)

theorem overlapMeasure_apply (P : DisplacementPVM V H) (y x : H)
    {s : Set V} (hs : MeasurableSet s) :
    overlapMeasure P y x s = ⟪y, P.projection s x⟫_ℂ := by
  classical
  exact if_pos hs

private theorem projection_inner (P : DisplacementPVM V H) {s t : Set V}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (x y : H) :
    ⟪P.projection s y, P.projection t x⟫_ℂ = ⟪y, P.projection (s ∩ t) x⟫_ℂ := by
  have he : (P.projection s).adjoint = P.projection s := (P.selfAdjoint s hs).star_eq
  rw [← he, ContinuousLinearMap.adjoint_inner_left, P.inter s t hs ht,
    ContinuousLinearMap.mul_apply]

private theorem projection_square_sum_le (P : DisplacementPVM V H)
    {ι : Type*} (F : Finset ι) (s : ι → Set V) (hs : ∀ i ∈ F, MeasurableSet (s i))
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (s i) (s j)) (x : H) :
    ∑ i ∈ F, ‖P.projection (s i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let p : ι → H := fun i => P.projection (s i) x
  let u := ∑ i ∈ F, p i
  have hself (i : ι) (hi : i ∈ F) : ⟪p i, p i⟫_ℂ = ⟪x, p i⟫_ℂ := by
    simpa only [p, inter_self] using projection_inner P (hs i hi) (hs i hi) x x
  have horth (i : ι) (hi : i ∈ F) (j : ι) (hj : j ∈ F) (hne : i ≠ j) :
      ⟪p i, p j⟫_ℂ = 0 := by
    rw [show ⟪p i, p j⟫_ℂ = _ from projection_inner P (hs i hi) (hs j hj) x x,
      (hd i hi j hj hne).inter_eq, P.empty]
    simp
  have hu : ⟪u, u⟫_ℂ = ∑ i ∈ F, ⟪p i, p i⟫_ℂ := by
    simp only [u, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single_of_mem i hi (fun j hj hji => horth j hj i hi hji)
  have hux : ⟪x, u⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [hu]
    simp only [u, inner_sum]
    exact Finset.sum_congr rfl (fun i hi => (hself i hi).symm)
  have hsq (z : H) : ⟪z, z⟫_ℂ = ((‖z‖ ^ 2 : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K z : ⟪z, z⟫_ℂ = (‖z‖ : ℂ) ^ 2).trans
      (Complex.ofReal_pow ‖z‖ 2).symm
  have husq : ‖u‖ ^ 2 = ∑ i ∈ F, ‖p i‖ ^ 2 := by
    simp_rw [hsq, ← Complex.ofReal_sum] at hu
    exact Complex.ofReal_injective hu
  have hnorm := norm_inner_le_norm (𝕜 := ℂ) x u
  rw [hux, hsq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hnorm
  have hle : ‖u‖ ≤ ‖x‖ := by
    by_cases h : ‖u‖ = 0
    · rw [h]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_right (by simpa [pow_two] using hnorm) (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
  change (∑ i ∈ F, ‖p i‖ ^ 2) ≤ ‖x‖ ^ 2
  rw [← husq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Uniform finite-partition variation bound for the actual overlap measure. -/
theorem overlap_variation_bound (P : DisplacementPVM V H)
    {ι : Type*} (F : Finset ι) (s : ι → Set V) (hs : ∀ i ∈ F, MeasurableSet (s i))
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (s i) (s j)) (x y : H) :
    ∑ i ∈ F, ‖overlapMeasure P y x (s i)‖ ≤ ‖y‖ * ‖x‖ := by
  have h₁ : ∑ i ∈ F, ‖overlapMeasure P y x (s i)‖ ≤
      ∑ i ∈ F, ‖P.projection (s i) y‖ * ‖P.projection (s i) x‖ := by
    apply Finset.sum_le_sum
    intro i hi
    rw [overlapMeasure_apply P y x (hs i hi)]
    have he := projection_inner P (hs i hi) (hs i hi) x y
    rw [inter_self] at he
    rw [← he]
    exact norm_inner_le_norm _ _
  refine h₁.trans ?_
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun i => ‖P.projection (s i) y‖) (fun i => ‖P.projection (s i) x‖)
  rw [← sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow]
  apply h₂.trans
  exact mul_le_mul (projection_square_sum_le P F s hs hd y)
    (projection_square_sum_le P F s hs hd x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (sq_nonneg _)


variable {ι κ : Type*}

omit [CompleteSpace O] in
private theorem basis_square_norm (b : HilbertBasis κ ℂ O) (v : O) :
    ENNReal.ofReal (‖v‖ ^ 2) = ∑' j, ENNReal.ofReal (‖⟪b j, v⟫_ℂ‖ ^ 2) := by
  have h : HasSum (fun j => ‖b.repr v j‖ ^ 2) (‖v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map]
      using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr v)
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  simp_rw [b.repr_apply_apply]

/-- The squared Hilbert–Schmidt norm as a positive sum in the chosen
orthonormal input basis, allowing an infinite sum before imposing membership. -/
def hilbertSchmidtSquare (b : HilbertBasis ι ℂ I) (A : I →L[ℂ] O) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)

/-- The actual paired coefficient, including the left and right boundary
maps on their respective sides of the full spectral phase operator. -/
def pairedCoefficient (u : HilbertBasis ι ℂ I) (W : I →L[ℂ] H)
    (L : H →L[ℂ] O) (U : V → H →L[ℂ] H) (k : V) : ℝ≥0∞ :=
  hilbertSchmidtSquare u (L.comp ((U k).comp W))

def pairedEntry (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (U : V → H →L[ℂ] H)
    (k : V) (i : ι) (j : κ) : ℂ :=
  ⟪L.adjoint (v j), U k (W (u i))⟫_ℂ

omit [MeasurableSpace V] [CompleteSpace I] in
theorem paired_coefficient_entry_expansion (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (U : V → H →L[ℂ] H) (k : V) :
    pairedCoefficient u W L U k =
      ∑' i, ∑' j, ENNReal.ofReal (‖pairedEntry u v W L U k i j‖ ^ 2) := by
  unfold pairedCoefficient hilbertSchmidtSquare
  apply tsum_congr
  intro i
  rw [basis_square_norm v]
  simp only [pairedEntry, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply]

omit [MeasurableSpace V] [CompleteSpace H] [CompleteSpace I] [CompleteSpace O] in
theorem paired_coefficient_finite (u : HilbertBasis ι ℂ I)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (U : V → H →L[ℂ] H) (k : V)
    (hW : hilbertSchmidtSquare u W ≠ ∞) (hU : ‖U k‖ ≤ 1) :
    pairedCoefficient u W L U k ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := ‖L‖ ^ 2)) hW)
  unfold pairedCoefficient hilbertSchmidtSquare
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← ENNReal.ofReal_mul (sq_nonneg ‖L‖)]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simp only [ContinuousLinearMap.comp_apply]
  refine (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (U k).le_of_opNorm_le hU _ |>.trans_eq (one_mul _)

omit [CompleteSpace I] in
theorem paired_coefficient_weighted_moment [Countable ι] [Countable κ]
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (U : V → H →L[ℂ] H)
    (hU : ∀ i j, Measurable (fun k => pairedEntry u v W L U k i j))
    (μ : Measure V) (w : V → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ k, w k * pairedCoefficient u W L U k ∂μ) =
      ∑' i, ∑' j, ∫⁻ k, w k * ENNReal.ofReal (‖pairedEntry u v W L U k i j‖ ^ 2) ∂μ := by
  simp_rw [paired_coefficient_entry_expansion u v, ← ENNReal.tsum_mul_left]
  have hm (i : ι) (j : κ) : Measurable (fun k =>
      w k * ENNReal.ofReal (‖pairedEntry u v W L U k i j‖ ^ 2)) :=
    hw.mul (((hU i j).norm.pow_const (2 : ℕ)).ennreal_ofReal)
  rw [lintegral_tsum (fun i => (Measurable.ennreal_tsum (hm i)).aemeasurable)]
  exact tsum_congr (fun i => lintegral_tsum (fun j => (hm i j).aemeasurable))

end UV.ContinuationBoundary

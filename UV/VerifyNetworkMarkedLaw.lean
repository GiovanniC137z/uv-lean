import UV.VerifyNetworkMarkedJoint
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Absolute costs with coefficients that grow by a fixed inverse power
of the common normal depth. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace UV

/-- Sufficient depth moment for the displacement, momentum, and proper-time
weights of a routed contact at strictly positive edge masses. -/
def networkMarkedDepthExponent {E : Type*} [Fintype E]
    (L : ℕ) (D : ℝ) (d q : ℕ) : ℕ :=
  2 * (q + (⌈D⌉₊ + d + 4 * L) + 3) * Fintype.card E

/-- An inverse-depth polynomial coefficient is paid by its degree in
addition to the graph's own required moment, using one common law. -/
theorem networkMarkedPolynomialCost_common_law_finite {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q J : ℕ)
    (μ : Measure ℝ) (z : ℝ → E → ℝ) (b : ℝ → NetworkVisitSpace n)
    (w : ℝ → ℝ≥0∞) (C : ℝ)
    (hmark : ∀ᵐ r ∂μ, 0 < r ∧ ‖b r‖ ≤ R ∧ (∀ e, c e * r ≤ z r e) ∧
      w r ≤ ENNReal.ofReal C * ENNReal.ofReal ((r ^ J)⁻¹))
    (hmoment : inverseMoment μ
      ((networkMarkedDepthExponent (E := E) L D directions.length q + J : ℕ) : ℝ) < ⊤) :
    (∫⁻ r, w r * networkMarkedPolynomialCost src dst m (z r) directions B (b r) D p q ∂μ) < ⊤ := by
  let N := networkMarkedDepthExponent (E := E) L D directions.length q
  obtain ⟨K, hK, hbound⟩ := networkMarkedPolynomialCost_bound
    G src dst hG hcover m c hm hc directions B hB R hD p q
  let f (r : ℝ) := ENNReal.ofReal ((r ^ (N + J))⁻¹)
  have hf : (∫⁻ r, f r ∂μ) = inverseMoment μ ((N + J : ℕ) : ℝ) := by
    unfold inverseMoment
    have hrpos : ∀ᵐ r ∂μ, r ∈ Ioi (0 : ℝ) := hmark.mono fun _ h => h.1
    have hrestrict : μ.restrict (Ioi (0 : ℝ)) = μ := Measure.restrict_eq_self_of_ae_mem hrpos
    rw [hrestrict]
    apply lintegral_congr_ae
    filter_upwards [hmark] with r hr
    rw [Real.rpow_neg hr.1.le, Real.rpow_natCast]
  calc
    _ ≤ ∫⁻ r, (ENNReal.ofReal K * ENNReal.ofReal C) * f r ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hmark] with r hr
      have hbound' :
          networkMarkedPolynomialCost src dst m (z r) directions B (b r) D p q ≤
            ENNReal.ofReal K * ENNReal.ofReal ((r ^ N)⁻¹) :=
        hbound (z r) (b r) r hr.2.1 hr.1 hr.2.2.1
      apply (mul_le_mul' hr.2.2.2 hbound').trans
      change (ENNReal.ofReal C * ENNReal.ofReal ((r ^ J)⁻¹)) *
        (ENNReal.ofReal K * ENNReal.ofReal ((r ^ N)⁻¹)) ≤
          (ENNReal.ofReal K * ENNReal.ofReal C) * ENNReal.ofReal ((r ^ (N + J))⁻¹)
      rw [mul_mul_mul_comm, mul_comm (ENNReal.ofReal C) (ENNReal.ofReal K),
        mul_comm (ENNReal.ofReal ((r ^ J)⁻¹)),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.1.le N)),
        ← mul_inv, ← pow_add]
    _ = (ENNReal.ofReal K * ENNReal.ofReal C) * inverseMoment μ ((N + J : ℕ) : ℝ) := by
      rw [lintegral_const_mul' _ _ (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ENNReal.ofReal_lt_top)), hf]
    _ < ⊤ := ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hmoment

/-- For a signed residual law, the absolute routed cost is integrated
against its actual Jordan total variation. -/
theorem networkMarkedPolynomialCost_signed_law_finite {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q J : ℕ)
    (σ : SignedMeasure ℝ) (z : ℝ → E → ℝ) (b : ℝ → NetworkVisitSpace n)
    (w : ℝ → ℝ≥0∞) (C : ℝ)
    (hmark : ∀ᵐ r ∂σ.totalVariation, 0 < r ∧ ‖b r‖ ≤ R ∧ (∀ e, c e * r ≤ z r e) ∧
      w r ≤ ENNReal.ofReal C * ENNReal.ofReal ((r ^ J)⁻¹))
    (hmoment : inverseMoment σ.totalVariation
      ((networkMarkedDepthExponent (E := E) L D directions.length q + J : ℕ) : ℝ) < ⊤) :
    (∫⁻ r, w r * networkMarkedPolynomialCost src dst m (z r) directions B (b r) D p q
      ∂σ.totalVariation) < ⊤ :=
  networkMarkedPolynomialCost_common_law_finite G src dst hG hcover m c hm hc directions
    B hB R hD p q J σ.totalVariation z b w C hmark hmoment

/-- The sum of the component variations gives a positive control
measure for a complex residual law. -/
def networkComplexControlMeasure (σ : ComplexMeasure ℝ) : Measure ℝ :=
  (ComplexMeasure.re σ).totalVariation + (ComplexMeasure.im σ).totalVariation

/-- The absolute routed cost is finite against the complex law's control
measure when it has the indicated joint inverse-depth moment. -/
theorem networkMarkedPolynomialCost_complex_law_finite {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q J : ℕ)
    (σ : ComplexMeasure ℝ) (z : ℝ → E → ℝ) (b : ℝ → NetworkVisitSpace n)
    (w : ℝ → ℝ≥0∞) (C : ℝ)
    (hmark : ∀ᵐ r ∂networkComplexControlMeasure σ,
      0 < r ∧ ‖b r‖ ≤ R ∧ (∀ e, c e * r ≤ z r e) ∧
      w r ≤ ENNReal.ofReal C * ENNReal.ofReal ((r ^ J)⁻¹))
    (hmoment : inverseMoment (networkComplexControlMeasure σ)
      ((networkMarkedDepthExponent (E := E) L D directions.length q + J : ℕ) : ℝ) < ⊤) :
    (∫⁻ r, w r * networkMarkedPolynomialCost src dst m (z r) directions B (b r) D p q
      ∂networkComplexControlMeasure σ) < ⊤ :=
  networkMarkedPolynomialCost_common_law_finite G src dst hG hcover m c hm hc directions
    B hB R hD p q J (networkComplexControlMeasure σ) z b w C hmark hmoment

private theorem networkSignedVariation_le_of_abs_le (σ : SignedMeasure ℝ) (μ : Measure ℝ)
    (h : ∀ A, MeasurableSet A → ENNReal.ofReal |σ A| ≤ μ A) :
    σ.totalVariation ≤ μ := by
  obtain ⟨i, hi, hiPos, hiNeg, hPos, hNeg⟩ := σ.toJordanDecomposition_spec
  rw [Measure.le_iff]
  intro A hA
  rw [SignedMeasure.totalVariation, Measure.add_apply, hPos, hNeg,
    SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hA,
    SignedMeasure.toMeasureOfLEZero_apply _ _ _ hA]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal (σ (i ∩ A)) + ENNReal.ofReal (-σ (iᶜ ∩ A)) ≤ μ A
  have hsplit : μ (i ∩ A) + μ (iᶜ ∩ A) = μ A := by
    calc
      _ = μ ((i ∩ A) ∪ (iᶜ ∩ A)) := (measure_union
        (disjoint_compl_right.mono Set.inter_subset_left Set.inter_subset_left)
        (hi.compl.inter hA)).symm
      _ = μ A := by rw [Set.inter_comm i A, Set.inter_comm iᶜ A, Set.inter_union_compl]
  exact (add_le_add ((ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (h _ (hi.inter hA))) ((ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans
    (h _ (hi.compl.inter hA)))).trans hsplit.le

/-- Any positive measure that dominates the norm of the complex measure on
measurable sets controls both component total variations individually. -/
theorem networkComplexControlMeasure_le_add (σ : ComplexMeasure ℝ) (μ : Measure ℝ)
    (hμ : ∀ A, MeasurableSet A → ENNReal.ofReal ‖σ A‖ ≤ μ A) :
    networkComplexControlMeasure σ ≤ μ + μ := by
  apply add_le_add
  · apply networkSignedVariation_le_of_abs_le
    intro A hA
    rw [ComplexMeasure.re_apply]
    exact (ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)).trans (hμ A hA)
  · apply networkSignedVariation_le_of_abs_le
    intro A hA
    rw [ComplexMeasure.im_apply]
    exact (ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)).trans (hμ A hA)

/-- The moment of a norm-dominating positive measure, such as the complex
total variation, suffices for the absolute costs of both signed components. -/
theorem networkMarkedPolynomialCost_complex_dominating_law_finite
    {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q J : ℕ)
    (σ : ComplexMeasure ℝ) (μ : Measure ℝ)
    (hμ : ∀ A, MeasurableSet A → ENNReal.ofReal ‖σ A‖ ≤ μ A)
    (z : ℝ → E → ℝ) (b : ℝ → NetworkVisitSpace n)
    (w : ℝ → ℝ≥0∞) (C : ℝ)
    (hmark : ∀ᵐ r ∂μ, 0 < r ∧ ‖b r‖ ≤ R ∧ (∀ e, c e * r ≤ z r e) ∧
      w r ≤ ENNReal.ofReal C * ENNReal.ofReal ((r ^ J)⁻¹))
    (hmoment : inverseMoment μ
      ((networkMarkedDepthExponent (E := E) L D directions.length q + J : ℕ) : ℝ) < ⊤) :
    (∫⁻ r, w r * networkMarkedPolynomialCost src dst m (z r) directions B (b r) D p q
      ∂networkComplexControlMeasure σ) < ⊤ := by
  have hfin := networkMarkedPolynomialCost_common_law_finite G src dst hG hcover m c hm hc
    directions B hB R hD p q J μ z b w C hmark hmoment
  refine (lintegral_mono' (networkComplexControlMeasure_le_add σ μ hμ) le_rfl).trans_lt ?_
  rw [lintegral_add_measure]
  exact ENNReal.add_lt_top.2 ⟨hfin, hfin⟩

end UV

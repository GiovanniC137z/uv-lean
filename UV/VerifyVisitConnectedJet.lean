import UV.RevisionBoundaryHeat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Probability.Moments.Variance

/-! The tag and magnetic-source degree of the first connected
double visit, using actual polynomial coefficient extraction. -/

noncomputable section

open MeasureTheory Set Real MvPolynomial Filter

namespace UV.VerifyVisitConnectedJet

open UV.RevisionBoundary

/-- The first slot counts closed visits. The second is magnetic degree. -/
def visitJetIndex (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

private theorem visit_jet_index_eq_iff {i j k l : ℕ} :
    visitJetIndex i j = visitJetIndex k l ↔ i = k ∧ j = l := by
  constructor
  · intro he
    exact ⟨by simpa [visitJetIndex] using congrArg (fun m : Fin 2 →₀ ℕ => m 0) he,
      by simpa [visitJetIndex] using congrArg (fun m : Fin 2 →₀ ℕ => m 1) he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem visit_jet_index_add (i j k l : ℕ) :
    visitJetIndex i j + visitJetIndex k l = visitJetIndex (i + k) (j + l) := by
  unfold visitJetIndex
  simp_rw [Finsupp.single_add]
  abel

abbrev VisitJet := MvPolynomial (Fin 2) ℝ

def visitTerm (i j : ℕ) (x : ℝ) : VisitJet := monomial (visitJetIndex i j) x

private theorem visit_term_mul (i j k l : ℕ) (x y : ℝ) :
    visitTerm i j x * visitTerm k l y = visitTerm (i + k) (j + l) (x * y) := by
  rw [visitTerm, visitTerm, monomial_mul, visit_jet_index_add]
  rfl

private theorem visit_term_coeff (i j k l : ℕ) (x : ℝ) :
    coeff (visitJetIndex i j) (visitTerm k l x) = if k = i ∧ l = j then x else 0 := by
  simp [visitTerm, visit_jet_index_eq_iff]

def determinantJet (a b : ℝ) : VisitJet := visitTerm 1 2 a + visitTerm 1 4 b

def exponentiatedJet (a b : ℝ) : VisitJet :=
  determinantJet a b + C (1 / 2 : ℝ) * (determinantJet a b * determinantJet a b)

theorem exponentiated_visit_jet_coefficients (a b : ℝ) :
    coeff (visitJetIndex 1 2) (exponentiatedJet a b) = a ∧
      coeff (visitJetIndex 1 4) (exponentiatedJet a b) = b ∧
      coeff (visitJetIndex 2 4) (exponentiatedJet a b) = a ^ (2 : ℕ) / 2 := by
  norm_num [exponentiatedJet, determinantJet, coeff_add, coeff_C_mul,
    add_mul, mul_add, visit_term_mul, visit_term_coeff]
  ring

/-- The normalized constant coefficient is one. Only the remaining
three coefficients within tag degree two and magnetic degree four
are needed before taking the connected logarithm. -/
def averagedVisitJet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Ω → ℝ) : VisitJet :=
  visitTerm 1 2 (∫ x, coeff (visitJetIndex 1 2) (exponentiatedJet (A x) (B x)) ∂μ) +
    visitTerm 1 4 (∫ x, coeff (visitJetIndex 1 4) (exponentiatedJet (A x) (B x)) ∂μ) +
    visitTerm 2 4 (∫ x, coeff (visitJetIndex 2 4) (exponentiatedJet (A x) (B x)) ∂μ)

def connectedVisitJet (P : VisitJet) : VisitJet := P - C (1 / 2 : ℝ) * (P * P)

private theorem connected_visit_jet_coefficients (a b c : ℝ) :
    coeff (visitJetIndex 2 4) (connectedVisitJet (visitTerm 1 2 a +
      visitTerm 1 4 b + visitTerm 2 4 c)) = c - a ^ (2 : ℕ) / 2 := by
  norm_num [connectedVisitJet, coeff_add, coeff_sub, coeff_C_mul, add_mul,
    mul_add, visit_term_mul, visit_term_coeff]
  ring

/-- The averaged source must precede the connected logarithm. The
fourth-degree jet within one charged determinant has no double-tag
coefficient. -/
theorem connected_double_visit_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Ω → ℝ}
    (hI : MemLp I 2 μ) (c : ℝ) (fourth : Ω → ℝ) :
    coeff (visitJetIndex 2 4)
        (connectedVisitJet (averagedVisitJet μ (fun x => c * I x) fourth)) =
      c ^ (2 : ℕ) / 2 * ProbabilityTheory.variance I μ := by
  unfold averagedVisitJet
  rw [connected_visit_jet_coefficients]
  simp_rw [(exponentiated_visit_jet_coefficients _ _).1,
    (exponentiated_visit_jet_coefficients _ _).2.2]
  rw [ProbabilityTheory.variance_eq_sub hI]
  simp only [Pi.pow_apply, mul_pow, integral_div, integral_const_mul]
  ring

/-- Logarithmic remainders of at least third tag degree give zero
in the exact mixed coefficient. -/
theorem cubic_visit_tag_irrelevant (P : VisitJet) :
    coeff (visitJetIndex 2 4) (MvPolynomial.X 0 ^ (3 : ℕ) * P) = 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  have hn : ¬ Finsupp.single (0 : Fin 2) (3 : ℕ) ≤ visitJetIndex 2 4 := by
    intro h
    have h' := h 0
    norm_num [visitJetIndex] at h'
  simp [hn]

/-- The positive proper-time cutoff gives the continuous value at
coincidence even though the uncut return diverges there. -/
def visitCutoff (δ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (if x = 0 then δ⁻¹ - T⁻¹
    else (Real.exp (-(x ^ (2 : ℕ)) / T) - Real.exp (-(x ^ (2 : ℕ)) / δ)) / x ^ (2 : ℕ))

theorem visit_cutoff_measurable (δ T : ℝ) : Measurable (visitCutoff δ T) := by
  have hg : Measurable (fun x : ℝ => if x = 0 then δ⁻¹ - T⁻¹ else
      (Real.exp (-(x ^ (2 : ℕ)) / T) - Real.exp (-(x ^ (2 : ℕ)) / δ)) / x ^ (2 : ℕ)) :=
    Measurable.ite (measurableSet_singleton _) measurable_const (by fun_prop)
  have hc : Measurable (fun _ : ℝ => (1 / (2 * Real.pi) : ℝ)) := measurable_const
  exact hc.mul hg

theorem visit_cutoff_exact {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    IntegrableOn (returnIntegrand x) (Ioc δ T) ∧
      visitCutoff δ T x = (1 / (2 * Real.pi)) * ∫ t in Ioc δ T, returnIntegrand x t := by
  have hT : 0 < T := hδ.trans_le hδT
  have hco : ContinuousOn (returnIntegrand x) (Icc δ T) := by
    unfold returnIntegrand
    have hz : ∀ t ∈ Icc δ T, t ≠ (0 : ℝ) := fun _ ht => (hδ.trans_le ht.1).ne'
    exact ((continuous_const.continuousOn.div continuous_id.continuousOn hz).rexp).div
      (continuous_id.pow 2).continuousOn (fun t ht => pow_ne_zero _ (hz t ht))
  have hci : IntegrableOn (returnIntegrand x) (Ioc δ T) :=
    hco.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨hci, ?_⟩
  by_cases hx : x = 0
  · subst x
    change (1 / (2 * Real.pi)) * (if (0 : ℝ) = 0 then δ⁻¹ - T⁻¹ else _) = _
    rw [if_pos rfl]
    congr 1
    rw [← intervalIntegral.integral_of_le hδT]
    symm
    let F := fun t : ℝ => -t⁻¹
    have hF : ContinuousOn F (Icc δ T) := fun t ht =>
      ((continuousAt_id.inv₀ (hδ.trans_le ht.1).ne').neg).continuousWithinAt
    have hD : ∀ t ∈ Ioo δ T, HasDerivAt F (returnIntegrand 0 t) t := by
      intro t ht
      convert ((hasDerivAt_inv (hδ.trans ht.1).ne').neg) using 1
      simp [returnIntegrand, one_div]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδT hF hD
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδT).mpr hci)]
    unfold F
    ring
  · have hi0 := (return_integral_exact hδ hx).1
    have hiδ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mpr hi0
    have hiB := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδT).mpr hci
    have hsum := intervalIntegral.integral_add_adjacent_intervals hiδ hiB
    rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδT,
      intervalIntegral.integral_of_le hT.le, (return_integral_exact hδ hx).2,
      (return_integral_exact hT hx).2] at hsum
    change (1 / (2 * Real.pi)) * (if x = 0 then δ⁻¹ - T⁻¹ else _) = _
    rw [if_neg hx]
    congr 1
    rw [sub_div]
    linarith

theorem visit_cutoff_bounds {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    visitCutoff δ T x ∈ Icc 0 (visitCutoff δ T 0) := by
  have hx := visit_cutoff_exact hδ hδT x
  have h0 := visit_cutoff_exact hδ hδT 0
  rw [mem_Icc, hx.2, h0.2]
  have hconst : 0 ≤ 1 / (2 * Real.pi) := by positivity
  refine ⟨mul_nonneg hconst ?_, mul_le_mul_of_nonneg_left ?_ hconst⟩
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  · apply setIntegral_mono_on hx.1 h0.1 measurableSet_Ioc
    intro t ht
    unfold returnIntegrand
    simp only [neg_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero]
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr <|
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (hδ.trans ht.1).le)
      (sq_nonneg _)

theorem connected_marked_visit_variance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (c : ℝ) (fourth : ℝ → ℝ) :
    coeff (visitJetIndex 2 4)
        (connectedVisitJet (averagedVisitJet μ (fun x => c * visitCutoff δ T x) fourth)) =
      c ^ (2 : ℕ) / 2 * ProbabilityTheory.variance (visitCutoff δ T) μ := by
  apply connected_double_visit_variance
  exact memLp_of_bounded (Eventually.of_forall (visit_cutoff_bounds hδ hδT))
    (visit_cutoff_measurable δ T).aestronglyMeasurable 2

end UV.VerifyVisitConnectedJet

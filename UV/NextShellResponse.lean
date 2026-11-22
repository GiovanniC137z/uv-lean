import UV.NextSameSideShell
import UV.FurtherPoleVariation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Boundary response in a regular invariant coordinate with a fixed
test density. The carrier unit moves in one declared common algebra.
Differentiation is performed at finite height before taking the limit. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

variable {E R : Type*} [NormedAddCommGroup E] [NormedRing R] [NormedAlgebra ℝ R]

/-- The canonical scalar convention in the common transported algebra. -/
def Plane.transportedCanonicalCovariance (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) (j : UnitVector R) : R :=
  (diamond.eta ε • (j : R)) * Ring.inverse (diamond.transportedPole ε height D j)

theorem Plane.transported_canonical_split (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) (j : UnitVector R) (hj : (j : R) ^ 2 = -1) :
    diamond.transportedCanonicalCovariance ε height D j =
      polePoisson (height : ℝ) D • (1 : R) +
        (diamond.eta ε * polePV (height : ℝ) D) • (j : R) := by
  let η := diamond.eta ε
  let h : ℝ := height
  let j₀ : R := j
  have h₁ : (η • j₀) * algebraMap ℝ R D = (η * D) • j₀ := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_smul, mul_comm D]
  have hη : η * η = 1 := by
    rw [← pow_two, diamond.eta_sq ε]
  have h₂ : (η • j₀) * ((η * h) • j₀) = -(h • (1 : R)) := by
    rw [smul_mul_assoc, mul_smul_comm, ← pow_two, show j₀ ^ 2 = -1 from hj,
      smul_neg, smul_neg, ← smul_smul, smul_smul, hη, one_smul]
  unfold Plane.transportedCanonicalCovariance
  rw [diamond.transported_pole_inverse_formula ε height D j hj]
  change (η • j₀) * ((D ^ 2 + h ^ 2)⁻¹ • (algebraMap ℝ R D - (η * h) • j₀)) = _
  rw [mul_smul_comm, mul_sub, h₁, h₂, sub_neg_eq_add, smul_add, smul_smul, smul_smul, add_comm]
  unfold polePoisson polePV
  congr 1 <;> congr 1 <;> ring

private theorem shell_fraction_norm_le {a h D : ℝ} (hh : 0 < h)
    (ha : |a| ≤ D ^ 2 + h ^ 2) :
    ‖a / (D ^ 2 + h ^ 2) ^ 2‖ ≤ (h ^ 2)⁻¹ := by
  have hden : 0 < D ^ 2 + h ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hden)]
  calc
    _ ≤ (D ^ 2 + h ^ 2) / (D ^ 2 + h ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right ha (sq_nonneg _)
    _ = (D ^ 2 + h ^ 2)⁻¹ := by field_simp
    _ ≤ (h ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hh) (le_add_of_nonneg_left (sq_nonneg D))

theorem same_side_real_norm_le {h : ℝ} (hh : 0 < h) (D : ℝ) :
    ‖sameSideReal h D‖ ≤ (h ^ 2)⁻¹ := by
  apply shell_fraction_norm_le hh
  exact abs_le.mpr ⟨by linarith [sq_nonneg D], by linarith [sq_nonneg h]⟩

theorem same_side_imag_norm_le {h : ℝ} (hh : 0 < h) (D : ℝ) :
    ‖sameSideImag h D‖ ≤ (h ^ 2)⁻¹ := by
  apply shell_fraction_norm_le hh
  rw [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * h)]
  nlinarith [sq_nonneg (|D| - h), sq_abs D]

/-- One scale-independent differentiation lemma for either shell
regularizer. The derivative bound is needed only at the current height. -/
private theorem hasDerivAt_tested_shell_component
    {f : ℝ → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {D D' : ℝ → ℝ → ℝ} (ht : ∀ t, Continuous (D t)) (h0 : ∀ x, D 0 x = x)
    {b : ℝ} (hb : 0 < b)
    (hD : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, HasDerivAt (fun u => D u x) (D' t x) t)
    (hD' : Continuous (D' 0)) {B : ℝ}
    (hB : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, ‖D' t x‖ ≤ B)
    {q q' : ℝ → ℝ} (hq : ∀ x, HasDerivAt q (q' x) x) (hq' : Continuous q')
    {C : ℝ} (hC : ∀ x, ‖q' x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, q (D t x) * f x)
      (∫ x, q' x * (D' 0 x * f x)) 0 := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hq x).continuousAt
  have hF (t : ℝ) : Continuous (fun x => q (D t x) * f x) :=
    (hqc.comp (ht t)).mul hf
  have hF₀ : Integrable (fun x => q (D 0 x) * f x) :=
    (hF 0).integrable_of_hasCompactSupport (hs.mul_left (f := fun x => q (D 0 x)))
  have hFn : ∀ᶠ t : ℝ in 𝓝 0, AEStronglyMeasurable (fun x => q (D t x) * f x) volume :=
    Eventually.of_forall fun t => (hF t).aestronglyMeasurable
  have hm : Continuous (fun x => q' (D 0 x) * (D' 0 x * f x)) :=
    (hq'.comp (ht 0)).mul (hD'.mul hf)
  have hC₀ : 0 ≤ C := (norm_nonneg (q' 0)).trans (hC 0)
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ t ∈ Metric.ball (0 : ℝ) b, ‖q' (D t x) * (D' t x * f x)‖ ≤ C * B * ‖f x‖ := by
    refine Eventually.of_forall fun x t hs => ?_
    rw [norm_mul, norm_mul, mul_assoc]
    exact (mul_le_mul_of_nonneg_right (hC _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hB t hs x) (norm_nonneg _)) hC₀)
  have hdiff : ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ t ∈ Metric.ball (0 : ℝ) b,
        HasDerivAt (fun u => q (D u x) * f x) (q' (D t x) * (D' t x * f x)) t := by
    refine Eventually.of_forall fun x t htb => ?_
    simpa only [Function.comp_def, mul_assoc] using ((hq (D t x)).comp t (hD t htb x)).mul_const (f x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := (0 : ℝ)) hb hFn hF₀ hm.aestronglyMeasurable hbound
    ((hf.integrable_of_hasCompactSupport hs).norm.const_mul (C * B)) hdiff).2
  simpa only [h0] using h

variable [CompleteSpace R]

/-- Derivative of the actual tested canonical covariance at positive
height. D is the regular chart at the base point. The test is held fixed. -/
theorem Plane.tested_canonical_covariance_hasDerivAt (diamond : Plane E) (ε : Evolution)
    (height : Height) {j : ℝ → UnitVector R} {dj : R}
    (hj : HasDerivAt (fun t => (j t : R)) dj 0) (hjSq : ∀ t, (j t : R) ^ 2 = -1)
    {f : ℝ → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {D D' : ℝ → ℝ → ℝ} (ht : ∀ t, Continuous (D t)) (h0 : ∀ x, D 0 x = x)
    {b : ℝ} (hb : 0 < b)
    (hD : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, HasDerivAt (fun u => D u x) (D' t x) t)
    (hD' : Continuous (D' 0)) {B : ℝ}
    (hB : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, ‖D' t x‖ ≤ B) :
    let h : ℝ := height
    let ψ (x : ℝ) := D' 0 x * f x
    HasDerivAt
      (fun t : ℝ => ∫ x, f x • diamond.transportedCanonicalCovariance ε height (D t x) (j t))
      (((∫ x, sameSideImag h x * ψ x) • (1 : R) -
          (diamond.eta ε * ∫ x, sameSideReal h x * ψ x) • (j 0 : R)) +
        (diamond.eta ε * ∫ x, polePV h x * f x) • dj) 0 := by
  let h : ℝ := height
  let ψ (x : ℝ) := D' 0 x * f x
  let η := diamond.eta ε
  have hpos : 0 < h := height.property
  have hqc : Continuous (sameSideImag h) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have hpc : Continuous (sameSideReal h) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have hq := hasDerivAt_tested_shell_component hf hs ht h0 hb hD hD' hB
    (polePoisson_hasDerivAt hpos) hqc (same_side_imag_norm_le hpos)
  have hp := hasDerivAt_tested_shell_component hf hs ht h0 hb hD hD' hB
    (polePV_hasDerivAt hpos) hpc.neg (fun x => by simpa using same_side_real_norm_le hpos x)
  simp only [neg_mul, integral_neg] at hp
  have hsum := (hq.smul_const (1 : R)).add ((hp.const_mul η).smul hj)
  have heq (t : ℝ) :
      (∫ x, f x • diamond.transportedCanonicalCovariance ε height (D t x) (j t)) =
      (∫ x, polePoisson h (D t x) * f x) • (1 : R) +
        (η * ∫ x, polePV h (D t x) * f x) • (j t : R) := by
    have hsplit : (fun x => f x • diamond.transportedCanonicalCovariance ε height (D t x) (j t)) =
        (fun x => (polePoisson h (D t x) * f x) • (1 : R) +
          (η * (polePV h (D t x) * f x)) • (j t : R)) := by
      funext x
      rw [diamond.transported_canonical_split ε height _ _ (hjSq t), smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> ring
    have hi {q : ℝ → ℝ} (hq₀ : Continuous q) :
        Integrable (fun x => q (D t x) * f x) :=
      ((hq₀.comp (ht t)).mul hf).integrable_of_hasCompactSupport
        (hs.mul_left (f := fun x => q (D t x)))
    have hqi := hi (continuous_iff_continuousAt.mpr fun x => (polePoisson_hasDerivAt hpos x).continuousAt)
    have hpi := hi (continuous_iff_continuousAt.mpr fun x => (polePV_hasDerivAt hpos x).continuousAt)
    rw [hsplit, integral_add (hqi.smul_const _) ((hpi.const_mul η).smul_const _),
      integral_smul_const, integral_smul_const, integral_const_mul]
  rw [show (fun t : ℝ => ∫ x, f x • diamond.transportedCanonicalCovariance ε height (D t x) (j t)) =
    _ from funext heq]
  convert hsum using 1
  simp only [h0, mul_neg, neg_smul, sub_eq_add_neg]
  abel

omit [CompleteSpace R] in
/-- The three terms of the boundary response. The normal velocity
multiplies the test before the finite-part and delta-derivative actions. -/
theorem Plane.canonical_boundary_response_limit (diamond : Plane E) (ε : Evolution)
    (j : UnitVector R) (dj : R)
    {f ψ ψ' : ℝ → ℝ} {L K : ℝ≥0}
    (hf : LipschitzWith L f) (hsf : HasCompactSupport f)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hsψ : HasCompactSupport ψ)
    (hψ' : LipschitzWith K ψ') :
    Tendsto (fun h : ℝ =>
      (((∫ x, sameSideImag h x * ψ x) • (1 : R) -
          (diamond.eta ε * ∫ x, sameSideReal h x * ψ x) • (j : R)) +
        (diamond.eta ε * ∫ x, polePV h x * f x) • dj))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((-(Real.pi * ψ' 0)) • (1 : R) -
          (diamond.eta ε * ∫ x, shellFinitePartTest ψ x) • (j : R)) +
        (diamond.eta ε * ∫ x in Ioi (0 : ℝ), symmetricTest f x) • dj)) := by
  have hb := same_side_shell_test_limit hψ hsψ hψ'
  have hbRe := continuous_fst.continuousAt.tendsto.comp hb
  have hbIm := continuous_snd.continuousAt.tendsto.comp hb
  have hp := pole_pv_test_limit hf (hf.continuous.integrable_of_hasCompactSupport hsf)
  simpa only [Function.comp_def] using
    ((hbIm.smul_const (1 : R)).sub
      ((hbRe.const_mul (diamond.eta ε)).smul_const (j : R))).add
      ((hp.const_mul (diamond.eta ε)).smul_const dj)

/-- The derivative of each tested finite-height covariance has the
three-term boundary value on the same regular chart. -/
theorem Plane.tested_canonical_boundary_response (diamond : Plane E) (ε : Evolution)
    {j : ℝ → UnitVector R} {dj : R}
    (hj : HasDerivAt (fun t => (j t : R)) dj 0) (hjSq : ∀ t, (j t : R) ^ 2 = -1)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f)
    {D D' : ℝ → ℝ → ℝ} (ht : ∀ t, Continuous (D t)) (h0 : ∀ x, D 0 x = x)
    {b : ℝ} (hb : 0 < b)
    (hD : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, HasDerivAt (fun u => D u x) (D' t x) t)
    (hD' : Continuous (D' 0)) {B : ℝ}
    (hB : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, ‖D' t x‖ ≤ B)
    {ψ' : ℝ → ℝ} {K : ℝ≥0}
    (hψ : ∀ x, HasDerivAt (fun y => D' 0 y * f y) (ψ' x) x)
    (hψ' : LipschitzWith K ψ') :
    let ψ (x : ℝ) := D' 0 x * f x
    ∃ response : ℝ → R,
      (∀ h : Height, HasDerivAt
        (fun t : ℝ => ∫ x, f x • diamond.transportedCanonicalCovariance ε h (D t x) (j t))
        (response (h : ℝ)) 0) ∧
      Tendsto response (𝓝[>] (0 : ℝ))
        (𝓝 (((-(Real.pi * ψ' 0)) • (1 : R) -
          (diamond.eta ε * ∫ x, shellFinitePartTest ψ x) • (j 0 : R)) +
          (diamond.eta ε * ∫ x in Ioi (0 : ℝ), symmetricTest f x) • dj)) := by
  let ψ (x : ℝ) := D' 0 x * f x
  refine ⟨fun h : ℝ =>
    (((∫ x, sameSideImag h x * ψ x) • (1 : R) -
      (diamond.eta ε * ∫ x, sameSideReal h x * ψ x) • (j 0 : R)) +
      (diamond.eta ε * ∫ x, polePV h x * f x) • dj), ?_, ?_⟩
  · intro h
    exact diamond.tested_canonical_covariance_hasDerivAt ε h hj hjSq hf.continuous hs
      ht h0 hb hD hD' hB
  · exact diamond.canonical_boundary_response_limit ε (j 0) dj hf hs hψ
      (hs.mul_left (f := D' 0)) hψ'

end UV.SectorPlane

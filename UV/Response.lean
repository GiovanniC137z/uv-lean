import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! Ordered resolvent and Schur error estimates from the response section.
The inverse existence and norm estimates below are proved in a complete normed
ring; no commutation, root-location, or physical reconstruction is assumed. -/

noncomputable section
namespace UV

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- Quantitative Neumann estimate, including existence of the actual inverse. -/
theorem response_inverse_one_sub_bound {t : R} {q : ℝ}
    (htq : ‖t‖ ≤ q) (hq : q < 1) :
    IsUnit (1 - t) ∧ ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - q) := by
  have ht : ‖t‖ < 1 := htq.trans_lt hq
  refine ⟨isUnit_one_sub_of_norm_lt_one ht, ?_⟩
  rw [← geom_series_eq_inverse t ht]
  calc
    ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹ := by
      simpa only [norm_one, sub_self, zero_add] using tsum_geometric_le_of_norm_lt_one t ht
    _ ≤ 1 / (1 - q) := by
      rw [one_div]
      exact inv_anti₀ (by linarith) (by linarith)

/-- Approximate inverse certification: a certified inverse of A and a strict
Neumann margin give the inverse of A-E with the source's exact constant. -/
theorem response_inverse_perturbation {A E : R} {B ε : ℝ}
    (hA : IsUnit A) (hB : ‖Ring.inverse A‖ ≤ B)
    (hε : ‖E‖ ≤ ε) (hq : B * ε < 1) :
    IsUnit (A - E) ∧ ‖Ring.inverse (A - E)‖ ≤ B / (1 - B * ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hden : 0 < 1 - B * ε := sub_pos.mpr hq
  have ht : ‖Ring.inverse A * E‖ ≤ B * ε := by
    exact (norm_mul_le _ _).trans (mul_le_mul hB hε (norm_nonneg _) hB0)
  obtain ⟨hu, hnorm⟩ := response_inverse_one_sub_bound ht hq
  have hfactor : A * (1 - Ring.inverse A * E) = A - E := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
  have hunit : IsUnit (A - E) := hfactor ▸ hA.mul hu
  refine ⟨hunit, ?_⟩
  have hinverse : Ring.inverse (A - E) =
      Ring.inverse (1 - Ring.inverse A * E) * Ring.inverse A := by
    have hid : Ring.inverse (A - E) * 1 =
        Ring.inverse (1 - Ring.inverse A * E) * Ring.inverse A := by
      apply (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hunit).mpr
      symm
      calc
        _ = A * ((1 - Ring.inverse A * E) *
              Ring.inverse (1 - Ring.inverse A * E)) * Ring.inverse A := by
          rw [← hfactor]
          noncomm_ring
        _ = 1 := by rw [Ring.mul_inverse_cancel _ hu, mul_one, Ring.mul_inverse_cancel A hA]
    simpa only [mul_one] using hid
  rw [hinverse]
  calc
    _ ≤ ‖Ring.inverse (1 - Ring.inverse A * E)‖ * ‖Ring.inverse A‖ := norm_mul_le _ _
    _ ≤ (1 / (1 - B * ε)) * B := mul_le_mul hnorm hB (norm_nonneg _) (by positivity)
    _ = B / (1 - B * ε) := by ring

omit [NormOneClass R] [CompleteSpace R] in
/-- The ordered second resolvent identity. -/
theorem response_resolvent_identity {A B : R} (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse A - Ring.inverse B =
      Ring.inverse A * (B - A) * Ring.inverse B := by
  rw [mul_sub, sub_mul]
  rw [mul_assoc, Ring.mul_inverse_cancel B hB, mul_one,
    Ring.inverse_mul_cancel A hA, one_mul]

/-- A posteriori resolvent difference bound in terms only of the approximate
inverse norm and the certified response error. -/
theorem response_resolvent_error {A E : R} {B ε : ℝ}
    (hA : IsUnit A) (hB : ‖Ring.inverse A‖ ≤ B)
    (hε : ‖E‖ ≤ ε) (hq : B * ε < 1) :
    ‖Ring.inverse (A - E) - Ring.inverse A‖ ≤ B ^ 2 * ε / (1 - B * ε) := by
  obtain ⟨hunit, hinv⟩ := response_inverse_perturbation hA hB hε hq
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hden : 0 < 1 - B * ε := sub_pos.mpr hq
  rw [response_resolvent_identity hunit hA]
  have he : A - (A - E) = E := by noncomm_ring
  rw [he]
  calc
    _ ≤ (‖Ring.inverse (A - E)‖ * ‖E‖) * ‖Ring.inverse A‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((B / (1 - B * ε)) * ε) * B := by
      gcongr
    _ = B ^ 2 * ε / (1 - B * ε) := by ring

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- The inverse and Schur part of cor:OQED-aposteriori-Schur, with correctly
typed electromagnetic and retained-channel maps. Here A is the known
approximate inverse response and E is the certified response increment. -/
theorem response_schur_error {A E : H →L[ℂ] H} {B ε : ℝ}
    (hA : IsUnit A) (hB : ‖Ring.inverse A‖ ≤ B)
    (hε : ‖E‖ ≤ ε) (hq : B * ε < 1)
    (U : H →L[ℂ] K) (V : K →L[ℂ] H) :
    IsUnit (A - E) ∧
      ‖Ring.inverse (A - E)‖ ≤ B / (1 - B * ε) ∧
      ‖U.comp ((Ring.inverse (A - E) - Ring.inverse A).comp V)‖ ≤
        ‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε) := by
  obtain ⟨hunit, hinv⟩ := response_inverse_perturbation hA hB hε hq
  refine ⟨hunit, hinv, ?_⟩
  have herr := response_resolvent_error hA hB hε hq
  calc
    _ ≤ ‖U‖ * ‖(Ring.inverse (A - E) - Ring.inverse A).comp V‖ :=
      U.opNorm_comp_le _
    _ ≤ ‖U‖ * (‖Ring.inverse (A - E) - Ring.inverse A‖ * ‖V‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖U‖ * ((B ^ 2 * ε / (1 - B * ε)) * ‖V‖) := by
      gcongr
    _ = _ := by ring

omit [CompleteSpace H] [Nontrivial H] in
/-- The change of a Schur correction is exactly the composed resolvent change.
This includes its sign and has no commutation requirement. -/
theorem response_schur_difference (U : H →L[ℂ] K) (V : K →L[ℂ] H)
    (D RX RY : H →L[ℂ] H) :
    -U.comp ((RX - D).comp V) - -U.comp ((RY - D).comp V) =
      -U.comp ((RX - RY).comp V) := by
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  abel

/-- Source pole derivative, once the null-vector differentiation has identified
the numerator and the nonzero baseline denominator. -/
def responsePoleDerivative (W : K →L[ℂ] ℂ) (v : K) (d : ℂ)
    (Δ : K →L[ℂ] K) : ℂ := -(W (Δ v)) / d

def responsePoleRate (W : K →L[ℂ] ℂ) (v : K) (d : ℂ)
    (Δ : K →L[ℂ] K) : ℝ := -2 * (responsePoleDerivative W v d Δ).im

/-- The baseline-pole functional is Lipschitz in the complete Schur correction.
This is the quantitative part of eq:OQED-pole-error-bound, without claiming
existence of an analytic root family. -/
theorem response_pole_rate_error (W : K →L[ℂ] ℂ) (v : K) {d : ℂ} (hd : d ≠ 0)
    (ΔX ΔY : K →L[ℂ] K) :
    |responsePoleRate W v d ΔX - responsePoleRate W v d ΔY| ≤
      2 * (‖W‖ * ‖v‖ / ‖d‖) * ‖ΔX - ΔY‖ := by
  have hd0 : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hdiff : responsePoleDerivative W v d ΔX - responsePoleDerivative W v d ΔY =
      -(W ((ΔX - ΔY) v)) / d := by
    simp only [responsePoleDerivative, ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hnorm : ‖responsePoleDerivative W v d ΔX - responsePoleDerivative W v d ΔY‖ ≤
      (‖W‖ * ‖v‖ / ‖d‖) * ‖ΔX - ΔY‖ := by
    rw [hdiff, norm_div, norm_neg]
    calc
      ‖W ((ΔX - ΔY) v)‖ / ‖d‖ ≤
          (‖W‖ * (‖ΔX - ΔY‖ * ‖v‖)) / ‖d‖ := by
        apply div_le_div_of_nonneg_right _ hd0.le
        exact (W.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((ΔX - ΔY).le_opNorm v) (norm_nonneg W))
      _ = _ := by ring
  calc
    _ = 2 * |(responsePoleDerivative W v d ΔX - responsePoleDerivative W v d ΔY).im| := by
      simp only [responsePoleRate, Complex.sub_im]
      calc
        _ = |(-2 : ℝ) * ((responsePoleDerivative W v d ΔX).im -
            (responsePoleDerivative W v d ΔY).im)| := by congr 1; ring
        _ = _ := by rw [abs_mul]; norm_num
    _ ≤ 2 * ‖responsePoleDerivative W v d ΔX - responsePoleDerivative W v d ΔY‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
    _ ≤ _ := by linarith

/-- The assembled first-order rate certificate of cor:OQED-aposteriori-Schur.
The baseline-pole functional is explicit; identifying it with a derivative of
an analytic root still uses the source's separate simple-pole hypotheses. -/
theorem response_aposteriori_rate_error {A E : H →L[ℂ] H} {B ε : ℝ}
    (hA : IsUnit A) (hB : ‖Ring.inverse A‖ ≤ B)
    (hε : ‖E‖ ≤ ε) (hq : B * ε < 1)
    (U : H →L[ℂ] K) (V : K →L[ℂ] H) (D : H →L[ℂ] H)
    (W : K →L[ℂ] ℂ) (v : K) {d : ℂ} (hd : d ≠ 0) :
    |responsePoleRate W v d (-U.comp ((Ring.inverse (A - E) - D).comp V)) -
      responsePoleRate W v d (-U.comp ((Ring.inverse A - D).comp V))| ≤
      2 * (‖W‖ * ‖v‖ / ‖d‖) *
        (‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε)) := by
  have hschur := (response_schur_error hA hB hε hq U V).2.2
  have hrate := response_pole_rate_error W v hd
    (-U.comp ((Ring.inverse (A - E) - D).comp V))
    (-U.comp ((Ring.inverse A - D).comp V))
  rw [response_schur_difference, norm_neg] at hrate
  exact hrate.trans (mul_le_mul_of_nonneg_left hschur (by positivity))

/-- The strict approximate-rate margin certifies positivity of the exact
first-order rate, rather than a finite shifted-root rate. -/
theorem response_rate_positive_of_error {exactRate approximateRate error : ℝ}
    (herror : |exactRate - approximateRate| ≤ error) (hmargin : error < approximateRate) :
    0 < exactRate := by
  have := (abs_le.mp herror).1
  linarith

/-- The normalized contour-integral error on a circle. The source's general
contour-length factor becomes its radius for this contour. -/
theorem response_circle_integral_error {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] {f g : ℂ → Z} {c : ℂ} {r C : ℝ} (hr : 0 ≤ r)
    (hf : CircleIntegrable f c r) (hg : CircleIntegrable g c r)
    (hbound : ∀ z ∈ Metric.sphere c r, ‖f z - g z‖ ≤ C) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegral f c r -
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegral g c r‖ ≤ r * C := by
  rw [← smul_sub, ← circleIntegral.integral_sub hf hg]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hbound

/-- The quantitative circle-contour part of prop:OQED-observable-residue-error.
The two normalized contour integrals obey the claimed bound. Their identification
with residues requires the separate meromorphic/simple-pole hypotheses. -/
theorem response_observable_circle_error
    (A E : ℂ → H →L[ℂ] H) (U : ℂ → H →L[ℂ] K) (V : ℂ → K →L[ℂ] H)
    {c : ℂ} {r B ε Lout Lin : ℝ} (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hLo : 0 ≤ Lout)
    (hq : B * ε < 1)
    (hA : ∀ z ∈ Metric.sphere c r, IsUnit (A z))
    (hB : ∀ z ∈ Metric.sphere c r, ‖Ring.inverse (A z)‖ ≤ B)
    (hε : ∀ z ∈ Metric.sphere c r, ‖E z‖ ≤ ε)
    (hU : ∀ z ∈ Metric.sphere c r, ‖U z‖ ≤ Lout)
    (hV : ∀ z ∈ Metric.sphere c r, ‖V z‖ ≤ Lin)
    (hX : CircleIntegrable (fun z => (U z).comp ((Ring.inverse (A z - E z)).comp (V z))) c r)
    (hY : CircleIntegrable (fun z => (U z).comp ((Ring.inverse (A z)).comp (V z))) c r) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        circleIntegral (fun z => (U z).comp ((Ring.inverse (A z - E z)).comp (V z))) c r -
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        circleIntegral (fun z => (U z).comp ((Ring.inverse (A z)).comp (V z))) c r‖ ≤
      r * Lout * Lin * B ^ 2 * ε / (1 - B * ε) := by
  have hden : 0 < 1 - B * ε := sub_pos.mpr hq
  calc
    _ ≤ r * (Lout * Lin * B ^ 2 * ε / (1 - B * ε)) := by
      apply response_circle_integral_error hr hX hY
      intro z hz
      rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
      have hh := (response_schur_error (hA z hz) (hB z hz) (hε z hz) hq (U z) (V z)).2.2
      apply hh.trans
      gcongr
      · exact hU z hz
      · exact hV z hz
    _ = _ := by ring

omit [Nontrivial H] in
/-- A holomorphic response pencil has a holomorphic inverse wherever it is
invertible; the set need not itself be open because analyticity is in a
neighborhood of every point. -/
theorem response_analytic_inverse {s : Set ℂ} {A : ℂ → H →L[ℂ] H}
    (hA : AnalyticOnNhd ℂ A s) (hunit : ∀ z ∈ s, IsUnit (A z)) :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (A z)) s := by
  exact analyticOnNhd_inverse.comp hA hunit

/-- Analytic inverse and Schur correction under the response error margin.
The electromagnetic inverse is constructed by the Neumann estimate, and all
frequency dependent coupling maps retain their source order. -/
theorem response_analytic_schur {s : Set ℂ} {A E D : ℂ → H →L[ℂ] H}
    {U : ℂ → H →L[ℂ] K} {V : ℂ → K →L[ℂ] H} {B ε : ℝ}
    (hA : AnalyticOnNhd ℂ A s) (hE : AnalyticOnNhd ℂ E s)
    (hD : AnalyticOnNhd ℂ D s) (hU : AnalyticOnNhd ℂ U s)
    (hV : AnalyticOnNhd ℂ V s)
    (hunit : ∀ z ∈ s, IsUnit (A z))
    (hB : ∀ z ∈ s, ‖Ring.inverse (A z)‖ ≤ B)
    (hε : ∀ z ∈ s, ‖E z‖ ≤ ε) (hq : B * ε < 1) :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (A z - E z)) s ∧
    AnalyticOnNhd ℂ (fun z => -(U z).comp ((Ring.inverse (A z - E z) - D z).comp (V z))) s := by
  have hinv : AnalyticOnNhd ℂ (fun z => Ring.inverse (A z - E z)) s :=
    response_analytic_inverse (hA.sub hE)
      (fun z hz => (response_inverse_perturbation (hunit z hz) (hB z hz) (hε z hz) hq).1)
  refine ⟨hinv, ?_⟩
  intro z hz
  have hinner := ((ContinuousLinearMap.compL ℂ K H H).analyticAt_bilinear _).comp₂
    ((hinv z hz).sub (hD z hz)) (hV z hz)
  exact (((ContinuousLinearMap.compL ℂ K H K).analyticAt_bilinear _).comp₂
    (hU z hz) hinner).fun_neg

end UV

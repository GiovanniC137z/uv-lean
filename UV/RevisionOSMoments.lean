import UV.RevisionOSWick
import UV.RevisionOSGibbs
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual Gibbs expectations of products of scalar boundary observables.
The input Wick rule is a domain interface for the centered Gaussian fields.
The finite contraction counts and the Gibbs variation are proved separately. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace UV

variable {Ω ι : Type*} [MeasurableSpace Ω]

def osMonomial (F : ι → Ω → ℝ) (xs : List ι) (ω : Ω) : ℝ :=
  (xs.map (fun i ↦ F i ω)).prod

/-- Integrable Gaussian moments with pairwise covariance `K`, specified by
Isserlis' recurrence on finite lists of field slots. -/
structure OSWickMoments (μ : Measure Ω) (F : ι → Ω → ℝ) (K : ι → ι → ℝ) : Prop where
  integrable : ∀ xs, Integrable (osMonomial F xs) μ
  moment : ∀ (n : ℕ) (xs : List ι), xs.length ≤ 2 * n →
    (∫ ω, osMonomial F xs ω ∂μ) = osWickMoment K n xs

def osWickQuartic (v y : ℝ) : ℝ := (y ^ 4 - 6 * v * y ^ 2 + 3 * v ^ 2) / 24

omit [MeasurableSpace Ω] in
theorem osMonomial_append (F : ι → Ω → ℝ) (xs ys : List ι) (ω : Ω) :
    osMonomial F (xs ++ ys) ω = osMonomial F xs ω * osMonomial F ys ω := by
  simp [osMonomial, List.prod_append]

theorem osWickQuartic_insert_integrable {μ : Measure Ω} {F : ι → Ω → ℝ}
    {K : ι → ι → ℝ} (hW : OSWickMoments μ F K) (xs : List ι) (y : ι) :
    Integrable (fun ω ↦ osMonomial F xs ω * osWickQuartic (K y y) (F y ω)) μ := by
  have hi := (((hW.integrable (xs ++ [y, y, y, y])).sub
    ((hW.integrable (xs ++ [y, y])).const_mul (6 * K y y))).add
    ((hW.integrable xs).const_mul (3 * K y y ^ 2))).div_const 24
  apply hi.congr
  refine Eventually.of_forall fun ω ↦ ?_
  simp only [Pi.add_apply, Pi.sub_apply, osMonomial_append, osWickQuartic]
  simp only [osMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

theorem osWickQuartic_insert_mean {μ : Measure Ω} {F : ι → Ω → ℝ}
    {K : ι → ι → ℝ} (hW : OSWickMoments μ F K) (xs : List ι) (y : ι)
    {n : ℕ} (hn : xs.length ≤ 2 * n) :
    (∫ ω, osMonomial F xs ω * osWickQuartic (K y y) (F y ω) ∂μ) =
      (osWickMoment K (n + 2) (xs ++ [y, y, y, y]) -
        6 * K y y * osWickMoment K (n + 1) (xs ++ [y, y]) +
        3 * K y y ^ 2 * osWickMoment K n xs) / 24 := by
  have len4 : (xs ++ [y, y, y, y]).length ≤ 2 * (n + 2) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have len2 : (xs ++ [y, y]).length ≤ 2 * (n + 1) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  calc
    _ = ∫ ω, (osMonomial F (xs ++ [y, y, y, y]) ω -
        (6 * K y y) * osMonomial F (xs ++ [y, y]) ω +
        (3 * K y y ^ 2) * osMonomial F xs ω) / 24 ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun ω ↦ ?_
      simp only [osWickQuartic, osMonomial_append]
      simp only [osMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    _ = _ := by
      have hsub : Integrable (fun ω ↦ osMonomial F (xs ++ [y, y, y, y]) ω -
        6 * K y y * osMonomial F (xs ++ [y, y]) ω) μ :=
        (hW.integrable _).sub ((hW.integrable _).const_mul _)
      rw [integral_div, integral_add hsub ((hW.integrable xs).const_mul (3 * K y y ^ 2)),
        integral_sub (hW.integrable (xs ++ [y, y, y, y])) ((hW.integrable (xs ++ [y, y])).const_mul (6 * K y y)),
        integral_const_mul, integral_const_mul,
        hW.moment (n + 2) _ len4, hW.moment (n + 1) _ len2, hW.moment n _ hn]

theorem osWickRawQuartic_pair_mean {μ : Measure Ω} {F : ι → Ω → ℝ}
    {K : ι → ι → ℝ} (hW : OSWickMoments μ F K) (a b y : ι) (hnull : K a b = 0) :
    (∫ ω, F a ω * F b ω * F y ω ^ 4 / 24 ∂μ) = K y y * (K a y * K b y) / 2 := by
  calc
    _ = (∫ ω, osMonomial F [a, b, y, y, y, y] ω ∂μ) / 24 := by
      rw [← integral_div]
      apply integral_congr_ae
      refine Eventually.of_forall fun ω ↦ ?_
      simp only [osMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    _ = _ := by
      rw [hW.moment 3 _ (by simp)]
      exact osWick_unsubtracted_quartic_contractions K a b y hnull

theorem osWickQuartic_centered_mean {μ : Measure Ω} {F : ι → Ω → ℝ}
    {K : ι → ι → ℝ} (hW : OSWickMoments μ F K) (y : ι) :
    ∫ ω, osWickQuartic (K y y) (F y ω) ∂μ = 0 := by
  have h := osWickQuartic_insert_mean hW [] y (n := 0) (by simp)
  change (∫ ω, 1 * osWickQuartic (K y y) (F y ω) ∂μ) =
    (osWickMoment K 2 [y, y, y, y] - 6 * K y y * osWickMoment K 1 [y, y] +
      3 * K y y ^ 2 * 1) / 24 at h
  rw [mul_one, osWick_ordered_quartic_no_probes, zero_div] at h
  simpa only [one_mul] using h

theorem osWick_centeredQuadratic_free_norm {μ : Measure Ω} {F : ι → Ω → ℝ}
    [IsProbabilityMeasure μ] {K : ι → ι → ℝ} (hW : OSWickMoments μ F K)
    (a b c d : ι) (hac : K a c = 0) (had : K a d = 0) :
    ∫ ω, (F a ω * F b ω - K a b) * (F c ω * F d ω - K c d) ∂μ = 0 := by
  let M := osMonomial F
  calc
    _ = ∫ ω, M [a, b, c, d] ω - K a b * M [c, d] ω -
      K c d * M [a, b] ω + K a b * K c d ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun ω ↦ ?_
      simp [M, osMonomial]
      ring
    _ = _ := by
      have h1 : Integrable (fun ω ↦ M [a, b, c, d] ω - K a b * M [c, d] ω) μ :=
        (hW.integrable [a, b, c, d]).sub ((hW.integrable [c, d]).const_mul (K a b))
      have h2 : Integrable (fun ω ↦ M [a, b, c, d] ω - K a b * M [c, d] ω -
        K c d * M [a, b] ω) μ := h1.sub ((hW.integrable [a, b]).const_mul (K c d))
      rw [integral_add h2 (integrable_const (K a b * K c d)),
        integral_sub h1 ((hW.integrable [a, b]).const_mul (K c d)),
        integral_sub (hW.integrable [a, b, c, d]) ((hW.integrable [c, d]).const_mul (K a b)),
        integral_const_mul, integral_const_mul,
        hW.moment 2 _ (by simp), hW.moment 1 _ (by simp), hW.moment 1 _ (by simp), integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
      exact osWick_centered_boundary_norm K a b c d hac had

/-- The inserted Wick quartic pairs only with all four boundary probes.
Centering constants contribute no contractions. -/
theorem osWickQuartic_centeredQuadratic_mean {μ : Measure Ω} {F : ι → Ω → ℝ}
    {K : ι → ι → ℝ} (hW : OSWickMoments μ F K) (a b c d y : ι) :
    (∫ ω, (F a ω * F b ω - K a b) * (F c ω * F d ω - K c d) *
      osWickQuartic (K y y) (F y ω) ∂μ) = K a y * K b y * K c y * K d y := by
  let M (xs : List ι) (ω : Ω) := osMonomial F xs ω * osWickQuartic (K y y) (F y ω)
  have hI := fun xs ↦ osWickQuartic_insert_integrable hW xs y
  have hA : (∫ ω, M [a, b, c, d] ω ∂μ) = K a y * K b y * K c y * K d y := by
    rw [osWickQuartic_insert_mean hW _ _ (n := 2) (by simp)]
    exact osWick_ordered_quartic_contractions K a b c d y
  have hB (i j : ι) : (∫ ω, M [i, j] ω ∂μ) = 0 := by
    rw [osWickQuartic_insert_mean hW _ _ (n := 1) (by simp)]
    change (osWickMoment K 3 [i, j, y, y, y, y] - 6 * K y y *
      osWickMoment K 2 [i, j, y, y] + 3 * K y y ^ 2 * osWickMoment K 1 [i, j]) / 24 = 0
    rw [osWick_ordered_quartic_two_probes K i j y, zero_div]
  have h0 : (∫ ω, M [] ω ∂μ) = 0 := by
    simpa [M, osMonomial] using osWickQuartic_centered_mean hW y
  calc
    _ = ∫ ω, M [a, b, c, d] ω - K a b * M [c, d] ω -
      K c d * M [a, b] ω + (K a b * K c d) * M [] ω ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun ω ↦ ?_
      simp [M, osMonomial]
      ring
    _ = _ := by
      have h1 : Integrable (fun ω ↦ M [a, b, c, d] ω - K a b * M [c, d] ω) μ :=
        (hI [a, b, c, d]).sub ((hI [c, d]).const_mul (K a b))
      have h2 : Integrable (fun ω ↦ M [a, b, c, d] ω - K a b * M [c, d] ω -
        K c d * M [a, b] ω) μ := h1.sub ((hI [a, b]).const_mul (K c d))
      rw [integral_add h2 ((hI []).const_mul (K a b * K c d)),
        integral_sub h1 ((hI [a, b]).const_mul (K c d)),
        integral_sub (hI [a, b, c, d]) ((hI [c, d]).const_mul (K a b)),
        integral_const_mul, integral_const_mul, integral_const_mul, hA, hB, hB, h0]
      ring

end UV

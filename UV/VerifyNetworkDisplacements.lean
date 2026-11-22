import UV.ContinueNetworkNormalization
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Displacement marks of the literal shared-vertex network. Each mark
differentiates the positive-sign Fourier phase on the same Euclidean
visit coordinates. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology

namespace UV

def networkDisplacementFactors {n : ℕ} (directions : List (NetworkVisitSpace n))
    (x : NetworkVisitSpace n) : ℂ :=
  (directions.map (fun d => Complex.I * (inner ℝ d x : ℂ))).prod

@[simp] theorem networkDisplacementFactors_nil {n : ℕ} (x : NetworkVisitSpace n) :
    networkDisplacementFactors [] x = 1 := rfl

@[simp] theorem networkDisplacementFactors_cons {n : ℕ} (d : NetworkVisitSpace n)
    (directions : List (NetworkVisitSpace n)) (x : NetworkVisitSpace n) :
    networkDisplacementFactors (d :: directions) x =
      (Complex.I * (inner ℝ d x : ℂ)) * networkDisplacementFactors directions x := rfl

theorem networkDisplacementFactors_eq_real_product {n : ℕ}
    (directions : List (NetworkVisitSpace n)) (x : NetworkVisitSpace n) :
    networkDisplacementFactors directions x =
      Complex.I ^ directions.length * (((directions.map fun d => inner ℝ d x).prod : ℝ) : ℂ) := by
  induction directions with
  | nil => simp
  | cons d directions ih =>
      simp only [networkDisplacementFactors_cons, ih, List.length_cons, pow_succ, List.map_cons,
        List.prod_cons, Complex.ofReal_mul]
      ring

theorem networkDisplacementFactors_continuous {n : ℕ} (directions : List (NetworkVisitSpace n)) :
    Continuous (networkDisplacementFactors directions) := by
  induction directions with
  | nil => simpa only [networkDisplacementFactors_nil] using
      (continuous_const : Continuous (fun _ : NetworkVisitSpace n => (1 : ℂ)))
  | cons d directions ih =>
      change Continuous (fun x : NetworkVisitSpace n =>
        (Complex.I * (inner ℝ d x : ℂ)) * networkDisplacementFactors directions x)
      exact (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.inner continuous_id))).mul ih

theorem networkDisplacementFactors_norm_le {n : ℕ} (directions : List (NetworkVisitSpace n))
    (x : NetworkVisitSpace n) :
    ‖networkDisplacementFactors directions x‖ ≤ (directions.map norm).prod * ‖x‖ ^ directions.length := by
  induction directions with
  | nil => simp
  | cons d directions ih =>
      simp only [networkDisplacementFactors_cons, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      calc
        _ ≤ (‖d‖ * ‖x‖) * ((directions.map norm).prod * ‖x‖ ^ directions.length) :=
          mul_le_mul (norm_inner_le_norm _ _) ih (norm_nonneg _) (by positivity)
        _ = _ := by ring

def networkMarkedIntegrand {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (directions : List (NetworkVisitSpace n)) (q x : NetworkVisitSpace n) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ q x : ℂ)) * networkDisplacementFactors directions x *
    (networkSharedKernel src dst m z s x : ℂ)

def networkMarkedFourier {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (directions : List (NetworkVisitSpace n)) (q : NetworkVisitSpace n) : ℂ :=
  ∫ x, networkMarkedIntegrand src dst m z s directions q x

/-- The derivative convention contributes only a unit-modulus factor to
the Fourier integral with the real displacement product inserted. -/
theorem networkMarkedFourier_eq_real_displacement_integral {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (directions : List (NetworkVisitSpace n)) (q : NetworkVisitSpace n) :
    networkMarkedFourier src dst m z s directions q = Complex.I ^ directions.length *
      ∫ x, Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
        (((directions.map fun d => inner ℝ d x).prod : ℝ) : ℂ) *
          (networkSharedKernel src dst m z s x : ℂ) := by
  rw [networkMarkedFourier, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [networkMarkedIntegrand, networkDisplacementFactors_eq_real_product]
  ring

@[simp] theorem networkMarkedFourier_nil {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (q : NetworkVisitSpace n) :
    networkMarkedFourier src dst m z s [] q = networkSharedFourier src dst m z s q := by
  simp only [networkMarkedFourier, networkMarkedIntegrand, networkDisplacementFactors_nil,
    mul_one, networkSharedFourier]

theorem networkMarkedIntegrand_continuous {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (directions : List (NetworkVisitSpace n)) (q : NetworkVisitSpace n) :
    Continuous (networkMarkedIntegrand src dst m z s directions q) := by
  have hphase : Continuous (fun x : NetworkVisitSpace n =>
      Complex.exp (Complex.I * (inner ℝ q x : ℂ))) := by fun_prop
  exact (hphase.mul (networkDisplacementFactors_continuous directions)).mul
    (Complex.continuous_ofReal.comp (networkSharedKernel_continuous src dst m z s))

theorem networkMarkedIntegrand_norm {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (hs : ∀ e, 0 < s e)
    (directions : List (NetworkVisitSpace n)) (q x : NetworkVisitSpace n) :
    ‖networkMarkedIntegrand src dst m z s directions q x‖ =
      ‖networkDisplacementFactors directions x‖ * networkSharedKernel src dst m z s x := by
  simp only [networkMarkedIntegrand, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (networkSharedKernel_nonneg src dst m z s hs x)]

theorem networkMarkedIntegrand_integrable {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (directions : List (NetworkVisitSpace n)) (q : NetworkVisitSpace n) :
    Integrable (networkMarkedIntegrand src dst m z s directions q) := by
  obtain ⟨γ, hγ, hγx⟩ := networkSharedEnergy_coercive G src dst s hG hcover hs
  let D := (directions.map norm).prod
  let P := networkSharedPrefactor m z s
  have hD : 0 ≤ D := by
    unfold D
    induction directions with
    | nil => simp
    | cons d directions ih =>
        exact mul_nonneg (norm_nonneg d) ih
  have hP : 0 ≤ P := networkSharedPrefactor_nonneg m z s hs
  have hI := (integrable_real_degree_gaussian (E := NetworkVisitSpace n) (μ := volume)
    (a := γ / 4) (D := directions.length) (by positivity) (by positivity)).const_mul (D * P)
  apply hI.mono' (networkMarkedIntegrand_continuous src dst m z s directions q).aestronglyMeasurable
  filter_upwards with x
  rw [networkMarkedIntegrand_norm src dst m z s hs, networkSharedKernel_gaussian]
  have hE : Real.exp (-(networkSharedEnergy src dst s x) / 4) ≤
      Real.exp (-(γ / 4 * ‖x‖ ^ 2)) := by
    exact Real.exp_le_exp.mpr (by nlinarith only [hγx x])
  calc
    _ ≤ (D * ‖x‖ ^ directions.length) * (P * Real.exp (-(γ / 4 * ‖x‖ ^ 2))) :=
      mul_le_mul (networkDisplacementFactors_norm_le directions x) (mul_le_mul_of_nonneg_left hE hP)
        (by positivity) (by positivity)
    _ = (D * P) * (‖x‖ ^ directions.length * Real.exp (-(γ / 4 * ‖x‖ ^ 2))) := by ring
    _ ≤ _ := by
      rw [Real.rpow_natCast]
      gcongr
      linarith

private theorem networkMarkedIntegrand_hasDerivAt {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (directions : List (NetworkVisitSpace n)) (q d x : NetworkVisitSpace n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => networkMarkedIntegrand src dst m z s directions (q + u • d) x)
      (networkMarkedIntegrand src dst m z s (d :: directions) (q + t • d) x) t := by
  have hlin : HasDerivAt (fun u : ℝ => inner ℝ (q + u • d) x) (inner ℝ d x) t := by
    simpa only [inner_add_left, real_inner_smul_left, id, one_mul] using
      ((hasDerivAt_id t).mul_const (inner ℝ d x)).const_add (inner ℝ q x)
  have h := (((hlin.ofReal_comp.const_mul Complex.I).cexp).mul_const
    (networkDisplacementFactors directions x)).mul_const
      (networkSharedKernel src dst m z s x : ℂ)
  convert h using 1
  simp only [networkMarkedIntegrand, networkDisplacementFactors_cons]
  ring

/-- A directional derivative of the actual coherent vertex integral
inserts the corresponding displacement readout inside that integral. -/
theorem networkMarkedFourier_hasDerivAt {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (directions : List (NetworkVisitSpace n)) (q d : NetworkVisitSpace n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => networkMarkedFourier src dst m z s directions (q + u • d))
      (networkMarkedFourier src dst m z s (d :: directions) (q + t • d)) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (x₀ := t) (ε := 1) zero_lt_one
    (Eventually.of_forall (fun u =>
      (networkMarkedIntegrand_continuous src dst m z s directions (q + u • d)).aestronglyMeasurable))
    (networkMarkedIntegrand_integrable G src dst m z s hG hcover hs directions (q + t • d))
    (networkMarkedIntegrand_continuous src dst m z s (d :: directions) (q + t • d)).aestronglyMeasurable
    (bound := fun x => ‖networkMarkedIntegrand src dst m z s (d :: directions) q x‖)
    (Eventually.of_forall (fun x u _ => by
      dsimp only
      rw [networkMarkedIntegrand_norm src dst m z s hs, networkMarkedIntegrand_norm src dst m z s hs]))
    (networkMarkedIntegrand_integrable G src dst m z s hG hcover hs (d :: directions) q).norm
    (Eventually.of_forall (fun x u _ => networkMarkedIntegrand_hasDerivAt src dst m z s directions q d x u))).2

end UV

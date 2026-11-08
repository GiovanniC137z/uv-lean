import UV.CliffordContact
import UV.Convergence
import Mathlib.MeasureTheory.Group.Integral

/-! Exact bare-vertex Ward contraction and its common-domain identity.
The two contracted terms are retained under a single integral. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise

namespace UV

def bareWardTensor (F : ℝ → ℝ) (m : ℝ) (Q : DiracMomentum)
    (μ ν : Fin 4) (k : DiracMomentum) : ℂ :=
  (F (‖k‖ ^ 2) * F (‖k + Q‖ ^ 2) : ℝ) *
    Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) ν)

def bareWardContracted (F : ℝ → ℝ) (m : ℝ) (Q : DiracMomentum)
    (ν : Fin 4) (k : DiracMomentum) : ℂ :=
  (F (‖k‖ ^ 2) * F (‖k + Q‖ ^ 2) : ℝ) *
    (Matrix.trace (bareWardLine m k ν) - Matrix.trace (bareWardLine m (k + Q) ν))

def bareWardRemainder (F : ℝ → ℝ) (m : ℝ) (Q : DiracMomentum)
    (ν : Fin 4) (k : DiracMomentum) : ℂ :=
  (F (‖k‖ ^ 2) * (F (‖k + Q‖ ^ 2) - F (‖k - Q‖ ^ 2)) : ℝ) *
    Matrix.trace (bareWardLine m k ν)

def bareWardCutoffTerm (F : ℝ → ℝ) (m : ℝ) (Q : DiracMomentum)
    (ν : Fin 4) (k : DiracMomentum) : ℂ :=
  (F (‖k‖ ^ 2) * F (‖k - Q‖ ^ 2) : ℝ) * Matrix.trace (bareWardLine m k ν)

theorem bare_gamma_contraction (Q : DiracMomentum) :
    (∑ μ, (Q μ : ℂ) • (Complex.I • euclideanGamma μ)) = Complex.I • diracSlash Q := by
  simp only [diracSlash, Finset.smul_sum, smul_smul]
  congr 1
  funext μ
  rw [mul_comm]

theorem freeDiracSymbol_add_sub (m : ℝ) (k Q : DiracMomentum) :
    freeDiracSymbol m (k + Q) - freeDiracSymbol m k = Complex.I • diracSlash Q := by
  simp only [freeDiracSymbol, diracSlash_add, smul_add]
  abel

theorem bare_ward_trace_contraction {m : ℝ} (hm : 0 < m)
    (Q k : DiracMomentum) (ν : Fin 4) :
    (∑ μ, (Q μ : ℂ) * Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      Matrix.trace (bareWardLine m k ν) - Matrix.trace (bareWardLine m (k + Q) ν) := by
  have hsum : (∑ μ, (Q μ : ℂ) •
      (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      (freeDiracSymbol m (k + Q) - freeDiracSymbol m k) * freeDiracPropagator m k *
        bareWardLine m (k + Q) ν := by
    simp only [bareWardLine, ← smul_mul_assoc, ← Finset.sum_mul]
    rw [bare_gamma_contraction, freeDiracSymbol_add_sub]
  have htrace : (∑ μ, (Q μ : ℂ) * Matrix.trace
      (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      Matrix.trace (∑ μ, (Q μ : ℂ) •
        (bareWardLine m k μ * bareWardLine m (k + Q) ν)) := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul]
  rw [htrace]
  rw [hsum, sub_mul, sub_mul, Matrix.trace_sub]
  congr 1
  · have hcyc := Matrix.trace_mul_cycle (freeDiracSymbol m (k + Q))
      (freeDiracPropagator m k) (bareWardLine m (k + Q) ν)
    rw [hcyc]
    unfold bareWardLine
    rw [Matrix.mul_assoc (Complex.I • euclideanGamma ν) (freeDiracPropagator m (k + Q))
      (freeDiracSymbol m (k + Q)), freeDiracPropagator_mul_symbol hm (k + Q), Matrix.mul_one]
  · rw [freeDiracSymbol_mul_propagator hm k, Matrix.one_mul]

theorem bare_ward_tensor_contraction {m : ℝ} (hm : 0 < m)
    (F : ℝ → ℝ) (Q k : DiracMomentum) (ν : Fin 4) :
    (∑ μ, (Q μ : ℂ) * bareWardTensor F m Q μ ν k) = bareWardContracted F m Q ν k := by
  unfold bareWardTensor bareWardContracted
  rw [show (∑ μ, (Q μ : ℂ) *
      ((F (‖k‖ ^ 2) * F (‖k + Q‖ ^ 2) : ℝ) *
      Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) ν))) =
      (F (‖k‖ ^ 2) * F (‖k + Q‖ ^ 2) : ℝ) *
      ∑ μ, (Q μ : ℂ) * Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) ν) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    ring]
  rw [bare_ward_trace_contraction hm Q k ν]

theorem bare_ward_contracted_integrable {m : ℝ} (hm : 0 < m)
    (F : ℝ → ℝ) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor F m Q μ ν)) (ν : Fin 4) :
    Integrable (bareWardContracted F m Q ν) := by
  have hi := integrable_finset_sum Finset.univ (fun μ _ => (hH μ ν).const_mul (Q μ : ℂ))
  exact hi.congr (Eventually.of_forall (fun k => bare_ward_tensor_contraction hm F Q k ν))

theorem bare_ward_pointwise_common_domain (F : ℝ → ℝ) (m : ℝ) (Q : DiracMomentum)
    (ν : Fin 4) (k : DiracMomentum) :
    bareWardContracted F m Q ν k = bareWardRemainder F m Q ν k +
      bareWardCutoffTerm F m Q ν k - bareWardCutoffTerm F m Q ν (k + Q) := by
  have he : k + Q - Q = k := add_sub_cancel_right k Q
  unfold bareWardContracted bareWardRemainder bareWardCutoffTerm
  rw [he]
  push_cast
  ring

theorem bareWardLine_trace_continuous {m : ℝ} (hm : 0 < m) (ν : Fin 4) :
    Continuous (fun k : DiracMomentum => Matrix.trace (bareWardLine m k ν)) := by
  simp_rw [bareWardLine_trace]
  apply Complex.continuous_ofReal.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro k
    positivity

theorem bareWardCutoffTerm_continuous {m : ℝ} (hm : 0 < m)
    {F : ℝ → ℝ} (hF : Continuous F) (Q : DiracMomentum) (ν : Fin 4) :
    Continuous (bareWardCutoffTerm F m Q ν) := by
  unfold bareWardCutoffTerm
  apply Continuous.mul
  · apply Complex.continuous_ofReal.comp
    exact (hF.comp (continuous_norm.pow 2)).mul
      (hF.comp (((continuous_id.sub continuous_const).norm).pow 2))
  · exact bareWardLine_trace_continuous hm ν

theorem bareWardRemainder_continuous {m : ℝ} (hm : 0 < m)
    {F : ℝ → ℝ} (hF : Continuous F) (Q : DiracMomentum) (ν : Fin 4) :
    Continuous (bareWardRemainder F m Q ν) := by
  unfold bareWardRemainder
  apply Continuous.mul
  · apply Complex.continuous_ofReal.comp
    exact (hF.comp (continuous_norm.pow 2)).mul
      ((hF.comp (((continuous_id.add continuous_const).norm).pow 2)).sub
        (hF.comp (((continuous_id.sub continuous_const).norm).pow 2)))
  · exact bareWardLine_trace_continuous hm ν

/-- The common bounded-domain identity. The only integrability used here is
local continuity on compact balls; no global split-term L1 is required. -/
theorem bare_ward_finite_cutoff_identity {m : ℝ} (hm : 0 < m)
    {F : ℝ → ℝ} (hF : Continuous F) (Q : DiracMomentum) (ν : Fin 4) (R : ℝ) :
    (∫ k in ball (0 : DiracMomentum) R, bareWardContracted F m Q ν k) =
      (∫ k in ball (0 : DiracMomentum) R, bareWardRemainder F m Q ν k) +
      (∫ k in ball (0 : DiracMomentum) R, bareWardCutoffTerm F m Q ν k) -
      ∫ k in ball (0 : DiracMomentum) R, bareWardCutoffTerm F m Q ν (k + Q) := by
  have hC := bareWardCutoffTerm_continuous hm hF Q ν
  have hCshift : Continuous (fun k => bareWardCutoffTerm F m Q ν (k + Q)) :=
    hC.comp (continuous_id.add continuous_const)
  have hJ := bareWardRemainder_continuous hm hF Q ν
  have hiC := (hC.continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : DiracMomentum) R)).mono_set
    ball_subset_closedBall
  have hiCs := (hCshift.continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : DiracMomentum) R)).mono_set
    ball_subset_closedBall
  have hiJ := (hJ.continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : DiracMomentum) R)).mono_set
    ball_subset_closedBall
  calc
    _ = ∫ k in ball (0 : DiracMomentum) R,
        bareWardRemainder F m Q ν k + bareWardCutoffTerm F m Q ν k -
          bareWardCutoffTerm F m Q ν (k + Q) :=
      integral_congr_ae (Eventually.of_forall (bare_ward_pointwise_common_domain F m Q ν))
    _ = _ := by
      have hh := integral_sub (hiJ.add hiC) hiCs
      simp only [Pi.add_apply] at hh
      rw [integral_add hiJ hiC] at hh
      exact hh

theorem nonnegative_laplace_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun τ => Real.exp (-τ * u)) ρ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (by fun_prop : Continuous (fun τ : ℝ => Real.exp (-τ * u))).aestronglyMeasurable
  · filter_upwards [hp] with τ hτ
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) hu)

theorem nonnegative_laplace_antitone (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    laplace ρ v ≤ laplace ρ u := by
  apply integral_mono_ae (nonnegative_laplace_integrable ρ hp (hu.trans huv))
    (nonnegative_laplace_integrable ρ hp hu)
  filter_upwards [hp] with τ hτ
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left huv (neg_nonpos.mpr hτ))

theorem nonnegative_laplace_ordered_difference (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    laplace ρ u - laplace ρ v ≤ (2 * (v - u) / u) * laplace ρ (u / 2) := by
  have hiu := nonnegative_laplace_integrable ρ hp hu.le
  have hiv := nonnegative_laplace_integrable ρ hp (hu.le.trans huv)
  have hih := nonnegative_laplace_integrable ρ hp (show 0 ≤ u / 2 by linarith)
  unfold laplace
  rw [← integral_sub hiu hiv, ← integral_const_mul]
  apply integral_mono_ae (hiu.sub hiv) (hih.const_mul _)
  filter_upwards [hp] with τ hτ
  have hlin : 1 - Real.exp (-τ * (v - u)) ≤ τ * (v - u) := by
    linarith [Real.add_one_le_exp (-τ * (v - u))]
  have hsplit : Real.exp (-τ * v) = Real.exp (-τ * u) * Real.exp (-τ * (v - u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : Real.exp (-τ * u) = Real.exp (-(u / 2 * τ)) * Real.exp (-τ * (u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow := pow_mul_exp_neg_le (show 0 < u / 2 by linarith) hτ 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at hpow
  simp only [Pi.sub_apply]
  rw [hsplit]
  calc
    _ = Real.exp (-τ * u) * (1 - Real.exp (-τ * (v - u))) := by ring
    _ ≤ Real.exp (-τ * u) * (τ * (v - u)) :=
      mul_le_mul_of_nonneg_left hlin (Real.exp_nonneg _)
    _ = (v - u) * (τ * Real.exp (-(u / 2 * τ))) * Real.exp (-τ * (u / 2)) := by rw [hhalf]; ring
    _ ≤ (v - u) * (1 / (u / 2)) * Real.exp (-τ * (u / 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr huv))
        (Real.exp_nonneg _)
    _ = _ := by ring

theorem nonnegative_laplace_difference (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |laplace ρ u - laplace ρ v| ≤
      (2 * |u - v| / min u v) * laplace ρ (min u v / 2) := by
  rcases le_total u v with huv | hvu
  · have hn := nonnegative_laplace_antitone ρ hp hu.le huv
    rw [abs_of_nonneg (sub_nonneg.mpr hn), min_eq_left huv,
      abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
    exact nonnegative_laplace_ordered_difference ρ hp hu huv
  · have hn := nonnegative_laplace_antitone ρ hp hv.le hvu
    rw [abs_of_nonpos (sub_nonpos.mpr hn), neg_sub, min_eq_right hvu,
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact nonnegative_laplace_ordered_difference ρ hp hv hvu

def wardLaplaceKernel (ρ : Measure ℝ) (a u : ℝ) : ℝ := laplace ρ (a ^ 2 * max u 0)

theorem wardLaplaceKernel_continuous (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) : Continuous (wardLaplaceKernel ρ a) := by
  unfold wardLaplaceKernel laplace
  apply continuous_of_dominated (bound := fun _τ : ℝ => (1 : ℝ))
  · intro u
    exact (by fun_prop : Continuous (fun τ : ℝ => Real.exp (-τ * (a ^ 2 * max u 0)))).aestronglyMeasurable
  · intro u
    filter_upwards [hp] with τ hτ
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ)
      (mul_nonneg (sq_nonneg a) (le_max_right u 0)))
  · exact integrable_const _
  · exact Eventually.of_forall (fun τ => by fun_prop)

theorem wardLaplaceKernel_eq (ρ : Measure ℝ) (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    wardLaplaceKernel ρ a u = laplace ρ (a ^ 2 * u) := by
  rw [wardLaplaceKernel, max_eq_left hu]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem bare_ward_numerator_diagonal_trace_sum (m : ℝ) (k l : DiracMomentum) :
    (∑ μ, Matrix.trace
      (((Complex.I • euclideanGamma μ) * freeDiracNumerator m k) *
        ((Complex.I • euclideanGamma μ) * freeDiracNumerator m l))) =
      ((-8 * ((∑ i : Fin 4, k i * l i) + 2 * m ^ 2) : ℝ) : ℂ) := by
  simp_rw [bareWardNumerator_eq_explicit]
  simp [bareWardNumeratorExplicit, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem bare_ward_diagonal_trace_sum (m : ℝ) (k l : DiracMomentum) :
    (∑ μ, Matrix.trace (bareWardLine m k μ * bareWardLine m l μ)) =
      ((-8 * ((∑ i : Fin 4, k i * l i) + 2 * m ^ 2) /
        ((‖k‖ ^ 2 + m ^ 2) * (‖l‖ ^ 2 + m ^ 2)) : ℝ) : ℂ) := by
  have hline (q : DiracMomentum) (j : Fin 4) : bareWardLine m q j =
      ((‖q‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹ •
        ((Complex.I • euclideanGamma j) * freeDiracNumerator m q) := by
    simp only [bareWardLine, freeDiracPropagator, Matrix.mul_smul]
  simp_rw [hline, smul_mul_smul, Matrix.trace_smul]
  rw [← Finset.smul_sum, bare_ward_numerator_diagonal_trace_sum]
  push_cast
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem bare_ward_tensor_diagonal_sum (F : ℝ → ℝ) (m : ℝ) (Q k : DiracMomentum) :
    (∑ μ, bareWardTensor F m Q μ μ k) =
      ((F (‖k‖ ^ 2) * F (‖k + Q‖ ^ 2) *
        (-8 * ((∑ i : Fin 4, k i * (k + Q) i) + 2 * m ^ 2) /
          ((‖k‖ ^ 2 + m ^ 2) * (‖k + Q‖ ^ 2 + m ^ 2))) : ℝ) : ℂ) := by
  simp only [bareWardTensor, ← Finset.mul_sum, bare_ward_diagonal_trace_sum,
    Complex.ofReal_mul]

/-- Summing diagonal components yields a uniform radial lower bound, avoiding
an auxiliary angular sector in the tail converse. -/
theorem bare_ward_trace_sum_tail_lower {m : ℝ} (hm : 0 ≤ m)
    (Q k : DiracMomentum) (hk : 0 < ‖k‖) (hQ : 2 * ‖Q‖ ≤ ‖k‖) (hmk : m ≤ ‖k‖) :
    1 / (2 * ‖k‖ ^ 2) ≤ ‖∑ μ, Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) μ)‖ := by
  have hinner : (∑ i : Fin 4, k i * (k + Q) i) =
      ‖k‖ ^ 2 + inner ℝ k Q := by
    have hh : (∑ i : Fin 4, k i * (k + Q) i) = inner ℝ k (k + Q) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [hh, inner_add_right, real_inner_self_eq_norm_sq]
  have hdot : ‖k‖ ^ 2 / 2 ≤ (∑ i : Fin 4, k i * (k + Q) i) + 2 * m ^ 2 := by
    rw [hinner]
    have hh := (abs_le.mp (abs_real_inner_le_norm k Q)).1
    have hmul := mul_le_mul_of_nonneg_left hQ (norm_nonneg k)
    nlinarith [sq_nonneg m]
  have hplus : ‖k + Q‖ ≤ 3 * ‖k‖ / 2 := by
    have hh := norm_add_le k Q
    linarith
  have hden₁ : ‖k‖ ^ 2 + m ^ 2 ≤ 2 * ‖k‖ ^ 2 := by nlinarith
  have hden₂ : ‖k + Q‖ ^ 2 + m ^ 2 ≤ 4 * ‖k‖ ^ 2 := by
    have hh := mul_self_le_mul_self (norm_nonneg (k + Q)) hplus
    nlinarith
  have hden : (‖k‖ ^ 2 + m ^ 2) * (‖k + Q‖ ^ 2 + m ^ 2) ≤ 8 * (‖k‖ ^ 2) ^ 2 := by
    have hh := mul_le_mul hden₁ hden₂ (by positivity : 0 ≤ ‖k + Q‖ ^ 2 + m ^ 2)
      (by positivity : 0 ≤ 2 * ‖k‖ ^ 2)
    nlinarith
  have hkp : 0 < ‖k + Q‖ := by
    have hh := norm_sub_norm_le k (-Q)
    rw [norm_neg, sub_neg_eq_add] at hh
    linarith
  have hdpos : 0 < (‖k‖ ^ 2 + m ^ 2) * (‖k + Q‖ ^ 2 + m ^ 2) := by positivity
  rw [bare_ward_diagonal_trace_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hdpos, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 8),
    abs_of_nonneg ((by positivity : 0 ≤ ‖k‖ ^ 2 / 2).trans hdot)]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * ‖k‖ ^ 2) hdpos).mpr
  have hh := mul_le_mul_of_nonneg_left hdot (by positivity : 0 ≤ 16 * ‖k‖ ^ 2)
  nlinarith

theorem bareWardLine_trace_norm_bound (m : ℝ) (k : DiracMomentum) (ν : Fin 4)
    (hk : 0 < ‖k‖) : ‖Matrix.trace (bareWardLine m k ν)‖ ≤ 4 / ‖k‖ := by
  have hcoord : |k ν| ≤ ‖k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le k ν
  rw [bareWardLine_trace, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (by positivity : 0 < ‖k‖ ^ 2 + m ^ 2)]
  calc
    _ ≤ 4 * ‖k‖ / ‖k‖ ^ 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < ‖k‖ ^ 2 + m ^ 2) (by positivity : 0 < ‖k‖ ^ 2)).mpr
      have hh := mul_le_mul_of_nonneg_right hcoord (by positivity : 0 ≤ 4 * ‖k‖ ^ 2)
      nlinarith [mul_nonneg (norm_nonneg k) (sq_nonneg m)]
    _ = _ := by field_simp

theorem laplace_bare_ward_remainder_tail (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q k : DiracMomentum) (ν : Fin 4)
    (hk : 0 < ‖k‖) (hQ : 2 * ‖Q‖ ≤ ‖k‖) :
    ‖bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν k‖ ≤
      (128 * ‖Q‖ / ‖k‖ ^ 2) * laplace ρ (‖k‖ ^ 2 / 8) ^ 2 := by
  have hplus : ‖k‖ / 2 ≤ ‖k + Q‖ := by
    have hh := norm_sub_norm_le k (-Q)
    rw [norm_neg, sub_neg_eq_add] at hh
    linarith
  have hminus : ‖k‖ / 2 ≤ ‖k - Q‖ := by
    have hh := norm_sub_norm_le k Q
    linarith
  have hpplus : 0 < ‖k + Q‖ := by linarith
  have hpminus : 0 < ‖k - Q‖ := by linarith
  have hmin : ‖k‖ ^ 2 / 4 ≤ min (‖k + Q‖ ^ 2) (‖k - Q‖ ^ 2) := by
    apply le_min
    · have hh := mul_self_le_mul_self (by positivity : 0 ≤ ‖k‖ / 2) hplus
      nlinarith
    · have hh := mul_self_le_mul_self (by positivity : 0 ≤ ‖k‖ / 2) hminus
      nlinarith
  have hdiffnorm : |‖k + Q‖ ^ 2 - ‖k - Q‖ ^ 2| ≤ 4 * ‖k‖ * ‖Q‖ := by
    rw [norm_add_sq_real, norm_sub_sq_real,
      show ‖k‖ ^ 2 + 2 * inner ℝ k Q + ‖Q‖ ^ 2 -
        (‖k‖ ^ 2 - 2 * inner ℝ k Q + ‖Q‖ ^ 2) = 4 * inner ℝ k Q by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm k Q) (by norm_num)).trans_eq (by ring)
  have hcoef : 2 * |‖k + Q‖ ^ 2 - ‖k - Q‖ ^ 2| /
      min (‖k + Q‖ ^ 2) (‖k - Q‖ ^ 2) ≤ 32 * ‖Q‖ / ‖k‖ := by
    calc
      _ ≤ 2 * |‖k + Q‖ ^ 2 - ‖k - Q‖ ^ 2| / (‖k‖ ^ 2 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hmin
      _ ≤ (8 * ‖k‖ * ‖Q‖) / (‖k‖ ^ 2 / 4) :=
        div_le_div_of_nonneg_right (by nlinarith [hdiffnorm]) (by positivity)
      _ = _ := by field_simp; ring
  have hF0 (u : ℝ) : 0 ≤ laplace ρ u := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hFmin : laplace ρ (min (‖k + Q‖ ^ 2) (‖k - Q‖ ^ 2) / 2) ≤ laplace ρ (‖k‖ ^ 2 / 8) :=
    nonnegative_laplace_antitone ρ hp (by positivity) (by linarith)
  have hFdiff : |laplace ρ (‖k + Q‖ ^ 2) - laplace ρ (‖k - Q‖ ^ 2)| ≤
      (32 * ‖Q‖ / ‖k‖) * laplace ρ (‖k‖ ^ 2 / 8) := by
    exact (nonnegative_laplace_difference ρ hp (by positivity) (by positivity)).trans
      (mul_le_mul hcoef hFmin (hF0 _) (by positivity))
  have hFk : laplace ρ (‖k‖ ^ 2) ≤ laplace ρ (‖k‖ ^ 2 / 8) :=
    nonnegative_laplace_antitone ρ hp (by positivity) (by nlinarith [sq_nonneg ‖k‖])
  unfold bareWardRemainder
  rw [wardLaplaceKernel_eq ρ 1 (sq_nonneg _), wardLaplaceKernel_eq ρ 1 (sq_nonneg _),
    wardLaplaceKernel_eq ρ 1 (sq_nonneg _)]
  simp only [one_pow, one_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF0 _)]
  calc
    _ ≤ (laplace ρ (‖k‖ ^ 2 / 8) *
        ((32 * ‖Q‖ / ‖k‖) * laplace ρ (‖k‖ ^ 2 / 8))) * (4 / ‖k‖) := by
      apply mul_le_mul
      · exact mul_le_mul hFk hFdiff (abs_nonneg _) (hF0 _)
      · exact bareWardLine_trace_norm_bound m k ν hk
      · exact norm_nonneg _
      · exact mul_nonneg (hF0 _) (mul_nonneg (by positivity) (hF0 _))
    _ = _ := by ring

theorem laplace_bare_ward_scaled_tensor_lower (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 ≤ m) (Q k : DiracMomentum)
    (hk : 0 < ‖k‖) (hQ : 16 * ‖Q‖ ≤ ‖k‖) (hmk : 8 * m ≤ ‖k‖) :
    (32 / ‖k‖ ^ 2) * laplace ρ (‖k‖ ^ 2 / 8) ^ 2 ≤
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖ := by
  let j : DiracMomentum := (1 / 8 : ℝ) • k
  have hjnorm : ‖j‖ = ‖k‖ / 8 := by
    dsimp [j]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    ring
  have hjpos : 0 < ‖j‖ := by rw [hjnorm]; positivity
  have hQj : 2 * ‖Q‖ ≤ ‖j‖ := by rw [hjnorm]; linarith
  have hmj : m ≤ ‖j‖ := by rw [hjnorm]; linarith
  have hnormplus : ‖j + Q‖ ≤ ‖k‖ / 4 := by
    have hh := norm_add_le j Q
    rw [hjnorm] at hh
    linarith
  have hjkin : ‖j‖ ^ 2 ≤ ‖k‖ ^ 2 / 8 := by rw [hjnorm]; nlinarith [sq_nonneg ‖k‖]
  have hjpluskin : ‖j + Q‖ ^ 2 ≤ ‖k‖ ^ 2 / 8 := by
    have hh := mul_self_le_mul_self (norm_nonneg (j + Q)) hnormplus
    nlinarith [sq_nonneg ‖k‖]
  have hF0 (u : ℝ) : 0 ≤ laplace ρ u := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hFj := nonnegative_laplace_antitone ρ hp (sq_nonneg ‖j‖) hjkin
  have hFjp := nonnegative_laplace_antitone ρ hp (sq_nonneg ‖j + Q‖) hjpluskin
  have hprod : laplace ρ (‖k‖ ^ 2 / 8) ^ 2 ≤ laplace ρ (‖j‖ ^ 2) * laplace ρ (‖j + Q‖ ^ 2) := by
    simpa only [pow_two] using mul_le_mul hFj hFjp (hF0 _) (hF0 _)
  have htr := bare_ward_trace_sum_tail_lower hm Q j hjpos hQj hmj
  have hnorm : ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ j‖ =
      (laplace ρ (‖j‖ ^ 2) * laplace ρ (‖j + Q‖ ^ 2)) *
      ‖∑ μ, Matrix.trace (bareWardLine m j μ * bareWardLine m (j + Q) μ)‖ := by
    simp only [bareWardTensor, ← Finset.mul_sum]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [wardLaplaceKernel_eq ρ 1 (sq_nonneg _), wardLaplaceKernel_eq ρ 1 (sq_nonneg _)]
    simp only [one_pow, one_mul, abs_mul, abs_of_nonneg (hF0 _)]
  rw [← show j = (1 / 8 : ℝ) • k from rfl, hnorm]
  calc
    _ = laplace ρ (‖k‖ ^ 2 / 8) ^ 2 * (1 / (2 * ‖j‖ ^ 2)) := by rw [hjnorm]; ring
    _ ≤ _ := mul_le_mul hprod htr (by positivity) (mul_nonneg (hF0 _) (hF0 _))

/-- Absolute integrability of the actual scalar remainder follows from the
original tensor components, with no separate L1 assumption on its two terms. -/
theorem laplace_bare_ward_remainder_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 < m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) : Integrable (bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν) := by
  let J := bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν
  have hJ : Continuous J := bareWardRemainder_continuous hm (wardLaplaceKernel_continuous ρ hp 1) Q ν
  have hsum : Integrable (fun k : DiracMomentum => ∑ μ,
      bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ k) :=
    integrable_finset_sum _ (fun μ _ => hH μ μ)
  have hmajor : Integrable (fun k : DiracMomentum => (4 * ‖Q‖) *
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖) :=
    (hsum.comp_smul (by norm_num : (1 / 8 : ℝ) ≠ 0)).norm.const_mul _
  let K : ℝ := 16 * ‖Q‖ + 8 * m + 1
  have hlocal : IntegrableOn J (closedBall (0 : DiracMomentum) K) :=
    hJ.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have htail : IntegrableOn J (closedBall (0 : DiracMomentum) K)ᶜ := by
    apply hmajor.integrableOn.mono' hJ.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with k hk
    have hknorm : K < ‖k‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hk
    have hkpos : 0 < ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hQk : 16 * ‖Q‖ ≤ ‖k‖ := by dsimp [K] at hknorm; linarith
    have hmk : 8 * m ≤ ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hsmall := laplace_bare_ward_remainder_tail ρ hp m Q k ν hkpos (by linarith [norm_nonneg Q])
    have hlarge := mul_le_mul_of_nonneg_left
      (laplace_bare_ward_scaled_tensor_lower ρ hp hm.le Q k hkpos hQk hmk)
      (by positivity : 0 ≤ 4 * ‖Q‖)
    apply hsmall.trans
    convert hlarge using 1
    ring
  have hall := hlocal.union htail
  simpa only [union_compl_self, integrableOn_univ] using hall

theorem laplace_bare_ward_weighted_cutoff_tail (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q k : DiracMomentum) (ν : Fin 4)
    (hk : 0 < ‖k‖) (hQ : 2 * ‖Q‖ ≤ ‖k‖) :
    ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ / (1 + ‖k‖) ≤
      (4 / ‖k‖ ^ 2) * laplace ρ (‖k‖ ^ 2 / 8) ^ 2 := by
  have hminus : ‖k‖ / 2 ≤ ‖k - Q‖ := by
    have hh := norm_sub_norm_le k Q
    linarith
  have hkin : ‖k‖ ^ 2 / 8 ≤ ‖k - Q‖ ^ 2 := by
    have hh := mul_self_le_mul_self (by positivity : 0 ≤ ‖k‖ / 2) hminus
    nlinarith [sq_nonneg ‖k‖]
  have hF0 (u : ℝ) : 0 ≤ laplace ρ u := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hFminus := nonnegative_laplace_antitone ρ hp (by positivity : 0 ≤ ‖k‖ ^ 2 / 8) hkin
  have hFk := nonnegative_laplace_antitone ρ hp (by positivity : 0 ≤ ‖k‖ ^ 2 / 8)
    (by nlinarith [sq_nonneg ‖k‖] : ‖k‖ ^ 2 / 8 ≤ ‖k‖ ^ 2)
  have hC : ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ ≤
      laplace ρ (‖k‖ ^ 2 / 8) ^ 2 * (4 / ‖k‖) := by
    unfold bareWardCutoffTerm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      wardLaplaceKernel_eq ρ 1 (sq_nonneg _), wardLaplaceKernel_eq ρ 1 (sq_nonneg _)]
    simp only [one_pow, one_mul, abs_mul, abs_of_nonneg (hF0 _)]
    apply mul_le_mul
    · simpa only [pow_two] using mul_le_mul hFk hFminus (hF0 _) (hF0 _)
    · exact bareWardLine_trace_norm_bound m k ν hk
    · exact norm_nonneg _
    · positivity
  calc
    _ ≤ (laplace ρ (‖k‖ ^ 2 / 8) ^ 2 * (4 / ‖k‖)) / (1 + ‖k‖) :=
      div_le_div_of_nonneg_right hC (by positivity)
    _ = (4 * laplace ρ (‖k‖ ^ 2 / 8) ^ 2) / (‖k‖ * (1 + ‖k‖)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (4 * laplace ρ (‖k‖ ^ 2 / 8) ^ 2) / ‖k‖ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [norm_nonneg k])
    _ = _ := by ring

theorem laplace_bare_ward_weighted_cutoff_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 < m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) : Integrable (fun k =>
      ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ / (1 + ‖k‖)) := by
  let W : DiracMomentum → ℝ := fun k =>
    ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ / (1 + ‖k‖)
  have hW : Continuous W := by
    apply (bareWardCutoffTerm_continuous hm (wardLaplaceKernel_continuous ρ hp 1) Q ν).norm.div
      (continuous_const.add continuous_norm)
    intro k
    positivity
  have hsum : Integrable (fun k : DiracMomentum => ∑ μ,
      bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ k) :=
    integrable_finset_sum _ (fun μ _ => hH μ μ)
  have hmajor : Integrable (fun k : DiracMomentum => (1 / 8 : ℝ) *
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖) :=
    (hsum.comp_smul (by norm_num : (1 / 8 : ℝ) ≠ 0)).norm.const_mul _
  let K : ℝ := 16 * ‖Q‖ + 8 * m + 1
  have hlocal : IntegrableOn W (closedBall (0 : DiracMomentum) K) :=
    hW.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have htail : IntegrableOn W (closedBall (0 : DiracMomentum) K)ᶜ := by
    apply hmajor.integrableOn.mono' hW.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with k hk
    have hknorm : K < ‖k‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hk
    have hkpos : 0 < ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hQk : 16 * ‖Q‖ ≤ ‖k‖ := by dsimp [K] at hknorm; linarith
    have hmk : 8 * m ≤ ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    rw [Real.norm_of_nonneg (by dsimp [W]; positivity : 0 ≤ W k)]
    have hsmall := laplace_bare_ward_weighted_cutoff_tail ρ hp m Q k ν hkpos (by linarith [norm_nonneg Q])
    have hlarge := mul_le_mul_of_nonneg_left
      (laplace_bare_ward_scaled_tensor_lower ρ hp hm.le Q k hkpos hQk hmk)
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    apply hsmall.trans
    convert hlarge using 1
    ring
  have hall := hlocal.union htail
  simpa only [union_compl_self, integrableOn_univ] using hall


def wardTentCutoff (R : ℝ) (k : DiracMomentum) : ℝ := max (1 - ‖k‖ / R) 0

theorem wardTentCutoff_continuous (R : ℝ) : Continuous (wardTentCutoff R) := by
  unfold wardTentCutoff
  fun_prop

theorem wardTentCutoff_bounds {R : ℝ} (hR : 0 < R) (k : DiracMomentum) :
    0 ≤ wardTentCutoff R k ∧ wardTentCutoff R k ≤ 1 := by
  unfold wardTentCutoff
  exact ⟨le_max_right _ _, max_le (sub_le_self 1 (div_nonneg (norm_nonneg k) hR.le)) zero_le_one⟩

theorem wardTentCutoff_zero {R : ℝ} (hR : 0 < R) {k : DiracMomentum} (hk : R ≤ ‖k‖) :
    wardTentCutoff R k = 0 := by
  unfold wardTentCutoff
  apply max_eq_right
  exact sub_nonpos.mpr ((one_le_div hR).mpr hk)

theorem wardTentCutoff_shift_difference {R : ℝ} (hR : 0 < R) (Q k : DiracMomentum) :
    |wardTentCutoff R k - wardTentCutoff R (k - Q)| ≤ ‖Q‖ / R := by
  have hh := abs_norm_sub_norm_le k (k - Q)
  have he : k - (k - Q) = Q := by abel
  rw [he] at hh
  calc
    _ ≤ |(1 - ‖k‖ / R) - (1 - ‖k - Q‖ / R)| := abs_max_sub_max_le_abs _ _ 0
    _ = |‖k‖ - ‖k - Q‖| / R := by
      rw [show (1 - ‖k‖ / R) - (1 - ‖k - Q‖ / R) = (‖k - Q‖ - ‖k‖) / R by ring,
        abs_div, abs_of_pos hR, abs_sub_comm]
    _ ≤ _ := div_le_div_of_nonneg_right hh hR.le

theorem wardTentCutoff_weighted_shift_difference {R : ℝ} (hR : 1 ≤ R)
    (Q k : DiracMomentum) :
    |wardTentCutoff R k - wardTentCutoff R (k - Q)| * (1 + ‖k‖) ≤ ‖Q‖ * (2 + ‖Q‖) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hk : ‖k‖ ≤ R + ‖Q‖
  · calc
      _ ≤ (‖Q‖ / R) * (1 + ‖k‖) := mul_le_mul_of_nonneg_right
        (wardTentCutoff_shift_difference hRpos Q k) (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hRpos).mpr
        have hh : ‖Q‖ * (1 + ‖k‖) ≤ (‖Q‖ * (2 + ‖Q‖)) * R := by
          have h₁ := mul_le_mul_of_nonneg_left hk (norm_nonneg Q)
          have h₂ := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ ‖Q‖ * (1 + ‖Q‖))
          nlinarith
        exact hh
  · have hkR : R ≤ ‖k‖ := by have := norm_nonneg Q; linarith
    have hmR : R ≤ ‖k - Q‖ := by have hh := norm_sub_norm_le k Q; linarith
    rw [wardTentCutoff_zero hRpos hkR, wardTentCutoff_zero hRpos hmR]
    simp only [sub_self, abs_zero, zero_mul]
    exact mul_nonneg (norm_nonneg Q) (by positivity)

theorem wardTentCutoff_tendsto (k : DiracMomentum) :
    Tendsto (fun n : ℕ => wardTentCutoff (n + 1) k) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ‖k‖ / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    by simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hn)
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hd).max (tendsto_const_nhds (x := (0 : ℝ)))
  simpa only [wardTentCutoff, sub_zero, max_eq_left zero_le_one] using hh

theorem ward_tent_product_integrable {C : DiracMomentum → ℂ} (hC : Continuous C)
    {R : ℝ} (hR : 0 < R) (Q : DiracMomentum) :
    Integrable (fun k => (wardTentCutoff R (k - Q) : ℂ) * C k) := by
  have hcont : Continuous (fun k => (wardTentCutoff R (k - Q) : ℂ) * C k) :=
    (Complex.continuous_ofReal.comp ((wardTentCutoff_continuous R).comp
      (continuous_id.sub continuous_const))).mul hC
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall Q R)
  intro k hk
  by_contra hbad
  have hr : R ≤ ‖k - Q‖ := by
    have hh : R < dist k Q := not_le.mp hbad
    exact (by simpa only [dist_eq_norm] using hh.le)
  change ((wardTentCutoff R (k - Q) : ℂ) * C k) ≠ 0 at hk
  exact hk (by rw [wardTentCutoff_zero hR hr, Complex.ofReal_zero, zero_mul])

/-- An integrable translation difference has zero integral under a one-power
weighted L1 bound on the unsplit function. Tent cutoffs provide a common
compact domain, and their boundary errors vanish by dominated convergence. -/
theorem integral_translation_difference_eq_zero_of_weighted_integrable
    {C : DiracMomentum → ℂ} (hC : Continuous C) (Q : DiracMomentum)
    (hW : Integrable (fun k => ‖C k‖ / (1 + ‖k‖)))
    (hD : Integrable (fun k => C k - C (k + Q))) :
    (∫ k, C k - C (k + Q)) = 0 := by
  let D : ℕ → DiracMomentum → ℂ := fun n k =>
    (wardTentCutoff (n + 1) k : ℂ) * (C k - C (k + Q))
  let E : ℕ → DiracMomentum → ℂ := fun n k =>
    ((wardTentCutoff (n + 1) k - wardTentCutoff (n + 1) (k - Q) : ℝ) : ℂ) * C k
  have hDm (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    exact ((Complex.continuous_ofReal.comp (wardTentCutoff_continuous (n + 1))).mul
      (hC.sub (hC.comp (continuous_id.add continuous_const)))).aestronglyMeasurable
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) volume := by
    exact ((Complex.continuous_ofReal.comp ((wardTentCutoff_continuous (n + 1)).sub
      ((wardTentCutoff_continuous (n + 1)).comp (continuous_id.sub continuous_const)))).mul hC).aestronglyMeasurable
  have hDb (n : ℕ) : ∀ᵐ k, ‖D n k‖ ≤ ‖C k - C (k + Q)‖ := by
    filter_upwards with k
    dsimp [D]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (wardTentCutoff_bounds (by positivity : (0 : ℝ) < n + 1) k).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (wardTentCutoff_bounds (by positivity : (0 : ℝ) < (n : ℝ) + 1) k).2
  have hEb (n : ℕ) : ∀ᵐ k, ‖E n k‖ ≤
      (‖Q‖ * (2 + ‖Q‖)) * (‖C k‖ / (1 + ‖k‖)) := by
    filter_upwards with k
    dsimp [E]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := wardTentCutoff_weighted_shift_difference (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith : (1 : ℝ) ≤ n + 1) Q k
    have hden : 0 < 1 + ‖k‖ := by positivity
    have hcoef := (le_div_iff₀ hden).mpr hh
    have hb := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (C k))
    convert hb using 1
    ring
  have hDl : ∀ᵐ k, Tendsto (fun n => D n k) atTop (𝓝 (C k - C (k + Q))) := by
    filter_upwards with k
    have hh := (Complex.continuous_ofReal.tendsto 1).comp (wardTentCutoff_tendsto k)
    simpa only [Complex.ofReal_one, one_mul] using hh.mul_const (C k - C (k + Q))
  have hEl : ∀ᵐ k, Tendsto (fun n => E n k) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards with k
    have hh := (wardTentCutoff_tendsto k).sub (wardTentCutoff_tendsto (k - Q))
    have hh' := (Complex.continuous_ofReal.tendsto 0).comp (by simpa only [sub_self] using hh)
    simpa only [Complex.ofReal_zero, zero_mul] using hh'.mul_const (C k)
  have hDlim := tendsto_integral_of_dominated_convergence (fun k => ‖C k - C (k + Q)‖)
    hDm hD.norm hDb hDl
  have hElim := tendsto_integral_of_dominated_convergence
    (fun k => (‖Q‖ * (2 + ‖Q‖)) * (‖C k‖ / (1 + ‖k‖)))
    hEm (hW.const_mul _) hEb hEl
  have heq : ∀ n, (∫ k, D n k) = ∫ k, E n k := by
    intro n
    have hR : (0 : ℝ) < n + 1 := by positivity
    have h₀ := ward_tent_product_integrable hC hR (0 : DiracMomentum)
    simp only [sub_zero] at h₀
    have hCplus : Continuous (fun k : DiracMomentum => C (k + Q)) := hC.comp (continuous_id.add continuous_const)
    have hPlus := ward_tent_product_integrable hCplus hR (0 : DiracMomentum)
    simp only [sub_zero] at hPlus
    have hMinus := ward_tent_product_integrable hC hR Q
    have hshift := integral_add_right_eq_self (μ := (volume : Measure DiracMomentum))
      (fun k : DiracMomentum => (wardTentCutoff (n + 1) (k - Q) : ℂ) * C k) Q
    simp only [add_sub_cancel_right] at hshift
    have hDeq : D n = (fun k => (wardTentCutoff (n + 1) k : ℂ) * C k -
        (wardTentCutoff (n + 1) k : ℂ) * C (k + Q)) := by funext k; dsimp [D]; ring
    have hEeq : E n = (fun k => (wardTentCutoff (n + 1) k : ℂ) * C k -
        (wardTentCutoff (n + 1) (k - Q) : ℂ) * C k) := by
      funext k
      dsimp [E]
      push_cast
      ring
    rw [hDeq, hEeq, integral_sub h₀ hPlus, integral_sub h₀ hMinus, hshift]
  have hElim' : Tendsto (fun n => ∫ k, D n k) atTop (𝓝 (0 : ℂ)) := by
    simpa only [heq, integral_zero] using hElim
  exact tendsto_nhds_unique hDlim hElim'

theorem laplace_bare_ward_integral_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 < m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) :
    (∫ k, bareWardContracted (wardLaplaceKernel ρ 1) m Q ν k) =
      ∫ k, bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν k := by
  let A := bareWardContracted (wardLaplaceKernel ρ 1) m Q ν
  let J := bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν
  let C := bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν
  have hA : Integrable A := bare_ward_contracted_integrable hm _ Q hH ν
  have hJ : Integrable J := laplace_bare_ward_remainder_integrable ρ hp hm Q hH ν
  have hC : Continuous C := bareWardCutoffTerm_continuous hm (wardLaplaceKernel_continuous ρ hp 1) Q ν
  have hW : Integrable (fun k => ‖C k‖ / (1 + ‖k‖)) :=
    laplace_bare_ward_weighted_cutoff_integrable ρ hp hm Q hH ν
  have hpoint : (fun k => A k - J k) =ᵐ[volume] (fun k => C k - C (k + Q)) := by
    filter_upwards with k
    have hh := bare_ward_pointwise_common_domain (wardLaplaceKernel ρ 1) m Q ν k
    change A k = J k + C k - C (k + Q) at hh
    linear_combination hh
  have hD : Integrable (fun k => C k - C (k + Q)) := by
    apply (hA.sub hJ).congr
    simpa only [Pi.sub_apply] using hpoint
  have hz := integral_translation_difference_eq_zero_of_weighted_integrable hC Q hW hD
  have hz' : (∫ k, A k - J k) = 0 := by rwa [integral_congr_ae hpoint]
  rw [integral_sub hA hJ] at hz'
  exact sub_eq_zero.mp hz'

theorem wardLaplaceKernel_pushforward (ρ : Measure ℝ) (a : ℝ) :
    wardLaplaceKernel ρ a = wardLaplaceKernel (ρ.map (fun τ : ℝ => a ^ 2 * τ)) 1 := by
  funext u
  unfold wardLaplaceKernel laplace
  simp only [one_pow, one_mul]
  rw [integral_map (by fun_prop : AEMeasurable (fun τ : ℝ => a ^ 2 * τ) ρ)
    (by fun_prop : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-τ * max u 0))
      (ρ.map (fun τ : ℝ => a ^ 2 * τ)))]
  congr 1
  funext τ
  congr 1
  ring

theorem ward_heat_support_nonnegative (ρ : Measure ℝ)
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) :
    ∀ᵐ τ ∂ρ.map (fun τ : ℝ => a ^ 2 * τ), 0 ≤ τ := by
  rw [ae_map_iff (by fun_prop : AEMeasurable (fun τ : ℝ => a ^ 2 * τ) ρ) measurableSet_Ici]
  filter_upwards [hp] with τ hτ
  exact mul_nonneg (sq_nonneg a) hτ

/-- The massive common-domain Ward lemma for the literal finite positive
Laplace kernel, with the dimensional scale a² retained. Only the original
tensor component L1 hypotheses are assumed. -/
theorem ward_common_cutoff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m : ℝ} (hm : 0 < m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν)) :
    (∀ ν, Integrable (bareWardRemainder (wardLaplaceKernel ρ a) m Q ν)) ∧
    ∀ ν, (∑ μ, (Q μ : ℂ) * ∫ k, bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν k) =
      ∫ k, bareWardRemainder (wardLaplaceKernel ρ a) m Q ν k := by
  rw [wardLaplaceKernel_pushforward] at hH ⊢
  let σ := ρ.map (fun τ : ℝ => a ^ 2 * τ)
  have hσ : ∀ᵐ τ ∂σ, 0 ≤ τ := ward_heat_support_nonnegative ρ hp a
  refine ⟨fun ν => laplace_bare_ward_remainder_integrable σ hσ hm Q hH ν, ?_⟩
  intro ν
  calc
    _ = ∫ k, ∑ μ, (Q μ : ℂ) * bareWardTensor (wardLaplaceKernel σ 1) m Q μ ν k := by
      rw [integral_finset_sum _ (fun μ _ => (hH μ ν).const_mul (Q μ : ℂ))]
      simp only [integral_const_mul]
    _ = ∫ k, bareWardContracted (wardLaplaceKernel σ 1) m Q ν k :=
      integral_congr_ae (Eventually.of_forall (fun k => bare_ward_tensor_contraction hm _ Q k ν))
    _ = _ := laplace_bare_ward_integral_eq σ hσ hm Q hH ν

def bareWardPolarization (F : ℝ → ℝ) (m e : ℝ) (Q : DiracMomentum) (μ ν : Fin 4) : ℂ :=
  ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) * ∫ k, bareWardTensor F m Q μ ν k

theorem ward_common_cutoff_polarization (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m : ℝ} (hm : 0 < m) (e : ℝ) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν)) (ν : Fin 4) :
    (∑ μ, (Q μ : ℂ) * bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν) =
      ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∫ k, bareWardRemainder (wardLaplaceKernel ρ a) m Q ν k := by
  have hh := (ward_common_cutoff ρ hp a hm Q hH).2 ν
  unfold bareWardPolarization
  calc
    _ = ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∑ μ, (Q μ : ℂ) * ∫ k, bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      ring
    _ = _ := by rw [hh]

end UV

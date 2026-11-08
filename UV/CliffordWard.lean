import UV.Obstructions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! An explicit four-component Euclidean Clifford realization of the
Ward-compatible two-vertex obstruction. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise RealInnerProductSpace

namespace UV

abbrev DiracMatrix := Matrix (Fin 4) (Fin 4) ℂ
abbrev DiracMomentum := EuclideanSpace ℝ (Fin 4)

/-- A standard Pauli tensor-product representation:
sigma1⊗1, sigma2⊗1, sigma3⊗sigma1, sigma3⊗sigma2. -/
def euclideanGamma : Fin 4 → DiracMatrix :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I;
      Complex.I, 0, 0, 0; 0, Complex.I, 0, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0],
    !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0;
      0, 0, 0, Complex.I; 0, 0, -Complex.I, 0]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem euclideanGamma_clifford (μ ν : Fin 4) :
    euclideanGamma μ * euclideanGamma ν + euclideanGamma ν * euclideanGamma μ =
      if μ = ν then 2 • (1 : DiracMatrix) else 0 := by
  fin_cases μ <;> fin_cases ν <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Matrix.ofNat_apply, Complex.I_sq]

theorem euclideanGamma_isHermitian (μ : Fin 4) : Matrix.IsHermitian (euclideanGamma μ) := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.conjTranspose_apply]

def diracSlash (k : DiracMomentum) : DiracMatrix :=
  ∑ μ, (k μ : ℂ) • euclideanGamma μ

def freeDiracSymbol (m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  Complex.I • diracSlash k + (m : ℂ) • 1

def freeDiracNumerator (m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  (-Complex.I) • diracSlash k + (m : ℂ) • 1

def freeDiracPropagator (m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹ • freeDiracNumerator m k

theorem diracMomentum_norm_sq (k : DiracMomentum) :
    ‖k‖ ^ 2 = k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  change k 0 ^ 2 + (k 1 ^ 2 + (k 2 ^ 2 + (k 3 ^ 2 + 0))) = _
  ring

set_option maxRecDepth 2000 in
theorem diracSlash_sq (k : DiracMomentum) :
    diracSlash k * diracSlash k = ((‖k‖ ^ 2 : ℝ) : ℂ) • (1 : DiracMatrix) := by
  rw [diracMomentum_norm_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracSlash, euclideanGamma, Matrix.mul_apply, Fin.sum_univ_succ,
      smul_eq_mul, Complex.ofReal_add, Complex.ofReal_pow] <;>
    ring_nf <;> simp [Complex.I_sq] <;> first | rfl | ring

theorem freeDiracSymbol_mul_numerator (m : ℝ) (k : DiracMomentum) :
    freeDiracSymbol m k * freeDiracNumerator m k =
      ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ) • (1 : DiracMatrix) := by
  unfold freeDiracSymbol freeDiracNumerator
  simp only [add_mul, mul_add, smul_mul_smul, Matrix.mul_one, Matrix.one_mul,
    diracSlash_sq, smul_smul, mul_neg, Complex.I_mul_I, neg_neg]
  rw [Complex.ofReal_add, Complex.ofReal_pow, add_smul]
  module

theorem freeDiracSymbol_mul_propagator {m : ℝ} (hm : 0 < m) (k : DiracMomentum) :
    freeDiracSymbol m k * freeDiracPropagator m k = 1 := by
  have hd : ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (‖k‖ ^ 2 + m ^ 2 : ℝ) ≠ 0)
  unfold freeDiracPropagator
  rw [Matrix.mul_smul, freeDiracSymbol_mul_numerator, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem freeDiracPropagator_mul_symbol {m : ℝ} (hm : 0 < m) (k : DiracMomentum) :
    freeDiracPropagator m k * freeDiracSymbol m k = 1 :=
  Matrix.mul_eq_one_comm.mp (freeDiracSymbol_mul_propagator hm k)

def bareWardLine (m : ℝ) (k : DiracMomentum) (μ : Fin 4) : DiracMatrix :=
  (Complex.I • euclideanGamma μ) * freeDiracPropagator m k

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem bareWardLine_trace (m : ℝ) (k : DiracMomentum) (μ : Fin 4) :
    Matrix.trace (bareWardLine m k μ) = ((4 * k μ / (‖k‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
  fin_cases μ <;>
    simp [bareWardLine, freeDiracPropagator, freeDiracNumerator, diracSlash,
      euclideanGamma, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      smul_eq_mul, div_eq_mul_inv] <;>
    ring_nf <;> simp [Complex.I_sq]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem bareWardLine_square_trace_sum (m : ℝ) (k : DiracMomentum) :
    (∑ μ, Matrix.trace (bareWardLine m k μ * bareWardLine m k μ)) =
      ((-8 * (‖k‖ ^ 2 + 2 * m ^ 2) / (‖k‖ ^ 2 + m ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [diracMomentum_norm_sq]
  push_cast
  simp only [div_eq_mul_inv]
  simp [bareWardLine, freeDiracPropagator, freeDiracNumerator, diracSlash,
    euclideanGamma, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
    smul_eq_mul, diracMomentum_norm_sq]
  simp only [← inv_pow]
  ring_nf
  have hi6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 by norm_num, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  simp only [Complex.I_sq, Complex.I_pow_four, hi6]
  ring

def dressedDiracPropagator (a M m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  (kernel a M (‖k‖ ^ 2) : ℂ) • freeDiracPropagator m k

def dressedDiracSymbol (a M m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  (kernel a M (‖k‖ ^ 2) : ℂ)⁻¹ • freeDiracSymbol m k

theorem dressedDiracSymbol_mul_propagator (a M : ℝ) {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) : dressedDiracSymbol a M m k * dressedDiracPropagator a M m k = 1 := by
  have hF : (kernel a M (‖k‖ ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernel_pos a M (‖k‖ ^ 2)).ne'
  unfold dressedDiracSymbol dressedDiracPropagator
  rw [smul_mul_smul, inv_mul_cancel₀ hF, one_smul, freeDiracSymbol_mul_propagator hm]

theorem dressedDiracPropagator_mul_symbol (a M : ℝ) {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) : dressedDiracPropagator a M m k * dressedDiracSymbol a M m k = 1 := by
  have hF : (kernel a M (‖k‖ ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernel_pos a M (‖k‖ ^ 2)).ne'
  unfold dressedDiracSymbol dressedDiracPropagator
  rw [smul_mul_smul, mul_inv_cancel₀ hF, one_smul, freeDiracPropagator_mul_symbol hm]

/-- The diagonal vertex predicted by differentiating the dressed inverse.
    Its identification with arbitrary continuous Ward vertices is proved below. -/
def softWardVertex (a M m : ℝ) (k : DiracMomentum) (μ : Fin 4) : DiracMatrix :=
  (kernel a M (‖k‖ ^ 2) : ℂ)⁻¹ •
    (Complex.I • euclideanGamma μ +
      ((a * k μ / Real.sqrt (‖k‖ ^ 2 + M ^ 2) : ℝ) : ℂ) • freeDiracSymbol m k)

theorem softWard_line_cancellation (a M : ℝ) {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) (μ : Fin 4) :
    softWardVertex a M m k μ * dressedDiracPropagator a M m k =
      bareWardLine m k μ +
        ((a * k μ / Real.sqrt (‖k‖ ^ 2 + M ^ 2) : ℝ) : ℂ) • (1 : DiracMatrix) := by
  have hF : (kernel a M (‖k‖ ^ 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (kernel_pos a M (‖k‖ ^ 2)).ne'
  unfold softWardVertex dressedDiracPropagator
  rw [smul_mul_smul, inv_mul_cancel₀ hF, one_smul, add_mul]
  simp only [smul_mul_assoc]
  rw [freeDiracSymbol_mul_propagator hm]
  simp only [bareWardLine, smul_mul_assoc]

theorem trace_square_add_scalar_one (A : DiracMatrix) (c : ℂ) :
    Matrix.trace ((A + c • 1) * (A + c • 1)) =
      Matrix.trace (A * A) + 2 * c * Matrix.trace A + 4 * c ^ 2 := by
  simp only [add_mul, mul_add, smul_mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin]
  norm_num
  ring

def softWardBubbleTrace (a M m e : ℝ) (k : DiracMomentum) : ℂ :=
  (-(e ^ 2) : ℂ) * ∑ μ,
    Matrix.trace ((softWardVertex a M m k μ * dressedDiracPropagator a M m k) *
      (softWardVertex a M m k μ * dressedDiracPropagator a M m k))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
/-- Exact evaluated external-index trace of the actual two dressed vertices
    and propagators in this explicit Clifford realization. -/
theorem softWardBubbleTrace_eq (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) :
    softWardBubbleTrace a M m e k = (wardTrace a M m e (‖k‖ ^ 2) : ℂ) := by
  unfold softWardBubbleTrace
  simp_rw [softWard_line_cancellation a M hm, trace_square_add_scalar_one,
    bareWardLine_trace]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, bareWardLine_square_trace_sum]
  simp only [Fin.sum_univ_succ]
  unfold wardTrace
  push_cast
  have hs : (Real.sqrt (‖k‖ ^ 2 + M ^ 2) : ℂ) ^ 2 =
      ((‖k‖ ^ 2 + M ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  have hu : ((‖k‖ ^ 2 : ℝ) : ℂ) =
      (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 + (k 3 : ℂ) ^ 2 := by
    rw [diracMomentum_norm_sq]
    push_cast
    rfl
  push_cast at hu
  norm_num only [Fin.reduceFinMk, Fin.succ_zero_eq_one] at *
  simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv_rev]
  simp only [← inv_pow, hs, Complex.ofReal_add, Complex.ofReal_pow]
  simp only [hu]
  ring

theorem softWardBubbleTrace_not_integrable {a e m : ℝ}
    (ha : 0 < a) (he : e ≠ 0) (hm : 0 < m) (M : ℝ) :
    ¬ Integrable (fun k : DiracMomentum => (softWardBubbleTrace a M m e k).re) := by
  simpa only [softWardBubbleTrace_eq a M e hm, Complex.ofReal_re] using
    wardTrace_not_integrable ha he M m

theorem diracSlash_add (k v : DiracMomentum) :
    diracSlash (k + v) = diracSlash k + diracSlash v := by
  simp only [diracSlash, PiLp.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem diracSlash_real_smul (h : ℝ) (v : DiracMomentum) :
    diracSlash (h • v) = (h : ℂ) • diracSlash v := by
  simp only [diracSlash, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum]

theorem diracSlash_single (μ : Fin 4) :
    diracSlash (EuclideanSpace.single μ (1 : ℝ)) = euclideanGamma μ := by
  simp [diracSlash, EuclideanSpace.single_apply]

theorem freeDiracSymbol_direction_hasDeriv (m : ℝ) (k : DiracMomentum) (μ : Fin 4) :
    HasDerivAt (fun h : ℝ => freeDiracSymbol m (k + h • EuclideanSpace.single μ 1))
      (Complex.I • euclideanGamma μ) 0 := by
  have heq : (fun h : ℝ => freeDiracSymbol m (k + h • EuclideanSpace.single μ 1)) =
      (fun h => freeDiracSymbol m k + h • (Complex.I • euclideanGamma μ)) := by
    ext h i j
    simp [freeDiracSymbol, diracSlash_add, diracSlash_real_smul, diracSlash_single,
      Complex.real_smul, smul_eq_mul]
    ring
  rw [heq]
  simpa only [one_smul] using
    ((hasDerivAt_id (0 : ℝ)).smul_const (Complex.I • euclideanGamma μ)).const_add
      (freeDiracSymbol m k)
theorem inverse_kernel_eq_exp (a M u : ℝ) :
    (kernel a M u)⁻¹ = Real.exp (a * depthProfile M u) := by
  rw [kernel, ← Real.exp_neg]
  congr 1
  ring

theorem inverse_kernel_direction_hasDeriv (a M : ℝ)
    (k v : EuclideanSpace ℝ (Fin 4)) (hk : k ≠ 0) :
    HasDerivAt (fun h : ℝ => (kernel a M (‖k + h • v‖ ^ 2))⁻¹)
      ((kernel a M (‖k‖ ^ 2))⁻¹ * a * ⟪k, v⟫ / Real.sqrt (‖k‖ ^ 2 + M ^ 2)) 0 := by
  have hq : ‖k‖ ^ 2 + M ^ 2 ≠ 0 := by have := norm_pos_iff.mpr hk; positivity
  have hcurve : HasDerivAt (fun h : ℝ => k + h • v) v 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add k
  have hnorm := hcurve.norm_sq
  simp only [zero_smul, add_zero] at hnorm
  have harg := (((hnorm.add_const (M ^ 2)).sqrt (by simpa only [zero_smul, add_zero] using hq)).sub_const M).const_mul a
  have he := harg.exp
  simp only [zero_smul, add_zero] at he
  simp_rw [inverse_kernel_eq_exp]
  convert he using 1
  simp only [depthProfile, div_eq_mul_inv, mul_inv_rev]
  ring

theorem continuous_ward_direction_diagonal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G D : ℝ → E} {V : E}
    (hG : ContinuousAt G 0) (hD : HasDerivAt D V 0)
    (hward : ∀ h : ℝ, h • G h = D h - D 0) : G 0 = V := by
  have ht : Tendsto G (𝓝[≠] (0 : ℝ)) (𝓝 V) := by
    apply (hasDerivAt_iff_tendsto_slope.mp hD).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hn : h ≠ 0 := hh
    simp only [slope_def_module, sub_zero]
    rw [← hward, inv_smul_smul₀ hn]
  exact tendsto_nhds_unique (hG.tendsto.mono_left nhdsWithin_le_nhds) ht

theorem dressedDiracSymbol_direction_hasDeriv (a M m : ℝ) (k : DiracMomentum)
    (hk : k ≠ 0) (μ : Fin 4) :
    HasDerivAt (fun h : ℝ => dressedDiracSymbol a M m (k + h • EuclideanSpace.single μ 1))
      (softWardVertex a M m k μ) 0 := by
  have hA := inverse_kernel_direction_hasDeriv a M k (EuclideanSpace.single μ 1) hk
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hA
  have h := hA.ofReal_comp.fun_smul (freeDiracSymbol_direction_hasDeriv m k μ)
  simp only [zero_smul, add_zero] at h
  convert h using 1
  · ext h
    simp only [dressedDiracSymbol, Complex.ofReal_inv ]
  · unfold softWardVertex
    push_cast
    module


def DressedWardCompatible (a M m : ℝ)
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix) : Prop :=
  ∀ p' p, (∑ ν, ((p' ν - p ν : ℝ) : ℂ) • G p' p ν) =
    dressedDiracSymbol a M m p' - dressedDiracSymbol a M m p

theorem continuous_dressed_ward_diagonal (a M m : ℝ)
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (hward : DressedWardCompatible a M m G) (k : DiracMomentum) (hk : k ≠ 0)
    (hcont : ∀ μ, ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k))
    (μ : Fin 4) : G k k μ = softWardVertex a M m k μ := by
  let v : DiracMomentum := EuclideanSpace.single μ 1
  have hGc : ContinuousAt (fun h : ℝ => G (k + h • v) k μ) 0 := by
    have hc : ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ)
        (k + (0 : ℝ) • v, k) := by simpa only [zero_smul, add_zero] using hcont μ
    have hpair : ContinuousAt (fun h : ℝ => (k + h • v, k)) 0 := by fun_prop
    exact hc.tendsto.comp hpair.tendsto
  have hline : ∀ h : ℝ, h • G (k + h • v) k μ =
      dressedDiracSymbol a M m (k + h • v) - dressedDiracSymbol a M m k := by
    intro h
    have hh := hward (k + h • v) k
    have hs : (∑ ν, (((k + h • v) ν - k ν : ℝ) : ℂ) • G (k + h • v) k ν) =
        (h : ℂ) • G (k + h • v) k μ := by
      simp [v, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    rw [hs] at hh
    have hscalar : h • G (k + h • v) k μ = (h : ℂ) • G (k + h • v) k μ := by
      ext i j
      simp [Complex.real_smul, smul_eq_mul]
    exact hscalar.trans hh
  have hline' : ∀ h : ℝ, h • G (k + h • v) k μ =
      dressedDiracSymbol a M m (k + h • EuclideanSpace.single μ 1) -
        dressedDiracSymbol a M m (k + (0 : ℝ) • EuclideanSpace.single μ 1) := by
    simpa only [v, zero_smul, add_zero] using hline
  have he := continuous_ward_direction_diagonal hGc
    (dressedDiracSymbol_direction_hasDeriv a M m k hk μ) hline'
  simpa only [zero_smul, add_zero] using he

def dressedWardBubbleTrace
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m e : ℝ) (k : DiracMomentum) : ℂ :=
  (-(e ^ 2) : ℂ) * ∑ μ,
    Matrix.trace ((G k k μ * dressedDiracPropagator a M m k) *
      (G k k μ * dressedDiracPropagator a M m k))

/-- The source's exact trace identity for every continuous Ward-compatible
    vertex, derived from its Ward identity and the explicit Clifford matrices. -/
theorem dressedWardBubbleTrace_eq
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    (hward : DressedWardCompatible a M m G) (k : DiracMomentum) (hk : k ≠ 0)
    (hcont : ∀ μ, ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k)) :
    dressedWardBubbleTrace G a M m e k = (wardTrace a M m e (‖k‖ ^ 2) : ℂ) := by
  unfold dressedWardBubbleTrace
  simp_rw [continuous_dressed_ward_diagonal a M m G hward k hk hcont]
  exact softWardBubbleTrace_eq a M e hm k

/-- The principal nonintegrability assertion of
    prop:OQED-Ward-bubble-obstruction, for the actual matrix bubble. -/
theorem dressedWardBubbleTrace_not_integrable
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    {a e m : ℝ} (ha : 0 < a) (he : e ≠ 0) (hm : 0 < m) (M : ℝ)
    (hward : DressedWardCompatible a M m G)
    (hcont : ∀ k : DiracMomentum, k ≠ 0 → ∀ μ,
      ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k)) :
    ¬ Integrable (fun k : DiracMomentum => (dressedWardBubbleTrace G a M m e k).re) := by
  intro hi
  have hk : ∀ᵐ k : DiracMomentum, k ≠ 0 := by rw [ae_iff]; simp
  have heq : (fun k : DiracMomentum => (dressedWardBubbleTrace G a M m e k).re) =ᵐ[volume]
      (fun k => wardTrace a M m e (‖k‖ ^ 2)) := by
    filter_upwards [hk] with k hk'
    rw [dressedWardBubbleTrace_eq G a M e hm hward k hk' (hcont k hk'), Complex.ofReal_re]
  exact wardTrace_not_integrable ha he M m (hi.congr heq)

theorem dressedWardBubbleTrace_complex_not_integrable
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    {a e m : ℝ} (ha : 0 < a) (he : e ≠ 0) (hm : 0 < m) (M : ℝ)
    (hward : DressedWardCompatible a M m G)
    (hcont : ∀ k : DiracMomentum, k ≠ 0 → ∀ μ,
      ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k)) :
    ¬ Integrable (dressedWardBubbleTrace G a M m e) := by
  intro hi
  exact dressedWardBubbleTrace_not_integrable G ha he hm M hward hcont hi.re

theorem dressedWardBubbleTrace_tendsto
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    (hward : DressedWardCompatible a M m G)
    (hcont : ∀ k : DiracMomentum, k ≠ 0 → ∀ μ,
      ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k)) :
    Tendsto (fun k : DiracMomentum => (dressedWardBubbleTrace G a M m e k).re)
      (cocompact DiracMomentum) (𝓝 (-4 * e ^ 2 * a ^ 2)) := by
  have h := (wardTrace_tendsto a M m e).comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_norm_cocompact_atTop : Tendsto (norm : DiracMomentum → ℝ)
        (cocompact DiracMomentum) atTop))
  apply h.congr'
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  have hne : k ≠ 0 := norm_pos_iff.mp hk
  rw [dressedWardBubbleTrace_eq G a M e hm hward k hne (hcont k hne), Complex.ofReal_re]
  rfl

def dressedWardBubbleComponent
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m e : ℝ) (μ ν : Fin 4) (k : DiracMomentum) : ℂ :=
  (-(e ^ 2) : ℂ) * Matrix.trace
    ((G k k μ * dressedDiracPropagator a M m k) *
      (G k k ν * dressedDiracPropagator a M m k))

/-- At least one actual tensor component fails absolute integrability, as
    asserted in the source proposition. -/
theorem dressedWardBubble_exists_nonintegrable_component
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    {a e m : ℝ} (ha : 0 < a) (he : e ≠ 0) (hm : 0 < m) (M : ℝ)
    (hward : DressedWardCompatible a M m G)
    (hcont : ∀ k : DiracMomentum, k ≠ 0 → ∀ μ,
      ContinuousAt (fun p : DiracMomentum × DiracMomentum => G p.1 p.2 μ) (k, k)) :
    ∃ μ, ¬ Integrable (dressedWardBubbleComponent G a M m e μ μ) := by
  by_contra! h
  have hi : Integrable (fun k : DiracMomentum => ∑ μ,
      dressedWardBubbleComponent G a M m e μ μ k) :=
    integrable_finset_sum _ (fun μ _ => h μ)
  have heq : (fun k : DiracMomentum => ∑ μ, dressedWardBubbleComponent G a M m e μ μ k) =
      dressedWardBubbleTrace G a M m e := by
    ext k
    simp only [dressedWardBubbleComponent, dressedWardBubbleTrace, Finset.mul_sum]
  rw [heq] at hi
  exact dressedWardBubbleTrace_complex_not_integrable G ha he hm M hward hcont hi

end UV

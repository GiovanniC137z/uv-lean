import UV.CliffordWard
import UV.DepthAsymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Actual second directional derivatives of the constant-background Dirac
symbol, followed by the contact-minus-bubble coefficient before integration. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise RealInnerProductSpace

namespace UV

def rootGradient (a M : ℝ) (k : DiracMomentum) (μ : Fin 4) : ℝ :=
  a * k μ / Real.sqrt (‖k‖ ^ 2 + M ^ 2)

def rootHessian (a M : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  a * ((if μ = ν then 1 else 0) / Real.sqrt (‖k‖ ^ 2 + M ^ 2) -
    k μ * k ν / Real.sqrt (‖k‖ ^ 2 + M ^ 2) ^ 3)

theorem inverseKernel_positiveMass_direction_hasDeriv (a : ℝ) {M : ℝ} (hM : 0 < M)
    (k v : DiracMomentum) :
    HasDerivAt (fun h : ℝ => (kernel a M (‖k + h • v‖ ^ 2))⁻¹)
      ((kernel a M (‖k‖ ^ 2))⁻¹ * a * ⟪k, v⟫ / Real.sqrt (‖k‖ ^ 2 + M ^ 2)) 0 := by
  have hq : ‖k‖ ^ 2 + M ^ 2 ≠ 0 := by positivity
  have hcurve : HasDerivAt (fun h : ℝ => k + h • v) v 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add k
  have hnorm := hcurve.norm_sq
  simp only [zero_smul, add_zero] at hnorm
  have harg := (((hnorm.add_const (M ^ 2)).sqrt
    (by simpa only [zero_smul, add_zero] using hq)).sub_const M).const_mul a
  have he := harg.exp
  simp only [zero_smul, add_zero] at he
  simp_rw [inverse_kernel_eq_exp]
  convert he using 1
  simp only [depthProfile, div_eq_mul_inv, mul_inv_rev]
  ring

theorem radialRoot_direction_hasDeriv {M : ℝ} (hM : 0 < M) (k v : DiracMomentum) :
    HasDerivAt (fun h : ℝ => Real.sqrt (‖k + h • v‖ ^ 2 + M ^ 2))
      (⟪k, v⟫ / Real.sqrt (‖k‖ ^ 2 + M ^ 2)) 0 := by
  have hq : ‖k‖ ^ 2 + M ^ 2 ≠ 0 := by positivity
  have hcurve : HasDerivAt (fun h : ℝ => k + h • v) v 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add k
  have h := (hcurve.norm_sq.add_const (M ^ 2)).sqrt
    (by simpa only [zero_smul, add_zero] using hq)
  simp only [zero_smul, add_zero] at h
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rootGradient_direction_hasDeriv (a : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    HasDerivAt (fun h : ℝ => rootGradient a M (k + h • EuclideanSpace.single ν 1) μ)
      (rootHessian a M k μ ν) 0 := by
  have hs : Real.sqrt (‖k‖ ^ 2 + M ^ 2) ≠ 0 := by positivity
  have hcoord : HasDerivAt
      (fun h : ℝ => (k + h • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ)
      (if μ = ν then (1 : ℝ) else 0) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (if μ = ν then (1 : ℝ) else 0)).const_add (k μ) using 1
    · ext h
      simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    · simp
  have hden := radialRoot_direction_hasDeriv hM k (EuclideanSpace.single ν 1)
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hden
  have h := (hcoord.const_mul a).fun_div hden (by simpa only [zero_smul, add_zero] using hs)
  simp only [zero_smul, add_zero] at h
  unfold rootGradient rootHessian
  convert h using 1
  field_simp [hs]

theorem dressedDiracSymbol_positiveMass_direction_hasDeriv (a m : ℝ) {M : ℝ}
    (hM : 0 < M) (k : DiracMomentum) (μ : Fin 4) :
    HasDerivAt (fun h : ℝ => dressedDiracSymbol a M m (k + h • EuclideanSpace.single μ 1))
      (softWardVertex a M m k μ) 0 := by
  have hA := inverseKernel_positiveMass_direction_hasDeriv a hM k (EuclideanSpace.single μ 1)
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hA
  have h := hA.ofReal_comp.fun_smul (freeDiracSymbol_direction_hasDeriv m k μ)
  simp only [zero_smul, add_zero] at h
  convert h using 1
  · ext h
    simp only [dressedDiracSymbol, Complex.ofReal_inv]
  · unfold softWardVertex
    push_cast
    module

def secondDiracSymbolFormula (a M m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : DiracMatrix :=
  (kernel a M (‖k‖ ^ 2) : ℂ)⁻¹ •
    (((rootGradient a M k μ * rootGradient a M k ν + rootHessian a M k μ ν : ℝ) : ℂ) •
      freeDiracSymbol m k +
      (rootGradient a M k μ : ℂ) • (Complex.I • euclideanGamma ν) +
      (rootGradient a M k ν : ℂ) • (Complex.I • euclideanGamma μ))

theorem softWardVertex_direction_hasDeriv (a m : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    HasDerivAt (fun h : ℝ => softWardVertex a M m (k + h • EuclideanSpace.single ν 1) μ)
      (secondDiracSymbolFormula a M m k μ ν) 0 := by
  have hA := inverseKernel_positiveMass_direction_hasDeriv a hM k (EuclideanSpace.single ν 1)
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hA
  have hroot := rootGradient_direction_hasDeriv a hM k μ ν
  have hins := (hasDerivAt_const (0 : ℝ) (Complex.I • euclideanGamma μ)).add
    (hroot.ofReal_comp.fun_smul (freeDiracSymbol_direction_hasDeriv m k ν))
  have h := hA.ofReal_comp.fun_smul hins
  simp only [Pi.add_apply, zero_smul, add_zero] at h
  convert h using 1
  · ext h
    simp only [softWardVertex, rootGradient, Complex.ofReal_inv]
  · unfold secondDiracSymbolFormula rootGradient
    push_cast
    module

/-- The Hessian is defined by an actual derivative, not its displayed formula. -/
def diracSymbolHessian (a M m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : DiracMatrix :=
  deriv (fun h : ℝ => softWardVertex a M m (k + h • EuclideanSpace.single ν 1) μ) 0

theorem diracSymbolHessian_eq (a m : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    diracSymbolHessian a M m k μ ν = secondDiracSymbolFormula a M m k μ ν :=
  (softWardVertex_direction_hasDeriv a m hM k μ ν).deriv

theorem diracSymbolHessian_eq_iterated_deriv (a m : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    diracSymbolHessian a M m k μ ν = deriv (fun h : ℝ => deriv (fun r : ℝ =>
      dressedDiracSymbol a M m (k + h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1)) 0) 0 := by
  unfold diracSymbolHessian
  congr 1
  apply funext
  intro h
  exact (dressedDiracSymbol_positiveMass_direction_hasDeriv a m hM
    (k + h • EuclideanSpace.single ν 1) μ).deriv.symm

def constantBackgroundDiracSymbol (a M m e : ℝ) (k A : DiracMomentum) : DiracMatrix :=
  dressedDiracSymbol a M m (k + e • A)

theorem constantBackgroundDiracSymbol_hasDeriv (a m e : ℝ) {M : ℝ} (hM : 0 < M)
    (k A : DiracMomentum) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ => constantBackgroundDiracSymbol a M m e k
      (A + r • EuclideanSpace.single μ 1))
      (e • softWardVertex a M m (k + e • A) μ) 0 := by
  have hd := dressedDiracSymbol_positiveMass_direction_hasDeriv a m hM (k + e • A) μ
  have hd' : HasDerivAt
      (fun h : ℝ => dressedDiracSymbol a M m (k + e • A + h • EuclideanSpace.single μ 1))
      (softWardVertex a M m (k + e • A) μ) (e * 0) := by simpa only [mul_zero] using hd
  have hc : HasDerivAt (fun r : ℝ => e * r) e 0 := by
    simpa only [mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul e
  have h := hd'.scomp 0 hc
  convert h using 1
  ext r
  unfold constantBackgroundDiracSymbol
  congr 1
  module

def constantBackgroundDiracHessian (a M m e : ℝ) (k : DiracMomentum)
    (μ ν : Fin 4) : DiracMatrix :=
  deriv (fun h : ℝ => deriv (fun r : ℝ => constantBackgroundDiracSymbol a M m e k
    (h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1)) 0) 0

theorem constantBackgroundDiracHessian_eq (a m e : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    constantBackgroundDiracHessian a M m e k μ ν = (e ^ 2) • diracSymbolHessian a M m k μ ν := by
  have heq : (fun h : ℝ => deriv (fun r : ℝ => constantBackgroundDiracSymbol a M m e k
      (h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1)) 0) =
      (fun h => e • softWardVertex a M m (k + (e * h) • EuclideanSpace.single ν 1) μ) := by
    funext h
    have hh := (constantBackgroundDiracSymbol_hasDeriv a m e hM k
      (h • EuclideanSpace.single ν 1) μ).deriv
    have hv : e • (h • EuclideanSpace.single ν (1 : ℝ)) =
        (e * h) • EuclideanSpace.single ν (1 : ℝ) := by module
    rw [hv] at hh
    exact hh
  have hd := softWardVertex_direction_hasDeriv a m hM k μ ν
  have hd' : HasDerivAt
      (fun h : ℝ => softWardVertex a M m (k + h • EuclideanSpace.single ν 1) μ)
      (secondDiracSymbolFormula a M m k μ ν) (e * 0) := by simpa only [mul_zero] using hd
  have hc : HasDerivAt (fun h : ℝ => e * h) e 0 := by
    simpa only [mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul e
  have h := (hd'.scomp 0 hc).const_smul e
  unfold constantBackgroundDiracHessian
  rw [heq, diracSymbolHessian_eq a m hM]
  simpa only [Function.comp_def, smul_smul, pow_two] using h.deriv

theorem secondDiracSymbolFormula_mul_propagator (a M : ℝ) {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) (μ ν : Fin 4) :
    secondDiracSymbolFormula a M m k μ ν * dressedDiracPropagator a M m k =
      ((rootGradient a M k μ * rootGradient a M k ν + rootHessian a M k μ ν : ℝ) : ℂ) •
        (1 : DiracMatrix) +
      (rootGradient a M k μ : ℂ) • bareWardLine m k ν +
      (rootGradient a M k ν : ℂ) • bareWardLine m k μ := by
  have hF : (kernel a M (‖k‖ ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernel_pos a M (‖k‖ ^ 2)).ne'
  unfold secondDiracSymbolFormula dressedDiracPropagator
  rw [smul_mul_smul, inv_mul_cancel₀ hF, one_smul]
  simp only [add_mul, smul_mul_assoc, freeDiracSymbol_mul_propagator hm,
    bareWardLine]

def rawContactMatrix (a M m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : DiracMatrix :=
  diracSymbolHessian a M m k μ ν * dressedDiracPropagator a M m k -
    (softWardVertex a M m k μ * dressedDiracPropagator a M m k) *
      (softWardVertex a M m k ν * dressedDiracPropagator a M m k)

/-- Actual second-variation contact minus the actual two-vertex bubble,
    combined pointwise before taking any integral. -/
theorem rawContactMatrix_eq (a : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) (μ ν : Fin 4) :
    rawContactMatrix a M m k μ ν =
      (rootHessian a M k μ ν : ℂ) • (1 : DiracMatrix) -
        bareWardLine m k μ * bareWardLine m k ν := by
  unfold rawContactMatrix
  rw [diracSymbolHessian_eq a m hM, secondDiracSymbolFormula_mul_propagator a M hm,
    softWard_line_cancellation a M hm, softWard_line_cancellation a M hm]
  simp only [rootGradient, add_mul, mul_add, Matrix.mul_one,
    Matrix.one_mul, smul_mul_assoc, Matrix.mul_smul, Complex.ofReal_add, Complex.ofReal_mul]
  push_cast
  module

def rawContactTensor (a M m e : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℂ :=
  (e ^ 2 : ℂ) * Matrix.trace (rawContactMatrix a M m k μ ν)

def constantBackgroundFirstSymbol (a M m e : ℝ) (k : DiracMomentum) (μ : Fin 4) : DiracMatrix :=
  deriv (fun r : ℝ => constantBackgroundDiracSymbol a M m e k
    (r • EuclideanSpace.single μ 1)) 0

theorem constantBackgroundFirstSymbol_eq (a m e : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ : Fin 4) :
    constantBackgroundFirstSymbol a M m e k μ = e • softWardVertex a M m k μ := by
  simpa only [constantBackgroundFirstSymbol, zero_add, smul_zero, add_zero] using
    (constantBackgroundDiracSymbol_hasDeriv a m e hM k 0 μ).deriv

/-- The coefficient formed directly from first and second background
    derivatives, retaining the source's contact-minus-bubble sign. -/
def actionGeneratedContactTensor (a M m e : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℂ :=
  Matrix.trace (constantBackgroundDiracHessian a M m e k μ ν * dressedDiracPropagator a M m k -
    (constantBackgroundFirstSymbol a M m e k μ * dressedDiracPropagator a M m k) *
      (constantBackgroundFirstSymbol a M m e k ν * dressedDiracPropagator a M m k))

theorem actionGeneratedContactTensor_eq (a m e : ℝ) {M : ℝ} (hM : 0 < M)
    (k : DiracMomentum) (μ ν : Fin 4) :
    actionGeneratedContactTensor a M m e k μ ν = rawContactTensor a M m e k μ ν := by
  unfold actionGeneratedContactTensor
  rw [constantBackgroundDiracHessian_eq a m e hM, constantBackgroundFirstSymbol_eq a m e hM,
    constantBackgroundFirstSymbol_eq a m e hM]
  simp only [smul_mul_assoc, Matrix.mul_smul]
  unfold rawContactTensor rawContactMatrix
  let H := diracSymbolHessian a M m k μ ν * dressedDiracPropagator a M m k
  let B := (softWardVertex a M m k μ * dressedDiracPropagator a M m k) *
    (softWardVertex a M m k ν * dressedDiracPropagator a M m k)
  change Matrix.trace ((e ^ 2) • H - e • (e • B)) = (e ^ 2 : ℂ) * Matrix.trace (H - B)
  have hscalar : (e ^ 2) • H - e • (e • B) = (e ^ 2) • (H - B) := by module
  rw [hscalar, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.ofReal_pow]

theorem rawContactTensor_eq_rootHessian (a e : ℝ) {M m : ℝ}
    (hM : 0 < M) (hm : 0 < m) (k : DiracMomentum) (μ ν : Fin 4) :
    rawContactTensor a M m e k μ ν = (e ^ 2 : ℂ) *
      (4 * (rootHessian a M k μ ν : ℂ) - Matrix.trace (bareWardLine m k μ * bareWardLine m k ν)) := by
  unfold rawContactTensor
  rw [rawContactMatrix_eq a hM hm]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  norm_num [mul_comm]

def bareWardNumeratorExplicit (m : ℝ) (k : DiracMomentum) : Fin 4 → DiracMatrix :=
  let x : Fin 4 → ℂ := fun j => k j
  let z : ℂ := m
  ![!![x 0 + Complex.I * x 1, 0, Complex.I * z, -x 2 + Complex.I * x 3;
      0, x 0 + Complex.I * x 1, -x 2 - Complex.I * x 3, Complex.I * z;
      Complex.I * z, x 2 - Complex.I * x 3, x 0 - Complex.I * x 1, 0;
      x 2 + Complex.I * x 3, Complex.I * z, 0, x 0 - Complex.I * x 1],
    !![-Complex.I * x 0 + x 1, 0, z, Complex.I * x 2 + x 3;
      0, -Complex.I * x 0 + x 1, Complex.I * x 2 - x 3, z;
      -z, Complex.I * x 2 + x 3, Complex.I * x 0 + x 1, 0;
      Complex.I * x 2 - x 3, -z, 0, Complex.I * x 0 + x 1],
    !![x 2 + Complex.I * x 3, Complex.I * z, 0, x 0 - Complex.I * x 1;
      Complex.I * z, x 2 - Complex.I * x 3, x 0 - Complex.I * x 1, 0;
      0, -x 0 - Complex.I * x 1, x 2 + Complex.I * x 3, -Complex.I * z;
      -x 0 - Complex.I * x 1, 0, -Complex.I * z, x 2 - Complex.I * x 3],
    !![-Complex.I * x 2 + x 3, z, 0, -Complex.I * x 0 - x 1;
      -z, Complex.I * x 2 + x 3, Complex.I * x 0 + x 1, 0;
      0, Complex.I * x 0 - x 1, -Complex.I * x 2 + x 3, -z;
      -Complex.I * x 0 + x 1, 0, z, Complex.I * x 2 + x 3]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem bareWardNumerator_eq_explicit (m : ℝ) (k : DiracMomentum) (μ : Fin 4) :
    (Complex.I • euclideanGamma μ) * freeDiracNumerator m k = bareWardNumeratorExplicit m k μ := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [freeDiracNumerator, diracSlash, euclideanGamma, bareWardNumeratorExplicit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, smul_eq_mul,
      Complex.mul_re, Complex.mul_im]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 8000000 in
theorem bareWardLine_cross_trace (m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) :
    Matrix.trace (bareWardLine m k μ * bareWardLine m k ν) =
      (((8 * k μ * k ν - 4 * (if μ = ν then 1 else 0) * (‖k‖ ^ 2 + m ^ 2)) /
        (‖k‖ ^ 2 + m ^ 2) ^ 2 : ℝ) : ℂ) := by
  have hnum : Matrix.trace
      (((Complex.I • euclideanGamma μ) * freeDiracNumerator m k) *
        ((Complex.I • euclideanGamma ν) * freeDiracNumerator m k)) =
      ((8 * k μ * k ν - 4 * (if μ = ν then 1 else 0) * (‖k‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
    rw [bareWardNumerator_eq_explicit, bareWardNumerator_eq_explicit]
    rw [diracMomentum_norm_sq]
    fin_cases μ <;> fin_cases ν <;> apply Complex.ext <;>
      simp [bareWardNumeratorExplicit, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_succ,
        pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hline (j : Fin 4) : bareWardLine m k j =
      ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹ •
        ((Complex.I • euclideanGamma j) * freeDiracNumerator m k) := by
    simp only [bareWardLine, freeDiracPropagator, Matrix.mul_smul]
  rw [hline μ, hline ν, smul_mul_smul, Matrix.trace_smul, hnum]
  simp only [smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- The exact tensor formula of eq:OQED-contact-explicit, now obtained from
    actual first and second derivatives of the dressed Dirac symbol. -/
theorem rawContactTensor_explicit (a e : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) (μ ν : Fin 4) :
    rawContactTensor a M m e k μ ν =
      ((e ^ 2 * (4 * a * ((if μ = ν then 1 else 0) / Real.sqrt (‖k‖ ^ 2 + M ^ 2) -
        k μ * k ν / Real.sqrt (‖k‖ ^ 2 + M ^ 2) ^ 3) +
        4 * (if μ = ν then 1 else 0) / (‖k‖ ^ 2 + m ^ 2) -
        8 * k μ * k ν / (‖k‖ ^ 2 + m ^ 2) ^ 2) : ℝ) : ℂ) := by
  rw [rawContactTensor_eq_rootHessian a e hM hm, bareWardLine_cross_trace]
  unfold rootHessian
  push_cast
  have hd : ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast at hd
  field_simp [hd]
  ring

def rawContactTrace (a M m e : ℝ) (k : DiracMomentum) : ℂ :=
  ∑ μ, rawContactTensor a M m e k μ μ

theorem rawContactTrace_eq (a e : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) : rawContactTrace a M m e k =
      (contactTrace a M m e (‖k‖ ^ 2) : ℂ) := by
  unfold rawContactTrace
  simp_rw [rawContactTensor_eq_rootHessian a e hM hm]
  rw [← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  rw [bareWardLine_square_trace_sum]
  have hs : Real.sqrt (‖k‖ ^ 2 + M ^ 2) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ ‖k‖ ^ 2 + M ^ 2 by positivity)
  have hu := diracMomentum_norm_sq k
  simp only [Fin.sum_univ_succ, rootHessian, ite_true]
  unfold contactTrace
  push_cast
  norm_num only [Fin.reduceFinMk, Fin.succ_zero_eq_one]
  have hsC : (Real.sqrt (‖k‖ ^ 2 + M ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsqC := congrArg (fun x : ℝ => (x : ℂ)) hsq
  have huC := congrArg (fun x : ℝ => (x : ℂ)) hu
  push_cast at hsqC huC
  simp only [div_eq_mul_inv, ← inv_pow]
  field_simp [hsC]
  simp only [hsqC, huC]
  ring

theorem rawContactTrace_not_integrable {a M m e : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hm : 0 < m) (he : e ≠ 0) : ¬ Integrable (rawContactTrace a M m e) := by
  intro hi
  have hreal := hi.re
  change Integrable (fun k : DiracMomentum => (rawContactTrace a M m e k).re) at hreal
  have heq : (fun k : DiracMomentum => (rawContactTrace a M m e k).re) =
      (fun k => contactTrace a M m e (‖k‖ ^ 2)) := by
    ext k
    rw [rawContactTrace_eq a e hM hm, Complex.ofReal_re]
  rw [heq] at hreal
  exact contactTrace_not_integrable ha hM he m hreal

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem freeDiracSymbol_det (m : ℝ) (k : DiracMomentum) :
    Matrix.det (freeDiracSymbol m k) = (((‖k‖ ^ 2 + m ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_succ_row_zero, diracMomentum_norm_sq]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  dsimp [Fin.succAbove, Fin.castSucc, Fin.succ]
  norm_num [freeDiracSymbol, diracSlash, euclideanGamma, Fin.sum_univ_succ,
    smul_eq_mul, Matrix.one_apply]
  push_cast
  ring_nf
  have hi6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 by norm_num, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hi8 : Complex.I ^ 8 = 1 := by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  simp only [Complex.I_sq, Complex.I_pow_four, hi6, hi8]
  ring


theorem dressedDiracSymbol_det (a M m : ℝ) (k : DiracMomentum) :
    Matrix.det (dressedDiracSymbol a M m k) =
      ((((kernel a M (‖k‖ ^ 2))⁻¹) ^ 4 * (‖k‖ ^ 2 + m ^ 2) ^ 2 : ℝ) : ℂ) := by
  simp only [dressedDiracSymbol, Matrix.det_smul, Fintype.card_fin, freeDiracSymbol_det]
  push_cast
  rfl

def diracLogDet (a M m : ℝ) (k : DiracMomentum) : ℝ :=
  Real.log (Matrix.det (dressedDiracSymbol a M m k)).re

theorem diracLogDet_eq (a M : ℝ) {m : ℝ} (hm : 0 < m) (k : DiracMomentum) :
    diracLogDet a M m k = 4 * a * depthProfile M (‖k‖ ^ 2) +
      2 * Real.log (‖k‖ ^ 2 + m ^ 2) := by
  unfold diracLogDet
  rw [dressedDiracSymbol_det, Complex.ofReal_re]
  have hK := kernel_pos a M (‖k‖ ^ 2)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    inverse_kernel_eq_exp, Real.log_exp]
  ring

def contactRadialPrimitive (a M m e r : ℝ) : ℝ :=
  4 * e ^ 2 * (a * r ^ 4 / Real.sqrt (r ^ 2 + M ^ 2) + r ^ 4 / (r ^ 2 + m ^ 2))

theorem contactRadialPrimitive_hasDeriv {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (a e r : ℝ) : HasDerivAt (contactRadialPrimitive a M m e)
      (r ^ 3 * contactTrace a M m e (r ^ 2)) r := by
  have hs : Real.sqrt (r ^ 2 + M ^ 2) ≠ 0 := by positivity
  have hd : r ^ 2 + m ^ 2 ≠ 0 := by positivity
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + M ^ 2))
      (r / Real.sqrt (r ^ 2 + M ^ 2)) r := by
    have h := (((hasDerivAt_id r).pow 2).add_const (M ^ 2)).sqrt
      (by positivity : r ^ 2 + M ^ 2 ≠ 0)
    convert h using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    field_simp
  have hfirst : HasDerivAt (fun x : ℝ => a * x ^ 4 / Real.sqrt (x ^ 2 + M ^ 2))
      (a * r ^ 3 * (3 * r ^ 2 + 4 * M ^ 2) / Real.sqrt (r ^ 2 + M ^ 2) ^ 3) r := by
    have h := (((hasDerivAt_id r).pow 4).const_mul a).fun_div hsqrt hs
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
    convert h using 1
    field_simp [hs]
    have hsq := Real.sq_sqrt (show 0 ≤ r ^ 2 + M ^ 2 by positivity)
    linear_combination -(4 * a * r ^ 3) * hsq
  have hsecond : HasDerivAt (fun x : ℝ => x ^ 4 / (x ^ 2 + m ^ 2))
      (2 * r ^ 3 * (r ^ 2 + 2 * m ^ 2) / (r ^ 2 + m ^ 2) ^ 2) r := by
    have h := ((hasDerivAt_id r).pow 4).fun_div (((hasDerivAt_id r).pow 2).add_const (m ^ 2)) hd
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
    convert h using 1
    ring
  have h := (hfirst.fun_add hsecond).const_mul (4 * e ^ 2)
  convert h using 1
  unfold contactTrace
  ring


theorem contactTrace_radial_continuous {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (a e : ℝ) : Continuous (fun r : ℝ => r ^ 3 * contactTrace a M m e (r ^ 2)) := by
  unfold contactTrace
  fun_prop (disch := (intro x; positivity))

theorem contactTrace_interval_integral {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (a e R : ℝ) : (∫ r in (0 : ℝ)..R, r ^ 3 * contactTrace a M m e (r ^ 2)) =
      4 * e ^ 2 * (a * R ^ 4 / Real.sqrt (R ^ 2 + M ^ 2) + R ^ 4 / (R ^ 2 + m ^ 2)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => contactRadialPrimitive_hasDeriv hM hm a e x)
    ((contactTrace_radial_continuous hM hm a e).intervalIntegrable 0 R)
  simpa [contactRadialPrimitive] using h

theorem contactTrace_ball_exhaustion {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (a e R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi) ^ (-4 : ℤ) *
      (∫ k : ScalarMomentum in Metric.ball 0 R, contactTrace a M m e (‖k‖ ^ 2)) =
      e ^ 2 / (2 * Real.pi ^ 2) *
        (a * R ^ 4 / Real.sqrt (R ^ 2 + M ^ 2) + R ^ 4 / (R ^ 2 + m ^ 2)) := by
  have h := fourier_radial_integral ((Iio R).indicator (fun r : ℝ => contactTrace a M m e (r ^ 2)))
  have hl : (fun q : ScalarMomentum =>
      (Iio R).indicator (fun r : ℝ => contactTrace a M m e (r ^ 2)) ‖q‖) =
      (Metric.ball 0 R).indicator (fun q : ScalarMomentum => contactTrace a M m e (‖q‖ ^ 2)) := by
    funext q
    simp only [indicator, mem_Iio, Metric.mem_ball, dist_zero_right]
  rw [hl, integral_indicator measurableSet_ball] at h
  have hr : (fun r : ℝ => r ^ 3 *
      (Iio R).indicator (fun r : ℝ => contactTrace a M m e (r ^ 2)) r) =
      (Iio R).indicator (fun r : ℝ => r ^ 3 * contactTrace a M m e (r ^ 2)) := by
    funext r
    by_cases hh : r < R <;> simp [indicator, hh]
  rw [hr, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
    contactTrace_interval_integral hM hm] at h
  convert h using 1
  field_simp [Real.pi_ne_zero]
  ring

def diracLogDetGradient (a M m : ℝ) (k : DiracMomentum) (μ : Fin 4) : ℝ :=
  4 * rootGradient a M k μ + 4 * k μ / (‖k‖ ^ 2 + m ^ 2)

def diracLogDetHessianFormula (a M m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  4 * rootHessian a M k μ ν + 4 * (if μ = ν then 1 else 0) / (‖k‖ ^ 2 + m ^ 2) -
    8 * k μ * k ν / (‖k‖ ^ 2 + m ^ 2) ^ 2

theorem normSq_single_hasDeriv (k : DiracMomentum) (μ : Fin 4) :
    HasDerivAt (fun h : ℝ => ‖k + h • EuclideanSpace.single μ 1‖ ^ 2) (2 * k μ) 0 := by
  have hcurve : HasDerivAt (fun h : ℝ => k + h • EuclideanSpace.single μ 1)
      (EuclideanSpace.single μ 1) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (EuclideanSpace.single μ (1 : ℝ))).const_add k
  simpa only [zero_smul, add_zero, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial, one_mul] using hcurve.norm_sq

theorem diracLogDet_direction_hasDeriv (a : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) (μ : Fin 4) :
    HasDerivAt (fun h : ℝ => diracLogDet a M m (k + h • EuclideanSpace.single μ 1))
      (diracLogDetGradient a M m k μ) 0 := by
  have hroot := radialRoot_direction_hasDeriv hM k (EuclideanSpace.single μ 1)
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] at hroot
  have hlog := ((normSq_single_hasDeriv k μ).add_const (m ^ 2)).log
    (by simpa only [zero_smul, add_zero] using (by positivity : ‖k‖ ^ 2 + m ^ 2 ≠ 0))
  have h := ((hroot.sub_const M).const_mul (4 * a)).fun_add (hlog.const_mul 2)
  simp only [zero_smul, add_zero] at h
  simp_rw [diracLogDet_eq a M hm]
  unfold depthProfile
  convert h using 1
  unfold diracLogDetGradient rootGradient
  ring

theorem diracLogDetGradient_direction_hasDeriv (a : ℝ) {M m : ℝ}
    (hM : 0 < M) (hm : 0 < m) (k : DiracMomentum) (μ ν : Fin 4) :
    HasDerivAt (fun h : ℝ => diracLogDetGradient a M m (k + h • EuclideanSpace.single ν 1) μ)
      (diracLogDetHessianFormula a M m k μ ν) 0 := by
  have hd : ‖k‖ ^ 2 + m ^ 2 ≠ 0 := by positivity
  have hcoord : HasDerivAt
      (fun h : ℝ => (k + h • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ)
      (if μ = ν then (1 : ℝ) else 0) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const
      (if μ = ν then (1 : ℝ) else 0)).const_add (k μ) using 1
    · ext h
      simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    · simp
  have hquot := hcoord.fun_div ((normSq_single_hasDeriv k ν).add_const (m ^ 2))
    (by simpa only [zero_smul, add_zero] using hd)
  have h := ((rootGradient_direction_hasDeriv a hM k μ ν).const_mul 4).fun_add
    (hquot.const_mul 4)
  simp only [zero_smul, add_zero] at h
  convert h using 1
  · ext h
    unfold diracLogDetGradient
    ring
  · unfold diracLogDetHessianFormula
    field_simp [hd]
    ring

def diracLogDetHessian (a M m : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  deriv (fun h : ℝ => deriv (fun r : ℝ => diracLogDet a M m
    (k + h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1)) 0) 0

theorem diracLogDetHessian_eq (a : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) (μ ν : Fin 4) :
    diracLogDetHessian a M m k μ ν = diracLogDetHessianFormula a M m k μ ν := by
  unfold diracLogDetHessian
  have heq : (fun h : ℝ => deriv (fun r : ℝ => diracLogDet a M m
      (k + h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1)) 0) =
      (fun h => diracLogDetGradient a M m (k + h • EuclideanSpace.single ν 1) μ) := by
    funext h
    exact (diracLogDet_direction_hasDeriv a hM hm (k + h • EuclideanSpace.single ν 1) μ).deriv
  rw [heq]
  exact (diracLogDetGradient_direction_hasDeriv a hM hm k μ ν).deriv

theorem rawContactTensor_logdet_Hessian (a e : ℝ) {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (k : DiracMomentum) (μ ν : Fin 4) :
    rawContactTensor a M m e k μ ν = ((e ^ 2 * diracLogDetHessian a M m k μ ν : ℝ) : ℂ) := by
  rw [rawContactTensor_explicit a e hM hm, diracLogDetHessian_eq a hM hm]
  unfold diracLogDetHessianFormula rootHessian
  congr 1
  ring

theorem diracLogDet_eq_complexLog (a M : ℝ) {m : ℝ} (hm : 0 < m) (k : DiracMomentum) :
    Complex.log (Matrix.det (dressedDiracSymbol a M m k)) = (diracLogDet a M m k : ℂ) := by
  have hK := kernel_pos a M (‖k‖ ^ 2)
  unfold diracLogDet
  rw [dressedDiracSymbol_det, Complex.ofReal_re]
  exact (Complex.ofReal_log (by positivity)).symm

theorem rawContactTrace_ball_exhaustion {M m : ℝ} (hM : 0 < M) (hm : 0 < m)
    (a e R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi) ^ (-4 : ℤ) *
      (∫ k : DiracMomentum in Metric.ball 0 R, (rawContactTrace a M m e k).re) =
      e ^ 2 / (2 * Real.pi ^ 2) *
        (a * R ^ 4 / Real.sqrt (R ^ 2 + M ^ 2) + R ^ 4 / (R ^ 2 + m ^ 2)) := by
  simp_rw [rawContactTrace_eq a e hM hm, Complex.ofReal_re]
  exact contactTrace_ball_exhaustion hM hm a e R hR

theorem rawContactTrace_pos {a M m e : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hm : 0 < m) (he : e ≠ 0) (k : DiracMomentum) :
    0 < (rawContactTrace a M m e k).re := by
  rw [rawContactTrace_eq a e hM hm, Complex.ofReal_re]
  exact contactTrace_pos ha hM he (sq_nonneg ‖k‖) m

theorem actionGeneratedContactTensor_logdet_Hessian (a e : ℝ) {M m : ℝ}
    (hM : 0 < M) (hm : 0 < m) (k : DiracMomentum) (μ ν : Fin 4) :
    actionGeneratedContactTensor a M m e k μ ν =
      ((e ^ 2 * diracLogDetHessian a M m k μ ν : ℝ) : ℂ) := by
  rw [actionGeneratedContactTensor_eq a m e hM, rawContactTensor_logdet_Hessian a e hM hm]

theorem actionGeneratedContactTensor_explicit (a e : ℝ) {M m : ℝ}
    (hM : 0 < M) (hm : 0 < m) (k : DiracMomentum) (μ ν : Fin 4) :
    actionGeneratedContactTensor a M m e k μ ν =
      ((e ^ 2 * (4 * a * ((if μ = ν then 1 else 0) / Real.sqrt (‖k‖ ^ 2 + M ^ 2) -
        k μ * k ν / Real.sqrt (‖k‖ ^ 2 + M ^ 2) ^ 3) +
        4 * (if μ = ν then 1 else 0) / (‖k‖ ^ 2 + m ^ 2) -
        8 * k μ * k ν / (‖k‖ ^ 2 + m ^ 2) ^ 2) : ℝ) : ℂ) := by
  rw [actionGeneratedContactTensor_eq a m e hM, rawContactTensor_explicit a e hM hm]

/-- The failure is componentwise absolute convergence of the coefficient
    actually generated by constant-background differentiation. -/
theorem actionGeneratedContactTensor_exists_nonintegrable_component
    {a M m e : ℝ} (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (he : e ≠ 0) :
    ∃ μ, ¬ Integrable (fun k : DiracMomentum => actionGeneratedContactTensor a M m e k μ μ) := by
  by_contra! h
  have hi : Integrable (fun k : DiracMomentum => ∑ μ,
      actionGeneratedContactTensor a M m e k μ μ) :=
    integrable_finset_sum _ (fun μ _ => h μ)
  have heq : (fun k : DiracMomentum => ∑ μ, actionGeneratedContactTensor a M m e k μ μ) =
      rawContactTrace a M m e := by
    ext k
    simp only [actionGeneratedContactTensor_eq a m e hM, rawContactTrace]
  rw [heq] at hi
  exact rawContactTrace_not_integrable ha hM hm he hi

end UV

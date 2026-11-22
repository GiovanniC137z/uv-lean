import UV.ContinuationSectorPlane
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact two-oscillator photon response on the intrinsic spatial chart of a
selected sector plane. Source: `prop:spex-polarization-uv`.
The Euclidean frequency variable below is squared frequency; no directed
Lorentzian boundary prescription is replaced by this real variable. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UV.ResumeCarrierPolarization

/-- The squared magnetic mixing fixed by the positive Hamiltonian square. -/
def mixing (r g k : ℝ) : ℝ := g ^ 2 * k ^ 2 * Real.exp (-(2 * r * k))

def frequencySum (Ω r g k : ℝ) : ℝ := Ω ^ 2 + k ^ 2 + mixing r g k

def discriminant (Ω r g k : ℝ) : ℝ :=
  (Ω ^ 2 - k ^ 2) ^ 2 + 2 * mixing r g k * (Ω ^ 2 + k ^ 2) + mixing r g k ^ 2

def frequencyGap (Ω r g k : ℝ) : ℝ := Real.sqrt (discriminant Ω r g k)

def highFrequency (Ω r g k : ℝ) : ℝ :=
  (frequencySum Ω r g k + frequencyGap Ω r g k) / 2

/-- Rationalized low root, including its continuous zero-momentum value. -/
def lowFrequency (Ω r g k : ℝ) : ℝ :=
  2 * Ω ^ 2 * k ^ 2 / (frequencySum Ω r g k + frequencyGap Ω r g k)

/-- Exact Gaussian Schur-complement photon covariance. -/
def response (Ω r g k x : ℝ) : ℝ :=
  (x + k ^ 2 + mixing r g k * x / (x + Ω ^ 2))⁻¹

def lowWeight (Ω r g k : ℝ) : ℝ :=
  (Ω ^ 2 - lowFrequency Ω r g k) / frequencyGap Ω r g k

def highWeight (Ω r g k : ℝ) : ℝ :=
  (highFrequency Ω r g k - Ω ^ 2) / frequencyGap Ω r g k

theorem mixing_nonneg (r g k : ℝ) : 0 ≤ mixing r g k := by
  unfold mixing
  positivity

theorem mixing_pos {r g k : ℝ} (hg : g ≠ 0) (hk : k ≠ 0) : 0 < mixing r g k := by
  unfold mixing
  exact mul_pos (mul_pos (sq_pos_of_ne_zero hg) (sq_pos_of_ne_zero hk)) (Real.exp_pos _)

theorem discriminant_nonneg (Ω r g k : ℝ) : 0 ≤ discriminant Ω r g k := by
  have hm := mixing_nonneg r g k
  unfold discriminant
  positivity

theorem frequencyGap_sq (Ω r g k : ℝ) :
    frequencyGap Ω r g k ^ 2 = discriminant Ω r g k :=
  Real.sq_sqrt (discriminant_nonneg Ω r g k)

theorem sum_sq_sub_gap_sq (Ω r g k : ℝ) :
    frequencySum Ω r g k ^ 2 - frequencyGap Ω r g k ^ 2 = 4 * Ω ^ 2 * k ^ 2 := by
  rw [frequencyGap_sq]
  unfold frequencySum discriminant
  ring

theorem sum_add_gap_pos {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    0 < frequencySum Ω r g k + frequencyGap Ω r g k := by
  have hm := mixing_nonneg r g k
  have hd : 0 ≤ frequencyGap Ω r g k := Real.sqrt_nonneg _
  unfold frequencySum
  nlinarith [sq_nonneg k, sq_pos_of_pos hΩ]

theorem lowFrequency_alternative {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    lowFrequency Ω r g k = (frequencySum Ω r g k - frequencyGap Ω r g k) / 2 := by
  unfold lowFrequency
  apply (div_eq_iff (ne_of_gt (sum_add_gap_pos hΩ r g k))).mpr
  have h := sum_sq_sub_gap_sq Ω r g k
  nlinarith

theorem normal_frequency_sum {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    lowFrequency Ω r g k + highFrequency Ω r g k = frequencySum Ω r g k := by
  rw [lowFrequency_alternative hΩ]
  unfold highFrequency
  ring

theorem normal_frequency_product {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    lowFrequency Ω r g k * highFrequency Ω r g k = Ω ^ 2 * k ^ 2 := by
  rw [lowFrequency_alternative hΩ]
  unfold highFrequency
  have h := sum_sq_sub_gap_sq Ω r g k
  nlinarith

theorem normal_frequency_gap {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    highFrequency Ω r g k - lowFrequency Ω r g k = frequencyGap Ω r g k := by
  rw [lowFrequency_alternative hΩ]
  unfold highFrequency
  ring

theorem lowFrequency_pos {Ω k : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0) (r g : ℝ) :
    0 < lowFrequency Ω r g k :=
  div_pos (by positivity) (sum_add_gap_pos hΩ r g k)

theorem highFrequency_pos {Ω : ℝ} (hΩ : 0 < Ω) (r g k : ℝ) :
    0 < highFrequency Ω r g k := by
  exact div_pos (sum_add_gap_pos hΩ r g k) (by norm_num)

theorem normal_frequencies_straddle {Ω g k : ℝ} (hΩ : 0 < Ω) (hg : g ≠ 0)
    (hk : k ≠ 0) (r : ℝ) :
    lowFrequency Ω r g k < Ω ^ 2 ∧ Ω ^ 2 < highFrequency Ω r g k := by
  have hm := mixing_pos (r := r) hg hk
  have hsq := frequencyGap_sq Ω r g k
  have hdn : 0 ≤ frequencyGap Ω r g k := Real.sqrt_nonneg _
  have hΩsq : 0 < Ω ^ 2 := sq_pos_of_pos hΩ
  have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
  have h1 : k ^ 2 + mixing r g k - Ω ^ 2 < frequencyGap Ω r g k := by
    have hpoly : (k ^ 2 + mixing r g k - Ω ^ 2) ^ 2 < discriminant Ω r g k := by
      unfold discriminant
      nlinarith
    nlinarith
  have h2 : Ω ^ 2 - k ^ 2 - mixing r g k < frequencyGap Ω r g k := by
    have hpoly : (Ω ^ 2 - k ^ 2 - mixing r g k) ^ 2 < discriminant Ω r g k := by
      unfold discriminant
      nlinarith
    nlinarith
  rw [lowFrequency_alternative hΩ]
  unfold highFrequency frequencySum
  constructor <;> linarith

theorem frequencyGap_pos {Ω g k : ℝ} (hΩ : 0 < Ω) (hg : g ≠ 0)
    (hk : k ≠ 0) (r : ℝ) : 0 < frequencyGap Ω r g k := by
  have h := normal_frequencies_straddle hΩ hg hk r
  rw [← normal_frequency_gap hΩ]
  linarith [h.1, h.2]

theorem spectral_weights_positive {Ω g k : ℝ} (hΩ : 0 < Ω) (hg : g ≠ 0)
    (hk : k ≠ 0) (r : ℝ) : 0 < lowWeight Ω r g k ∧ 0 < highWeight Ω r g k := by
  have h := normal_frequencies_straddle hΩ hg hk r
  exact ⟨div_pos (sub_pos.mpr h.1) (frequencyGap_pos hΩ hg hk r),
    div_pos (sub_pos.mpr h.2) (frequencyGap_pos hΩ hg hk r)⟩

theorem spectral_weights_sum {Ω g k : ℝ} (hΩ : 0 < Ω) (hg : g ≠ 0)
    (hk : k ≠ 0) (r : ℝ) : lowWeight Ω r g k + highWeight Ω r g k = 1 := by
  unfold lowWeight highWeight
  rw [← add_div]
  have hn : Ω ^ 2 - lowFrequency Ω r g k + (highFrequency Ω r g k - Ω ^ 2) =
      frequencyGap Ω r g k := by linarith [normal_frequency_gap hΩ r g k]
  rw [hn, div_self (ne_of_gt (frequencyGap_pos hΩ hg hk r))]

/-- The actual denominator factors into the two positive squared frequencies. -/
theorem response_factorization {Ω k x : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (hx : 0 ≤ x) (r g : ℝ) :
    response Ω r g k x = (x + Ω ^ 2) /
      ((x + lowFrequency Ω r g k) * (x + highFrequency Ω r g k)) := by
  have hlo := lowFrequency_pos hΩ hk r g
  have hhi := highFrequency_pos hΩ r g k
  have hden : x + k ^ 2 + mixing r g k * x / (x + Ω ^ 2) ≠ 0 := by
    have hm := mixing_nonneg r g k
    have hn : 0 ≤ mixing r g k * x / (x + Ω ^ 2) := by positivity
    positivity
  have hΩden : x + Ω ^ 2 ≠ 0 := by positivity
  have hloden : x + lowFrequency Ω r g k ≠ 0 := by positivity
  have hhiden : x + highFrequency Ω r g k ≠ 0 := by positivity
  unfold response
  rw [inv_eq_one_div]
  apply (div_eq_div_iff hden (mul_ne_zero hloden hhiden)).mpr
  have hsum := normal_frequency_sum hΩ r g k
  unfold frequencySum at hsum
  have hsumx := congrArg (fun y : ℝ => x * y) hsum
  dsimp at hsumx
  have hprod := normal_frequency_product hΩ r g k
  field_simp
  nlinarith [mul_nonneg (mixing_nonneg r g k) hx]

/-- Two strictly positive residues, including the direct magnetic contact. -/
theorem response_partial_fractions {Ω g k x : ℝ} (hΩ : 0 < Ω) (hg : g ≠ 0)
    (hk : k ≠ 0) (hx : 0 ≤ x) (r : ℝ) :
    response Ω r g k x = lowWeight Ω r g k / (x + lowFrequency Ω r g k) +
      highWeight Ω r g k / (x + highFrequency Ω r g k) := by
  rw [response_factorization hΩ hk hx]
  have hlo := lowFrequency_pos hΩ hk r g
  have hhi := highFrequency_pos hΩ r g k
  have hd := frequencyGap_pos hΩ hg hk r
  unfold lowWeight highWeight
  field_simp
  have hgap := normal_frequency_gap hΩ r g k
  nlinarith

/-- The spectral law is a probability law on the two positive squared energies.
At zero coupling it is the single free photon atom. -/
def photonSpectrum (Ω r g k : ℝ) : Measure ℝ :=
  if g = 0 then Measure.dirac (k ^ 2) else
    ENNReal.ofReal (lowWeight Ω r g k) • Measure.dirac (lowFrequency Ω r g k) +
    ENNReal.ofReal (highWeight Ω r g k) • Measure.dirac (highFrequency Ω r g k)

theorem photonSpectrum_probability {Ω k : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (r g : ℝ) : IsProbabilityMeasure (photonSpectrum Ω r g k) := by
  by_cases hg : g = 0
  · simp [photonSpectrum, hg]
    infer_instance
  · have hp := spectral_weights_positive hΩ hg hk r
    have hs := spectral_weights_sum hΩ hg hk r
    constructor
    simp only [photonSpectrum, if_neg hg, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp.1.le hp.2.le, hs, ENNReal.ofReal_one]

/-- Positive photon spectrum reproducing the exact Schur-complement response. -/
theorem photonSpectrum_response {Ω k x : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (hx : 0 ≤ x) (r g : ℝ) :
    (∫ s, (x + s)⁻¹ ∂photonSpectrum Ω r g k) = response Ω r g k x := by
  by_cases hg : g = 0
  · simp [photonSpectrum, hg, response, mixing]
  · have hp := spectral_weights_positive hΩ hg hk r
    rw [response_partial_fractions hΩ hg hk hx]
    simp only [photonSpectrum, if_neg hg]
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure]
    · simp [ENNReal.toReal_ofReal hp.1.le, ENNReal.toReal_ofReal hp.2.le, div_eq_mul_inv]
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The spectral measure is carried by strictly positive squared energies at
nonzero spatial momentum, including the zero-coupling case. -/
theorem photonSpectrum_positive_support {Ω k : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (r g : ℝ) : photonSpectrum Ω r g k (Set.Iic 0) = 0 := by
  by_cases hg : g = 0
  · simp [photonSpectrum, hg, not_le.mpr (sq_pos_of_ne_zero hk)]
  · have hl := lowFrequency_pos hΩ hk r g
    have hh := highFrequency_pos hΩ r g k
    simp [photonSpectrum, hg, not_le.mpr hl, not_le.mpr hh]

/-- The high branch tends to the material gap. -/
theorem highFrequency_tendsto (Ω r g : ℝ) :
    Tendsto (highFrequency Ω r g) (𝓝 0) (𝓝 (Ω ^ 2)) := by
  have hc : Continuous (highFrequency Ω r g) := by
    unfold highFrequency frequencySum frequencyGap discriminant mixing
    fun_prop
  convert hc.continuousAt.tendsto using 1
  simp [highFrequency, frequencySum, frequencyGap, discriminant, mixing,
    Real.sqrt_sq (sq_nonneg Ω)]

/-- Low squared energy divided by squared momentum tends to one. -/
theorem lowFrequency_ratio_tendsto {Ω : ℝ} (hΩ : 0 < Ω) (r g : ℝ) :
    Tendsto (fun k => lowFrequency Ω r g k / k ^ 2) (𝓝[≠] 0) (𝓝 1) := by
  have hc : Continuous (fun k => 2 * Ω ^ 2 /
      (frequencySum Ω r g k + frequencyGap Ω r g k)) := by
    unfold frequencySum frequencyGap discriminant mixing
    fun_prop (disch := intro k; exact ne_of_gt (sum_add_gap_pos hΩ r g k))
  have hval : 2 * Ω ^ 2 / (frequencySum Ω r g 0 + frequencyGap Ω r g 0) = 1 := by
    simp [frequencySum, frequencyGap, discriminant, mixing, Real.sqrt_sq (sq_nonneg Ω)]
    field_simp
    norm_num
  rw [← hval]
  apply Tendsto.congr' _ (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk' : k ≠ 0 := hk
  unfold lowFrequency
  field_simp

/-- The positive low energy has unit limiting carrier speed. -/
theorem lowEnergy_speed_tendsto {Ω : ℝ} (hΩ : 0 < Ω) (r g : ℝ) :
    Tendsto (fun k => Real.sqrt (lowFrequency Ω r g k) / |k|) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.continuous_sqrt.tendsto 1).comp (lowFrequency_ratio_tendsto hΩ r g)
  have he (k : ℝ) : Real.sqrt (lowFrequency Ω r g k / k ^ 2) =
      Real.sqrt (lowFrequency Ω r g k) / |k| := by
    rw [Real.sqrt_div' _ (sq_nonneg k), Real.sqrt_sq_eq_abs]
  simpa only [he, Real.sqrt_one, Function.comp_def] using h

/-- The low spectral residue tends to the full photon normalization. -/
theorem lowWeight_tendsto {Ω : ℝ} (hΩ : 0 < Ω) (r g : ℝ) :
    Tendsto (lowWeight Ω r g) (𝓝 0) (𝓝 1) := by
  have hd : frequencyGap Ω r g 0 = Ω ^ 2 := by
    simp [frequencyGap, discriminant, mixing, Real.sqrt_sq (sq_nonneg Ω)]
  have hc : ContinuousAt (lowWeight Ω r g) 0 := by
    unfold lowWeight lowFrequency
    apply ContinuousAt.div
    · apply continuousAt_const.sub
      apply ContinuousAt.div
      · fun_prop
      · unfold frequencySum frequencyGap discriminant mixing
        fun_prop
      · exact ne_of_gt (sum_add_gap_pos hΩ r g 0)
    · unfold frequencyGap discriminant mixing
      fun_prop
    · rw [hd]
      positivity
  convert hc.tendsto using 1
  simp [lowWeight, lowFrequency, hd, pow_ne_zero 2 hΩ.ne']

/-- The signed mixing amplitude in the Hamiltonian square itself. -/
def magneticCoupling (r g k : ℝ) : ℝ := g * k * Real.exp (-(r * k))

theorem magneticCoupling_sq (r g k : ℝ) : magneticCoupling r g k ^ 2 = mixing r g k := by
  have he : Real.exp (-(r * k)) ^ 2 = Real.exp (-(2 * r * k)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold magneticCoupling mixing
  rw [mul_pow, mul_pow, he]

/-- Stiffness of the precise Hamiltonian appearing in the source. -/
def stiffness (Ω r g k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![k ^ 2 + mixing r g k, -Ω * magneticCoupling r g k;
    -Ω * magneticCoupling r g k, Ω ^ 2]

/-- The quadratic form is the original magnetic square, including its contact. -/
theorem stiffness_form (Ω r g k A X : ℝ) :
    (k ^ 2 + mixing r g k) * A ^ 2 -
      2 * Ω * magneticCoupling r g k * A * X + Ω ^ 2 * X ^ 2 =
    k ^ 2 * A ^ 2 + (Ω * X - magneticCoupling r g k * A) ^ 2 := by
  rw [← magneticCoupling_sq]
  ring

/-- Strict positivity of each nonzero-momentum oscillator block. -/
theorem stiffness_form_pos {Ω k A X : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (hAX : A ≠ 0 ∨ X ≠ 0) (r g : ℝ) :
    0 < k ^ 2 * A ^ 2 + (Ω * X - magneticCoupling r g k * A) ^ 2 := by
  by_cases hA : A = 0
  · have hX : X ≠ 0 := hAX.resolve_left (not_ne_iff.mpr hA)
    simpa [hA] using sq_pos_of_ne_zero (mul_ne_zero hΩ.ne' hX)
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sq_pos_of_ne_zero hk) (sq_pos_of_ne_zero hA)) (sq_nonneg _)

/-- Exact normal-frequency polynomial of that same stiffness matrix. -/
theorem stiffness_characteristic {Ω : ℝ} (hΩ : 0 < Ω) (r g k y : ℝ) :
    Matrix.det (stiffness Ω r g k - y • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (lowFrequency Ω r g k - y) * (highFrequency Ω r g k - y) := by
  rw [Matrix.det_fin_two]
  norm_num [stiffness, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  have hm := magneticCoupling_sq r g k
  have hmy := congrArg (fun t : ℝ => Ω ^ 2 * t) hm
  dsimp at hmy
  have hs := normal_frequency_sum hΩ r g k
  have hsy := congrArg (fun t : ℝ => y * t) hs
  dsimp at hsy
  have hp := normal_frequency_product hΩ r g k
  unfold frequencySum at hs hsy
  nlinarith

/-- Euclidean precision before either oscillator is integrated out. -/
def precision (Ω r g k x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  stiffness Ω r g k + x • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem precision_determinant {Ω : ℝ} (hΩ : 0 < Ω) (r g k x : ℝ) :
    Matrix.det (precision Ω r g k x) =
      (x + lowFrequency Ω r g k) * (x + highFrequency Ω r g k) := by
  have h := stiffness_characteristic hΩ r g k (-x)
  simpa only [precision, neg_smul, sub_neg_eq_add, add_comm] using h

/-- The photon covariance is the (A,A) entry of the inverse of the original
joint Gaussian precision. Thus its spectral law concerns the stated action. -/
theorem precision_inverse_photon {Ω k x : ℝ} (hΩ : 0 < Ω) (hk : k ≠ 0)
    (hx : 0 ≤ x) (r g : ℝ) :
    (precision Ω r g k x)⁻¹ 0 0 = response Ω r g k x := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, precision_determinant hΩ]
  change Ring.inverse ((x + lowFrequency Ω r g k) * (x + highFrequency Ω r g k)) *
    precision Ω r g k x 1 1 = response Ω r g k x
  have he : precision Ω r g k x 1 1 = x + Ω ^ 2 := by simp [precision, stiffness]; ring
  rw [he, Ring.inverse_eq_inv, response_factorization hΩ hk hx]
  ring

/-- The sum of the positive normal energies gives the source's exact vacuum
shift, rather than a separate ultraviolet approximation. -/
theorem normal_energy_sum {Ω k : ℝ} (hΩ : 0 < Ω) (hk : 0 ≤ k) (r g : ℝ) :
    Real.sqrt (lowFrequency Ω r g k) + Real.sqrt (highFrequency Ω r g k) =
      Real.sqrt ((k + Ω) ^ 2 + mixing r g k) := by
  have hl : 0 ≤ lowFrequency Ω r g k := by
    unfold lowFrequency
    exact div_nonneg (by positivity) (sum_add_gap_pos hΩ r g k).le
  have hh := highFrequency_pos hΩ r g k
  have hp : Real.sqrt (lowFrequency Ω r g k) * Real.sqrt (highFrequency Ω r g k) = Ω * k := by
    rw [← Real.sqrt_mul hl, normal_frequency_product hΩ,
      Real.sqrt_mul (sq_nonneg Ω), Real.sqrt_sq hΩ.le, Real.sqrt_sq hk]
  have hs := normal_frequency_sum hΩ r g k
  unfold frequencySum at hs
  have hsq : (Real.sqrt (lowFrequency Ω r g k) + Real.sqrt (highFrequency Ω r g k)) ^ 2 =
      (k + Ω) ^ 2 + mixing r g k := by
    nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hh.le]
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-- All constitutive data stay on one locked sector plane; its geometric pole
unit remains a norm-one vector independently of the material coupling. -/
structure SelectedModel (E : Type*) [Norm E] where
  diamond : SectorPlane.Plane E
  Ω : ℝ
  material_positive : 0 < Ω
  r : ℝ
  depth_positive : 0 < r
  g : ℝ

/-- Explicit positive photon law on a selected carrier. This uses its intrinsic
spatial momentum and squared Euclidean frequency, while retaining the original
plane label and its normalized geometric pole direction. -/
theorem selected_model_photon_law {E : Type*} [Norm E] (model : SelectedModel E)
    (p : SectorPlane.Spatial) (hp : p ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    ‖model.diamond.Ghat.val‖ = 1 ∧
    IsProbabilityMeasure (photonSpectrum model.Ω model.r model.g ‖p‖) ∧
    photonSpectrum model.Ω model.r model.g ‖p‖ (Set.Iic 0) = 0 ∧
    (∫ s, (x + s)⁻¹ ∂photonSpectrum model.Ω model.r model.g ‖p‖) =
      (precision model.Ω model.r model.g ‖p‖ x)⁻¹ 0 0 := by
  have hk := norm_ne_zero_iff.mpr hp
  refine ⟨model.diamond.Ghat.property,
    photonSpectrum_probability model.material_positive hk model.r model.g,
    photonSpectrum_positive_support model.material_positive hk model.r model.g, ?_⟩
  rw [photonSpectrum_response model.material_positive hk hx,
    precision_inverse_photon model.material_positive hk hx]

end UV.ResumeCarrierPolarization

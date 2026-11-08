import UV.CliffordWard
import UV.DepthAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual fixed-transfer Ward contractions, with their matrix inverses and
the kernel ratios retained throughout. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise RealInnerProductSpace

namespace UV

def transferVertexContraction
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (P p' p : DiracMomentum) : DiracMatrix := ∑ μ, (P μ : ℂ) • G p' p μ

theorem dressedWard_transfer_contractions
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m : ℝ) (hw : DressedWardCompatible a M m G) (k P : DiracMomentum) :
    transferVertexContraction G P (k + P) k =
        dressedDiracSymbol a M m (k + P) - dressedDiracSymbol a M m k ∧
      transferVertexContraction G P k (k + P) =
        dressedDiracSymbol a M m (k + P) - dressedDiracSymbol a M m k := by
  constructor
  · simpa only [transferVertexContraction, PiLp.add_apply, add_sub_cancel_left] using hw (k + P) k
  · have h := hw k (k + P)
    have hn : (∑ μ, ((k μ - (k + P) μ : ℝ) : ℂ) • G k (k + P) μ) =
        -transferVertexContraction G P k (k + P) := by
      simp [transferVertexContraction, PiLp.add_apply, neg_smul,
        Finset.sum_neg_distrib]
    rw [hn] at h
    have hh := congrArg Neg.neg h
    simpa only [neg_neg, neg_sub] using hh

theorem doubleWard_matrix_identity (D D' S S' : DiracMatrix)
    (hDS : D * S = 1) (hSD : S * D = 1) (hD'S' : D' * S' = 1) :
    ((D' - D) * S) * ((D' - D) * S') = D' * S + D * S' - (2 : ℂ) • 1 := by
  have hl : (D' - D) * S = D' * S - 1 := by rw [sub_mul, hDS]
  have hr : (D' - D) * S' = 1 - D * S' := by rw [sub_mul, hD'S']
  rw [hl, hr]
  have hm : (D' * S) * (D * S') = 1 := by
    calc
      _ = D' * (S * D) * S' := by noncomm_ring
      _ = _ := by rw [hSD, Matrix.mul_one, hD'S']
  simp only [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, hm]
  module

def fixedTransferBubbleComponent
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m e : ℝ) (P k : DiracMomentum) (μ ν : Fin 4) : ℂ :=
  (-(e ^ 2) : ℂ) * Matrix.trace
    ((G (k + P) k μ * dressedDiracPropagator a M m k) *
      (G k (k + P) ν * dressedDiracPropagator a M m (k + P)))

def doubleWardBubble
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m e : ℝ) (P k : DiracMomentum) : ℂ :=
  (-(e ^ 2) : ℂ) * Matrix.trace
    ((transferVertexContraction G P (k + P) k * dressedDiracPropagator a M m k) *
      (transferVertexContraction G P k (k + P) * dressedDiracPropagator a M m (k + P)))

theorem doubleWardBubble_identity
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    (hw : DressedWardCompatible a M m G) (P k : DiracMomentum) :
    doubleWardBubble G a M m e P k = (-(e ^ 2) : ℂ) * Matrix.trace
      (dressedDiracSymbol a M m (k + P) * dressedDiracPropagator a M m k +
        dressedDiracSymbol a M m k * dressedDiracPropagator a M m (k + P) - (2 : ℂ) • 1) := by
  obtain ⟨h₁, h₂⟩ := dressedWard_transfer_contractions G a M m hw k P
  unfold doubleWardBubble
  rw [h₁, h₂, doubleWard_matrix_identity _ _ _ _
    (dressedDiracSymbol_mul_propagator a M hm k)
    (dressedDiracPropagator_mul_symbol a M hm k)
    (dressedDiracSymbol_mul_propagator a M hm (k + P))]

theorem doubleWardBubble_eq_sum_components
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M m e : ℝ) (P k : DiracMomentum) :
    doubleWardBubble G a M m e P k =
      ∑ μ, ∑ ν, ((P μ : ℂ) * (P ν : ℂ)) * fixedTransferBubbleComponent G a M m e P k μ ν := by
  unfold doubleWardBubble transferVertexContraction fixedTransferBubbleComponent
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem diracMomentum_inner (k l : DiracMomentum) :
    ⟪k, l⟫ = k 0 * l 0 + k 1 * l 1 + k 2 * l 2 + k 3 * l 3 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_succ]
  change l 0 * k 0 + (l 1 * k 1 + (l 2 * k 2 + (l 3 * k 3 + 0))) = _
  ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
theorem freeDirac_mixed_trace (m : ℝ) (k l : DiracMomentum) :
    Matrix.trace (freeDiracSymbol m l * freeDiracPropagator m k) =
      ((4 * (⟪k, l⟫ + m ^ 2) / (‖k‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
  have hn : Matrix.trace (freeDiracSymbol m l * freeDiracNumerator m k) =
      ((4 * (⟪k, l⟫ + m ^ 2) : ℝ) : ℂ) := by
    rw [diracMomentum_inner]
    apply Complex.ext <;>
      simp [freeDiracSymbol, freeDiracNumerator, diracSlash, euclideanGamma,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, smul_eq_mul, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  simp only [freeDiracPropagator, Matrix.mul_smul, Matrix.trace_smul, hn, smul_eq_mul]
  push_cast
  ring

theorem kernel_ratio_exact (a M u v : ℝ) :
    kernel a M u / kernel a M v =
      Real.exp (a * (Real.sqrt (v + M ^ 2) - Real.sqrt (u + M ^ 2))) := by
  unfold kernel depthProfile
  rw [← Real.exp_sub]
  congr 1
  ring

theorem dressedDirac_mixed_trace (a M m : ℝ) (k l : DiracMomentum) :
    Matrix.trace (dressedDiracSymbol a M m l * dressedDiracPropagator a M m k) =
      ((4 * (⟪k, l⟫ + m ^ 2) *
        Real.exp (a * (Real.sqrt (‖l‖ ^ 2 + M ^ 2) - Real.sqrt (‖k‖ ^ 2 + M ^ 2))) /
        (‖k‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
  simp only [dressedDiracSymbol, dressedDiracPropagator, smul_mul_smul, Matrix.trace_smul,
    freeDirac_mixed_trace, smul_eq_mul]
  have hk := kernel_ratio_exact a M (‖k‖ ^ 2) (‖l‖ ^ 2)
  have hkC := congrArg (fun x : ℝ => (x : ℂ)) hk
  push_cast at hkC ⊢
  simp only [div_eq_mul_inv] at hkC ⊢
  rw [mul_comm (kernel a M (‖l‖ ^ 2) : ℂ)⁻¹ (kernel a M (‖k‖ ^ 2) : ℂ), hkC]
  ring

def fixedTransferScalar (a M m e : ℝ) (P k : DiracMomentum) : ℝ :=
  -4 * e ^ 2 * ((⟪k, k + P⟫ + m ^ 2) *
    (Real.exp (a * (Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) - Real.sqrt (‖k‖ ^ 2 + M ^ 2))) /
        (‖k‖ ^ 2 + m ^ 2) +
      Real.exp (-a * (Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) - Real.sqrt (‖k‖ ^ 2 + M ^ 2))) /
        (‖k + P‖ ^ 2 + m ^ 2)) - 2)

theorem doubleWardBubble_scalar
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    (hw : DressedWardCompatible a M m G) (P k : DiracMomentum) :
    doubleWardBubble G a M m e P k = (fixedTransferScalar a M m e P k : ℂ) := by
  rw [doubleWardBubble_identity G a M e hm hw]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, dressedDirac_mixed_trace]
  unfold fixedTransferScalar
  have hint : ⟪k + P, k⟫ = ⟪k, k + P⟫ := real_inner_comm _ _
  simp only [hint]
  have he : a * (Real.sqrt (‖k‖ ^ 2 + M ^ 2) - Real.sqrt (‖k + P‖ ^ 2 + M ^ 2)) =
      -a * (Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) - Real.sqrt (‖k‖ ^ 2 + M ^ 2)) := by ring
  rw [he]
  push_cast
  ring

def transferScaledIncomingRoot (M r : ℝ) (v : DiracMomentum) : ℝ :=
  Real.sqrt (‖v‖ ^ 2 + (M * r⁻¹) ^ 2)

def transferScaledOutgoingRoot (M : ℝ) (P : DiracMomentum) (r : ℝ) (v : DiracMomentum) : ℝ :=
  Real.sqrt (‖v + r⁻¹ • P‖ ^ 2 + (M * r⁻¹) ^ 2)

def transferScaledDelta (M : ℝ) (P : DiracMomentum) (r : ℝ) (v : DiracMomentum) : ℝ :=
  (2 * ⟪v, P⟫ + ‖P‖ ^ 2 * r⁻¹) /
    (transferScaledOutgoingRoot M P r v + transferScaledIncomingRoot M r v)

def transferScaledB (m : ℝ) (P : DiracMomentum) (r : ℝ) (v : DiracMomentum) : ℝ :=
  ‖v‖ ^ 2 + ⟪v, P⟫ * r⁻¹ + (m * r⁻¹) ^ 2

def scaledFixedTransferScalar (a M m e : ℝ) (P : DiracMomentum) (r : ℝ) (v : DiracMomentum) : ℝ :=
  -4 * e ^ 2 * (transferScaledB m P r v *
    (Real.exp (a * transferScaledDelta M P r v) / (‖v‖ ^ 2 + (m * r⁻¹) ^ 2) +
      Real.exp (-a * transferScaledDelta M P r v) /
        (‖v + r⁻¹ • P‖ ^ 2 + (m * r⁻¹) ^ 2)) - 2)

theorem scaled_shift_identity {r : ℝ} (hr : 0 < r) (v P : DiracMomentum) :
    r • (v + r⁻¹ • P) = r • v + P := by
  rw [smul_add, ← mul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem norm_sq_mass_scale {r : ℝ} (hr : 0 < r) (v : DiracMomentum) (m : ℝ) :
    ‖r • v‖ ^ 2 + m ^ 2 = r ^ 2 * (‖v‖ ^ 2 + (m * r⁻¹) ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  field_simp [hr.ne']

theorem momentumRoot_scale {r : ℝ} (hr : 0 < r) (v : DiracMomentum) (M : ℝ) :
    Real.sqrt (‖r • v‖ ^ 2 + M ^ 2) = r * transferScaledIncomingRoot M r v := by
  rw [norm_sq_mass_scale hr, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  rfl

theorem momentumRoot_sum_pos (M : ℝ) {P : DiracMomentum} (hP : P ≠ 0) (k : DiracMomentum) :
    0 < Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) + Real.sqrt (‖k‖ ^ 2 + M ^ 2) := by
  by_cases hk : k = 0
  · subst k
    have hp : 0 < ‖P‖ := norm_pos_iff.mpr hP
    exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by simpa only [zero_add] using
      (by positivity : 0 < ‖P‖ ^ 2 + M ^ 2))) (Real.sqrt_nonneg _)
  · have hp : 0 < ‖k‖ := norm_pos_iff.mpr hk
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr (by positivity))

theorem momentumRoot_difference_quotient (M : ℝ) {P : DiracMomentum} (hP : P ≠ 0)
    (k : DiracMomentum) :
    Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) - Real.sqrt (‖k‖ ^ 2 + M ^ 2) =
      (‖k + P‖ ^ 2 - ‖k‖ ^ 2) /
        (Real.sqrt (‖k + P‖ ^ 2 + M ^ 2) + Real.sqrt (‖k‖ ^ 2 + M ^ 2)) := by
  apply (eq_div_iff (momentumRoot_sum_pos M hP k).ne').mpr
  have h₁ := Real.sq_sqrt (show 0 ≤ ‖k + P‖ ^ 2 + M ^ 2 by positivity)
  have h₂ := Real.sq_sqrt (show 0 ≤ ‖k‖ ^ 2 + M ^ 2 by positivity)
  nlinarith

theorem momentumRoot_difference_scaled (M : ℝ) {P : DiracMomentum} (hP : P ≠ 0)
    {r : ℝ} (hr : 0 < r) (v : DiracMomentum) :
    Real.sqrt (‖r • v + P‖ ^ 2 + M ^ 2) - Real.sqrt (‖r • v‖ ^ 2 + M ^ 2) =
      transferScaledDelta M P r v := by
  have hout : Real.sqrt (‖r • v + P‖ ^ 2 + M ^ 2) =
      r * transferScaledOutgoingRoot M P r v := by
    rw [← scaled_shift_identity hr v P, momentumRoot_scale hr]
    rfl
  have hin := momentumRoot_scale hr v M
  have hsum := momentumRoot_sum_pos M hP (r • v)
  rw [hout, hin] at hsum
  have hs : transferScaledOutgoingRoot M P r v + transferScaledIncomingRoot M r v ≠ 0 := by
    intro hz
    have : r * transferScaledOutgoingRoot M P r v + r * transferScaledIncomingRoot M r v = 0 := by
      rw [← mul_add, hz, mul_zero]
    linarith
  rw [momentumRoot_difference_quotient M hP, hout, hin, norm_add_sq_real]
  simp only [inner_smul_left, starRingEnd_apply, star_trivial]
  unfold transferScaledDelta
  rw [← mul_add]
  field_simp [hr.ne', hs]
  ring

theorem fixedTransferScalar_scale (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    {P : DiracMomentum} (hP : P ≠ 0) {r : ℝ} (hr : 0 < r) (v : DiracMomentum) :
    fixedTransferScalar a M m e P (r • v) = scaledFixedTransferScalar a M m e P r v := by
  have hin := norm_sq_mass_scale hr v m
  have hout : ‖r • v + P‖ ^ 2 + m ^ 2 =
      r ^ 2 * (‖v + r⁻¹ • P‖ ^ 2 + (m * r⁻¹) ^ 2) := by
    rw [← scaled_shift_identity hr v P, norm_sq_mass_scale hr]
  have hb : ⟪r • v, r • v + P⟫ + m ^ 2 = r ^ 2 * transferScaledB m P r v := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    unfold transferScaledB
    field_simp [hr.ne']
  have hmi : 0 < m * r⁻¹ := mul_pos hm (inv_pos.mpr hr)
  have hdi : ‖v‖ ^ 2 + (m * r⁻¹) ^ 2 ≠ 0 := by positivity
  have hdo : ‖v + r⁻¹ • P‖ ^ 2 + (m * r⁻¹) ^ 2 ≠ 0 := by positivity
  unfold fixedTransferScalar scaledFixedTransferScalar
  rw [momentumRoot_difference_scaled M hP hr, hin, hout, hb]
  field_simp [hr.ne', hdi, hdo]

theorem scaledFixedTransferScalar_joint_limit (a M m e : ℝ) (P n : DiracMomentum) (hn : n ≠ 0) :
    Tendsto (fun q : ℝ × DiracMomentum => scaledFixedTransferScalar a M m e P q.1 q.2)
      (atTop ×ˢ 𝓝 n) (𝓝 (-8 * e ^ 2 * (Real.cosh (a * (⟪n, P⟫ / ‖n‖)) - 1))) := by
  let L : Filter (ℝ × DiracMomentum) := atTop ×ˢ 𝓝 n
  have hv : Tendsto (fun q : ℝ × DiracMomentum => q.2) L (𝓝 n) := tendsto_snd
  have hi : Tendsto (fun q : ℝ × DiracMomentum => q.1⁻¹) L (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_fst
  have hvn := hv.norm.pow 2
  have hinner : Tendsto (fun q : ℝ × DiracMomentum => ⟪q.2, P⟫) L (𝓝 ⟪n, P⟫) :=
    hv.inner tendsto_const_nhds
  have hshift : Tendsto (fun q : ℝ × DiracMomentum => q.2 + q.1⁻¹ • P) L (𝓝 n) := by
    simpa only [zero_smul, add_zero] using hv.add (hi.smul tendsto_const_nhds)
  have hvout := hshift.norm.pow 2
  have hri : Tendsto (fun q : ℝ × DiracMomentum => transferScaledIncomingRoot M q.1 q.2)
      L (𝓝 ‖n‖) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp (hvn.add ((hi.const_mul M).pow 2))
    simpa only [transferScaledIncomingRoot, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, Real.sqrt_sq (norm_nonneg n)] using h
  have hro : Tendsto (fun q : ℝ × DiracMomentum => transferScaledOutgoingRoot M P q.1 q.2)
      L (𝓝 ‖n‖) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp (hvout.add ((hi.const_mul M).pow 2))
    simpa only [transferScaledOutgoingRoot, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, Real.sqrt_sq (norm_nonneg n)] using h
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hsum : ‖n‖ + ‖n‖ ≠ 0 := by positivity
  have hd : Tendsto (fun q : ℝ × DiracMomentum => transferScaledDelta M P q.1 q.2)
      L (𝓝 (⟪n, P⟫ / ‖n‖)) := by
    have h := ((hinner.const_mul 2).add (hi.const_mul (‖P‖ ^ 2))).div (hro.add hri) hsum
    have he : (2 * ⟪n, P⟫) / (‖n‖ + ‖n‖) = ⟪n, P⟫ / ‖n‖ := by
      field_simp [hnpos.ne']
      ring
    simpa only [transferScaledDelta, mul_zero, add_zero, he] using h
  have hbi : Tendsto (fun q : ℝ × DiracMomentum => ‖q.2‖ ^ 2 + (m * q.1⁻¹) ^ 2)
      L (𝓝 (‖n‖ ^ 2)) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      hvn.add ((hi.const_mul m).pow 2)
  have hbo : Tendsto (fun q : ℝ × DiracMomentum => ‖q.2 + q.1⁻¹ • P‖ ^ 2 + (m * q.1⁻¹) ^ 2)
      L (𝓝 (‖n‖ ^ 2)) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      hvout.add ((hi.const_mul m).pow 2)
  have hb : Tendsto (fun q : ℝ × DiracMomentum => transferScaledB m P q.1 q.2)
      L (𝓝 (‖n‖ ^ 2)) := by
    simpa only [transferScaledB, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (hvn.add (hinner.mul hi)).add ((hi.const_mul m).pow 2)
  have hn2 : ‖n‖ ^ 2 ≠ 0 := (sq_pos_of_pos hnpos).ne'
  have he₁ := (Real.continuous_exp.tendsto _).comp (hd.const_mul a)
  have he₂ := (Real.continuous_exp.tendsto _).comp (hd.const_mul (-a))
  have ht₁ := he₁.div hbi hn2
  have ht₂ := he₂.div hbo hn2
  have hall := ((hb.mul (ht₁.add ht₂)).sub (tendsto_const_nhds (x := (2 : ℝ)))).const_mul (-4 * e ^ 2)
  have he : (-4 * e ^ 2) * (‖n‖ ^ 2 *
      (Real.exp (a * (⟪n, P⟫ / ‖n‖)) / ‖n‖ ^ 2 +
        Real.exp (-a * (⟪n, P⟫ / ‖n‖)) / ‖n‖ ^ 2) - 2) =
      -8 * e ^ 2 * (Real.cosh (a * (⟪n, P⟫ / ‖n‖)) - 1) := by
    rw [Real.cosh_eq]
    rw [show -a * (⟪n, P⟫ / ‖n‖) = -(a * (⟪n, P⟫ / ‖n‖)) by ring]
    field_simp [hn2]
    ring
  simpa only [scaledFixedTransferScalar, he] using hall

theorem fixedTransferScalar_joint_limit (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    {P : DiracMomentum} (hP : P ≠ 0) (n : DiracMomentum) (hn : n ≠ 0) :
    Tendsto (fun q : ℝ × DiracMomentum => fixedTransferScalar a M m e P (q.1 • q.2))
      (atTop ×ˢ 𝓝 n) (𝓝 (-8 * e ^ 2 * (Real.cosh (a * (⟪n, P⟫ / ‖n‖)) - 1))) := by
  apply (scaledFixedTransferScalar_joint_limit a M m e P n hn).congr'
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  exact (fixedTransferScalar_scale a M e hm hP hq q.2).symm

/-- The exact ray limit asserted in cor:OQED-fixed-transfer-obstruction. -/
theorem fixedTransferScalar_unit_ray_limit (a M e : ℝ) {m : ℝ} (hm : 0 < m)
    {P : DiracMomentum} (hP : P ≠ 0) (n : DiracMomentum) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => fixedTransferScalar a M m e P (r • n)) atTop
      (𝓝 (-8 * e ^ 2 * (Real.cosh (a * ⟪n, P⟫) - 1))) := by
  have hne : n ≠ 0 := by intro hz; rw [hz, norm_zero] at hn; norm_num at hn
  have h := (fixedTransferScalar_joint_limit a M e hm hP n hne).comp
    (tendsto_id.prodMk tendsto_const_nhds)
  simpa only [Function.comp_def, hn, div_one] using h

theorem doubleWardBubble_unit_ray_limit
    (G : DiracMomentum → DiracMomentum → Fin 4 → DiracMatrix)
    (a M e : ℝ) {m : ℝ} (hm : 0 < m) (hw : DressedWardCompatible a M m G)
    {P : DiracMomentum} (hP : P ≠ 0) (n : DiracMomentum) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => (doubleWardBubble G a M m e P (r • n)).re) atTop
      (𝓝 (-8 * e ^ 2 * (Real.cosh (a * ⟪n, P⟫) - 1))) := by
  simp_rw [doubleWardBubble_scalar G a M e hm hw, Complex.ofReal_re]
  exact fixedTransferScalar_unit_ray_limit a M e hm hP n hn

end UV

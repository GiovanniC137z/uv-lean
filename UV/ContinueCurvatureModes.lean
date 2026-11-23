import UV.ResumeCurvatureDistributions
import UV.ContinueCurvatureFieldLaw
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Real sine and cosine normalization with the actual Haar probability
on the stated four-torus, in the selected signed lattice. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators ComplexConjugate Topology SchwartzMap FourierTransform InnerProductSpace ContDiff

namespace UV.ContinueCurvatureModes

open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.FurtherCurvatureShell
open UV.ResumeCurvatureDistributions UV.ResumeCurvatureRawBounds
open UV.ResumeCurvatureSmooth UV.ResumeCurvatureRawIdentity
open UV.ContinueCurvatureFieldLaw UV.ContinueCurvatureMarginals
open UV.ExtendCurvatureGibbs UV.ResumeCurvatureRawLaw
open UV.RevisionCurvatureDeterminant (latticeFrequency)

private instance positivePeriod : Fact (0 < (2 : ℝ) * π) := ⟨by positivity⟩

theorem torusCharacter_add (k l : TorusMode) (x : Torus) :
    torusCharacter (k+l) x = torusCharacter k x * torusCharacter l x := by
  unfold torusCharacter
  simp only [ContinuousMap.prod_apply, ContinuousMap.comp_apply]
  simp_rw [Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

theorem torusCharacter_neg (k : TorusMode) (x : Torus) :
    torusCharacter (-k) x = conj (torusCharacter k x) := by
  unfold torusCharacter
  simp only [ContinuousMap.prod_apply, ContinuousMap.comp_apply]
  simp_rw [Pi.neg_apply, fourier_neg, map_prod]

theorem circle_character_integral (k : ℤ) :
    (∫ x : AddCircle ((2 : ℝ)*π), fourier k x ∂AddCircle.haarAddCircle) =
      if k = 0 then (1 : ℂ) else 0 := by
  split_ifs with hk
  · subst k
    simp_rw [fourier_zero]
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (show 0 < (2:ℝ)*π by positivity))

theorem torus_character_integral (k : TorusMode) :
    (∫ x, torusCharacter k x ∂normalizedTorusVolume) = if k = 0 then (1 : ℂ) else 0 := by
  calc
    _ = ∏ j : Fin 4, ∫ x : AddCircle ((2 : ℝ)*π), fourier (k j) x ∂AddCircle.haarAddCircle :=
      integral_fintype_prod_eq_prod (fun j : Fin 4 => fun x : AddCircle ((2 : ℝ)*π) => fourier (k j) x)
    _ = _ := by
      simp_rw [circle_character_integral]
      by_cases hk : k = 0
      · simp [hk]
      have h : ∃ j : Fin 4, k j ≠ 0 := by
        by_contra! h
        apply hk
        funext j
        exact h j
      obtain ⟨j,hj⟩ := h
      rw [if_neg hk]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private def negativeMode (k : MeanZeroMode) : MeanZeroMode := ⟨-k.1, neg_ne_zero.mpr k.2⟩

private theorem firstActive_neg (k : MeanZeroMode) :
    firstActive (negativeMode k) = firstActive k := by
  unfold firstActive
  have hf : Finset.univ.filter (fun j : Fin 4 => (negativeMode k).1 j ≠ 0) =
      Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0) := by
    ext j
    simp [negativeMode]
  congr 1

private theorem firstActive_nonzero (k : MeanZeroMode) : k.1 (firstActive k) ≠ 0 := by
  have hm : firstActive k ∈ Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hm).2

private def phaseChooser (k : MeanZeroMode) : ℂ :=
  if 0 < k.1 (firstActive k) then 1 else Complex.I

private theorem phaseChooser_norm_sq (k : MeanZeroMode) :
    phaseChooser k * conj (phaseChooser k) = 1 := by
  unfold phaseChooser
  split <;> simp [Complex.conj_I]

private theorem phaseChooser_neg_cancel (k : MeanZeroMode) :
    phaseChooser k * phaseChooser (negativeMode k) +
      conj (phaseChooser k) * conj (phaseChooser (negativeMode k)) = 0 := by
  unfold phaseChooser
  rw [firstActive_neg]
  change (if 0 < k.1 (firstActive k) then (1:ℂ) else Complex.I) *
    (if 0 < -k.1 (firstActive k) then (1:ℂ) else Complex.I) +
    conj (if 0 < k.1 (firstActive k) then (1:ℂ) else Complex.I) *
    conj (if 0 < -k.1 (firstActive k) then (1:ℂ) else Complex.I) = 0
  have hk := firstActive_nonzero k
  rcases lt_or_gt_of_ne hk with hs | hs
  · simp [not_lt_of_ge hs.le, hs, Complex.conj_I]
  · simp [hs, not_lt_of_ge hs.le, Complex.conj_I]

private theorem mode_expansion (k : MeanZeroMode) (x : Torus) :
    (realTorusMode k x : ℂ) =
      ((sqrt 2 : ℝ) : ℂ) / 2 * (phaseChooser k * torusCharacter k x +
        conj (phaseChooser k) * torusCharacter (-k.1) x) := by
  unfold realTorusMode phaseChooser
  split
  · simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [torusCharacter_neg]
    apply Complex.ext <;>
      simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im]
    all_goals ring
  · simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    rw [torusCharacter_neg]
    apply Complex.ext <;>
      simp [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im, Complex.conj_I]
    all_goals ring

private theorem character_integrable (k : TorusMode) :
    Integrable (torusCharacter k) normalizedTorusVolume := by
  exact (BoundedContinuousFunction.mkOfCompact (torusCharacter k)).integrable _

private theorem mode_product_integral_expansion (k l : MeanZeroMode) :
    (∫ x, ((realTorusMode k x : ℂ) * (realTorusMode l x : ℂ)) ∂normalizedTorusVolume) =
      ((((sqrt 2 : ℝ) : ℂ) / 2)^2) *
      (phaseChooser k * phaseChooser l * (if k.1 + l.1 = 0 then (1:ℂ) else 0) +
        phaseChooser k * conj (phaseChooser l) * (if k.1 + -l.1 = 0 then (1:ℂ) else 0) +
        conj (phaseChooser k) * phaseChooser l * (if -k.1 + l.1 = 0 then (1:ℂ) else 0) +
        conj (phaseChooser k) * conj (phaseChooser l) * (if -k.1 + -l.1 = 0 then (1:ℂ) else 0)) := by
  calc
    _ = ∫ x, ((((sqrt 2 : ℝ) : ℂ) / 2)^2) *
        (phaseChooser k * phaseChooser l * torusCharacter (k.1+l.1) x +
          phaseChooser k * conj (phaseChooser l) * torusCharacter (k.1 + -l.1) x +
          conj (phaseChooser k) * phaseChooser l * torusCharacter (-k.1+l.1) x +
          conj (phaseChooser k) * conj (phaseChooser l) * torusCharacter (-k.1 + -l.1) x)
        ∂normalizedTorusVolume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [mode_expansion, torusCharacter_add]
        ring)
    _ = _ := by
      rw [integral_const_mul]
      let f₁ (x : Torus) := phaseChooser k * phaseChooser l * torusCharacter (k.1+l.1) x
      let f₂ (x : Torus) := phaseChooser k * conj (phaseChooser l) * torusCharacter (k.1 + -l.1) x
      let f₃ (x : Torus) := conj (phaseChooser k) * phaseChooser l * torusCharacter (-k.1+l.1) x
      let f₄ (x : Torus) := conj (phaseChooser k) * conj (phaseChooser l) * torusCharacter (-k.1 + -l.1) x
      have h₁ : Integrable f₁ normalizedTorusVolume :=
        (character_integrable (k.1+l.1)).const_mul _
      have h₂ : Integrable f₂ normalizedTorusVolume :=
        (character_integrable (k.1 + -l.1)).const_mul _
      have h₃ : Integrable f₃ normalizedTorusVolume :=
        (character_integrable (-k.1+l.1)).const_mul _
      have h₄ : Integrable f₄ normalizedTorusVolume :=
        (character_integrable (-k.1 + -l.1)).const_mul _
      change ((((sqrt 2 : ℝ) : ℂ) / 2)^2) *
        (∫ x, ((f₁ + f₂) + f₃) x + f₄ x ∂normalizedTorusVolume) = _
      rw [integral_add ((h₁.add h₂).add h₃) h₄]
      have h123 := integral_add (h₁.add h₂) h₃
      have h12 := integral_add h₁ h₂
      simp only [Pi.add_apply] at h123 h12 ⊢
      rw [h123, h12]
      simp_rw [f₁, f₂, f₃, f₄, integral_const_mul, torus_character_integral]

/-- The signed real sine/cosine modes have exactly unit normalization
and are mutually orthogonal under the literal normalized Haar measure. -/
theorem real_mode_integral_orthonormal (k l : MeanZeroMode) :
    (∫ x, realTorusMode k x * realTorusMode l x ∂normalizedTorusVolume) =
      if k = l then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]
  rw [mode_product_integral_expansion]
  have hSQ : ((((sqrt 2 : ℝ) : ℂ) / 2)^2) = (1/2 : ℂ) := by
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hSQ]
  by_cases he : k = l
  · subst l
    have hn : k.1 + k.1 ≠ 0 := by
      intro h
      apply k.2
      funext j
      have hj := congrFun h j
      change k.1 j + k.1 j = 0 at hj
      change k.1 j = 0
      omega
    have hnn : -k.1 + -k.1 ≠ 0 := by rw [← neg_add]; exact neg_ne_zero.mpr hn
    simp only [if_neg hn, if_neg hnn, add_neg_cancel, neg_add_cancel, if_true, mul_zero,
      zero_add, add_zero, mul_one, Complex.ofReal_one]
    rw [mul_comm (conj (phaseChooser k)), phaseChooser_norm_sq]
    norm_num
  · have hkl : k.1 + -l.1 ≠ 0 := fun hz => he (Subtype.ext (sub_eq_zero.mp hz))
    have hlk : -k.1 + l.1 ≠ 0 := by
      rw [add_comm]
      exact fun hz => he (Subtype.ext (sub_eq_zero.mp hz).symm)
    have hnn : -k.1 + -l.1 = 0 ↔ k.1 + l.1 = 0 := by
      rw [← neg_add, neg_eq_zero]
    by_cases hz : k.1 + l.1 = 0
    · have hl : l = negativeMode k := Subtype.ext (eq_neg_of_add_eq_zero_right hz)
      simp only [if_neg he, if_pos hz, if_pos (hnn.mpr hz), if_neg hkl,
        if_neg hlk, mul_zero, add_zero, mul_one, Complex.ofReal_zero]
      rw [hl, phaseChooser_neg_cancel, mul_zero]
    · simp only [if_neg he, if_neg hz, if_neg (fun h => hz (hnn.mp h)),
        if_neg hkl, if_neg hlk, mul_zero, zero_add, Complex.ofReal_zero]

private theorem fourierPair_integrable (F : ContinuousField) (k : MeanZeroMode) :
    Integrable (fun x => F x * realTorusMode k x) normalizedTorusVolume := by
  exact (BoundedContinuousFunction.mkOfCompact (F * realTorusMode k)).integrable _

/-- Extraction of one signed real Fourier coefficient in Haar normalization. -/
def fourierHaarReadout (k : MeanZeroMode) : ContinuousField →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x, F x * realTorusMode k x ∂normalizedTorusVolume
      map_add' := by
        intro F G
        simp_rw [ContinuousMap.add_apply, add_mul]
        exact integral_add (fourierPair_integrable F k) (fourierPair_integrable G k)
      map_smul' := by
        intro r F
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_assoc, integral_const_mul] }
    ‖realTorusMode k‖ (fun F => by
      apply (norm_integral_le_integral_norm _).trans
      rw [mul_comm ‖realTorusMode k‖ ‖F‖]
      simpa only [integral_const, measureReal_univ_eq_one, one_smul] using
        integral_mono (fourierPair_integrable F k).norm (integrable_const (‖F‖ * ‖realTorusMode k‖))
          (fun x => by
            rw [norm_mul]
            exact mul_le_mul (ContinuousMap.norm_coe_le_norm F x)
              (ContinuousMap.norm_coe_le_norm (realTorusMode k) x) (norm_nonneg _) (norm_nonneg _)))

theorem fourierHaarReadout_realTorusMode (k l : MeanZeroMode) :
    fourierHaarReadout k (realTorusMode l) = if k = l then 1 else 0 := by
  change (∫ x, realTorusMode l x * realTorusMode k x ∂normalizedTorusVolume) = _
  simp_rw [mul_comm (realTorusMode l _), real_mode_integral_orthonormal]

theorem cutoffRawPotential_fourierHaarReadout {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    fourierHaarReadout k (cutoffRawPotential Λ ℓ X a c) =
      if k ∈ retainedModes Λ then rawRegularization k * depthRescale ℓ X (k,(a,c)) else 0 := by
  classical
  simp only [cutoffRawPotential, rawPotentialTerm, map_sum, map_smul, smul_eq_mul,
    fourierHaarReadout_realTorusMode, mul_ite, mul_one, mul_zero, eq_comm (a := k),
    Finset.sum_ite_eq']

/-- The raw distribution is the cubic elliptic derivative of its Fourier
potential. Multiplying by that eigenvalue recovers each original elementary
coordinate in the normalized real Haar basis, almost surely for every depth. -/
theorem ae_fullRawPotential_fourierHaarReadout (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (ℓ : ℝ) (a : Fin 2) (c : Fin n) (k : MeanZeroMode),
      (1 + latticeFrequency k ^ 2) ^ 3 *
        fourierHaarReadout k (fullRawPotential ℓ X a c) = depthRescale ℓ X (k,(a,c)) := by
  filter_upwards [ae_rawPotential_uniform_limit n] with X h
  intro ℓ a c k
  have hlim := (fourierHaarReadout k).continuous.continuousAt.tendsto.comp (h ℓ a c)
  have hev : ∀ᶠ Λ in atTop, fourierHaarReadout k (cutoffRawPotential Λ ℓ X a c) =
      rawRegularization k * depthRescale ℓ X (k,(a,c)) := by
    filter_upwards [eventually_ge_atTop (latticeFrequency k)] with Λ hΛ
    rw [cutoffRawPotential_fourierHaarReadout, if_pos ((mem_retainedModes Λ k).2 hΛ)]
  have hc := tendsto_const_nhds.congr' (hev.mono (fun _ hEq => hEq.symm))
  rw [tendsto_nhds_unique hlim hc, rawRegularization, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : ((1 + latticeFrequency k ^ 2) ^ 3 : ℝ) ≠ 0), one_mul]

private def dualFrequency (k : TorusMode) : Cover :=
  (2 * π)⁻¹ • phaseVector k

private theorem dualFrequency_sub (k l : TorusMode) :
    dualFrequency (k-l) = dualFrequency k - dualFrequency l := by
  ext j
  simp [dualFrequency, phaseVector, Int.cast_sub, mul_sub]

private theorem dualFrequency_neg (k : TorusMode) : dualFrequency (-k) = -dualFrequency k := by
  ext j
  simp [dualFrequency, phaseVector]

private theorem norm_phaseVector (k : TorusMode) : ‖phaseVector k‖ = latticeFrequency k := by
  rw [EuclideanSpace.norm_eq, latticeFrequency]
  simp [phaseVector, sq_abs]

private theorem dualFrequency_separation {k l : TorusMode} (hkl : k ≠ l) :
    (2 * π)⁻¹ ≤ dist (dualFrequency k) (dualFrequency l) := by
  rw [dist_eq_norm, ← dualFrequency_sub, dualFrequency, norm_smul, norm_phaseVector,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 * π)⁻¹)]
  have hh := latticeHeight_le_latticeFrequency (k-l)
  have hp := Nat.pos_of_ne_zero (latticeHeight_ne_zero (sub_ne_zero.mpr hkl))
  have hi : (1 : ℝ) ≤ latticeFrequency (k-l) := (Nat.one_le_cast.mpr hp).trans hh
  exact le_mul_of_one_le_right (by positivity) hi

private def frequencyWindow (k : TorusMode) : ContDiffBump (dualFrequency k) where
  rIn := (2 * π)⁻¹ / 2
  rOut := (2 * π)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

private theorem frequencyWindow_value (k l : TorusMode) :
    frequencyWindow k (dualFrequency l) = if l = k then 1 else 0 := by
  classical
  by_cases h : l = k
  · subst l
    rw [if_pos rfl]
    exact (frequencyWindow k).one_of_mem_closedBall (Metric.mem_closedBall_self
      (frequencyWindow k).rIn_pos.le)
  · rw [if_neg h]
    exact (frequencyWindow k).zero_of_le_dist (dualFrequency_separation h)

private def selectedWindow (k : MeanZeroMode) : 𝓢(Cover, ℂ) := by
  let f (x : Cover) := ((sqrt 2 : ℝ) : ℂ) * phaseChooser k * (frequencyWindow k x : ℂ)
  have hc : HasCompactSupport f := by
    have hh : HasCompactSupport (fun x => (frequencyWindow k x : ℂ)) :=
      (frequencyWindow k).hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)
    exact hh.mul_left
  have hs : ContDiff ℝ ∞ f := contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (frequencyWindow k).contDiff)
  exact hc.toSchwartzMap hs

private theorem selectedWindow_value (k : MeanZeroMode) (l : TorusMode) :
    selectedWindow k (dualFrequency l) =
      if l = k.1 then ((sqrt 2 : ℝ) : ℂ) * phaseChooser k else 0 := by
  classical
  change ((sqrt 2 : ℝ) : ℂ) * phaseChooser k * ((frequencyWindow k (dualFrequency l) : ℝ) : ℂ) = _
  rw [frequencyWindow_value]
  split <;> simp

private def complexModeTest (k : MeanZeroMode) : 𝓢(Cover, ℂ) :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (selectedWindow k)

private def schwartzRealPart (f : 𝓢(Cover, ℂ)) : SchwartzTest where
  toFun := Complex.reCLM ∘ f
  smooth' := Complex.reCLM.contDiff.comp f.smooth'
  decay' q r := by
    obtain ⟨C,hC⟩ := f.decay' q r
    refine ⟨C, fun x => le_trans ?_ (hC x)⟩
    change ‖x‖ ^ q * ‖iteratedFDeriv ℝ r (Complex.reCLM ∘ f.toFun) x‖ ≤ _
    rw [Complex.reCLM.iteratedFDeriv_comp_left (i := r) f.smooth'.contDiffAt (by exact_mod_cast le_top)]
    gcongr
    have hRe : ‖Complex.reCLM‖ ≤ 1 := Complex.reCLM.opNorm_le_bound zero_le_one (fun z => by
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z)
    apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    exact mul_le_of_le_one_left (norm_nonneg _) hRe

/-- A real Schwartz test which extracts the specified normalized signed
mode from a raw distribution on the Euclidean cover. -/
def fourierSchwartzTest (k : MeanZeroMode) : SchwartzTest :=
  schwartzRealPart (complexModeTest k)

private theorem character_pairing (l : TorusMode) (f : 𝓢(Cover, ℂ)) :
    (∫ x, torusCharacter l (coverPoint x) * f x) = 𝓕 f (dualFrequency (-l)) := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  change torusCharacter l (coverPoint x) * f x =
    Complex.exp ((↑(-2 * π * ⟪x, dualFrequency (-l)⟫_ℝ) * Complex.I)) • f x
  have h : -2 * π * ⟪x, dualFrequency (-l)⟫_ℝ = phaseLinear l x := by
    rw [dualFrequency_neg, inner_neg_right, dualFrequency, inner_smul_right, phaseLinear]
    change -2 * π * -((2 * π)⁻¹ * ⟪x, phaseVector l⟫_ℝ) = ⟪phaseVector l, x⟫_ℝ
    rw [real_inner_comm (phaseVector l)]
    field_simp [pi_ne_zero]
  rw [h, character_cover_eq_exp, smul_eq_mul]

private theorem Fourier_complexModeTest (k : MeanZeroMode) :
    𝓕 (complexModeTest k) = selectedWindow k := by
  exact congrArg (fun f : 𝓢(Cover, ℂ) => (f : Cover → ℂ))
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (selectedWindow k))

private theorem character_pairing_integrable (l : TorusMode) (f : 𝓢(Cover, ℂ)) :
    Integrable (fun x => torusCharacter l (coverPoint x) * f x) volume := by
  refine (f.integrable (μ := volume)).norm.mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hcover : Continuous coverPoint := continuous_pi fun j => by
      change Continuous (fun x : Cover => ((x j : ℝ) : AddCircle ((2 : ℝ) * π)))
      exact continuous_quot_mk.comp (PiLp.continuous_apply 2 _ j)
    exact (((torusCharacter l).continuous.comp hcover).mul f.continuous).aestronglyMeasurable
  · rw [norm_mul, torusCharacter_point_norm, one_mul]

private theorem mode_pairing_complex (l : MeanZeroMode) (f : 𝓢(Cover, ℂ)) :
    (∫ x, (realTorusMode l (coverPoint x) : ℂ) * f x) =
      ((sqrt 2 : ℝ) : ℂ) / 2 * (phaseChooser l * 𝓕 f (dualFrequency (-l.1)) +
        conj (phaseChooser l) * 𝓕 f (dualFrequency l)) := by
  let f₁ (x : Cover) := phaseChooser l * (torusCharacter l (coverPoint x) * f x)
  let f₂ (x : Cover) := conj (phaseChooser l) * (torusCharacter (-l.1) (coverPoint x) * f x)
  have hf₁ : Integrable f₁ volume := (character_pairing_integrable l f).const_mul _
  have hf₂ : Integrable f₂ volume := (character_pairing_integrable (-l.1) f).const_mul _
  calc
    _ = ∫ x, ((sqrt 2 : ℝ) : ℂ) / 2 * (f₁ x + f₂ x) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      simp only [mode_expansion, f₁, f₂]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_add hf₁ hf₂]
      simp_rw [f₁, f₂, integral_const_mul, character_pairing, neg_neg]

private theorem mode_pairing_real (l k : MeanZeroMode) :
    modeTestPair l (fourierSchwartzTest k) =
      ((∫ x, (realTorusMode l (coverPoint x) : ℂ) * complexModeTest k x) : ℂ).re := by
  let f := complexModeTest k
  have hi : Integrable (fun x => (realTorusMode l (coverPoint x) : ℂ) * f x) volume := by
    let f₁ (x : Cover) := phaseChooser l * (torusCharacter l (coverPoint x) * f x)
    let f₂ (x : Cover) := conj (phaseChooser l) * (torusCharacter (-l.1) (coverPoint x) * f x)
    have hf₁ : Integrable f₁ volume := (character_pairing_integrable l f).const_mul _
    have hf₂ : Integrable f₂ volume := (character_pairing_integrable (-l.1) f).const_mul _
    apply ((hf₁.add hf₂).const_mul (((sqrt 2 : ℝ) : ℂ) / 2)).congr
    refine Eventually.of_forall fun x => ?_
    simp only [mode_expansion, f₁, f₂, Pi.add_apply]
    ring
  change (∫ x, realTorusMode l (coverPoint x) * (f x).re) = _
  rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp [Complex.mul_re]

private theorem mode_not_eq_negative (k : MeanZeroMode) : -k.1 ≠ k.1 := by
  intro h
  apply k.2
  ext j
  have hh := congrFun h j
  change -(k.1 j) = k.1 j at hh
  change k.1 j = 0
  omega

private theorem phaseChooser_opposite_re (k : MeanZeroMode) :
    (phaseChooser k * phaseChooser (negativeMode k)).re = 0 := by
  have h := congrArg Complex.re (phaseChooser_neg_cancel k)
  rw [← map_mul, Complex.add_re, Complex.conj_re, Complex.zero_re] at h
  linarith

/-- These Schwartz tests have exactly Kronecker pairings with the actual
Haar-normalized signed real sine and cosine modes. -/
theorem modeTestPair_fourierSchwartzTest (l k : MeanZeroMode) :
    modeTestPair l (fourierSchwartzTest k) = if l = k then 1 else 0 := by
  classical
  rw [mode_pairing_real, mode_pairing_complex, Fourier_complexModeTest,
    selectedWindow_value, selectedWindow_value]
  by_cases he : l = k
  · subst l
    simp only [if_neg (mode_not_eq_negative k), if_true, mul_zero, zero_add]
    have hh : (((sqrt 2 : ℝ) : ℂ) / 2) *
        (conj (phaseChooser k) * (((sqrt 2 : ℝ) : ℂ) * phaseChooser k)) = 1 := by
      calc
        _ = ((((sqrt 2 : ℝ) : ℂ)^2) / 2) * (phaseChooser k * conj (phaseChooser k)) := by ring
        _ = _ := by rw [phaseChooser_norm_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [hh, Complex.one_re]
  · have hn : l.1 ≠ k.1 := fun h => he (Subtype.ext h)
    rw [if_neg he, if_neg hn, mul_zero, add_zero]
    by_cases hOpp : -l.1 = k.1
    · have hl : l = negativeMode k := Subtype.ext (by simpa only [neg_neg] using congrArg Neg.neg hOpp)
      rw [if_pos hOpp, hl]
      have hh : (((sqrt 2 : ℝ) : ℂ) / 2) *
          (phaseChooser (negativeMode k) * (((sqrt 2 : ℝ) : ℂ) * phaseChooser k)) =
          phaseChooser k * phaseChooser (negativeMode k) := by
        calc
          _ = ((((sqrt 2 : ℝ) : ℂ)^2) / 2) * (phaseChooser k * phaseChooser (negativeMode k)) := by ring
          _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
      rw [hh, phaseChooser_opposite_re]
    · simp [hOpp]

/-- Each elementary readout is a literal Schwartz evaluation of the finite
raw distribution, with the original spherical cutoff and no normalization change. -/
theorem cutoffRawDistribution_fourierSchwartzTest {n : ℕ} (Λ ℓ : ℝ)
    (X : ModeSlot n → ℝ) (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    cutoffRawDistribution Λ ℓ X a c (fourierSchwartzTest k) =
      if k ∈ retainedModes Λ then depthRescale ℓ X (k,(a,c)) else 0 := by
  classical
  rw [cutoffRawDistribution_eq_mode_pair_sum]
  simp only [modeTestPair_fourierSchwartzTest, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

/-- Almost surely for all depths and all signed elementary modes, the raw
Gaussian distribution recovers the original source readout by literal Schwartz evaluation. -/
theorem ae_rawSample_fourierSchwartzTest (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (ℓ : ℝ) (a : Fin 2) (c : Fin n) (k : MeanZeroMode),
      UV.ResumeCurvatureRawLaw.rawSample ℓ a c X (fourierSchwartzTest k) =
        depthRescale ℓ X (k,(a,c)) := by
  classical
  filter_upwards [ae_regularized_coordinates_summable n,
    ae_fullRawDistribution_eq_mode_pair_tsum n] with X hGood hRaw
  intro ℓ a c k
  have hr : UV.ResumeCurvatureRawLaw.rawSample ℓ a c X =
      if Summable (fun i : ModeSlot n => rawRegularization i.1 * |depthRescale ℓ X i|) then
        fullRawDistribution ℓ X a c else 0 := rfl
  rw [hr, if_pos (hGood ℓ), (hRaw ℓ a c (fourierSchwartzTest k)).2]
  simp only [modeTestPair_fourierSchwartzTest, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    simp [hj]

local instance : MeasurableSpace RawDistribution := cylinderSpace

/-- The full signed coordinate family obtained by evaluating each actual
raw field on the dual Schwartz test. -/
def fieldFourierReadout {n : ℕ} (F : RawFields n) (i : ModeSlot n) : ℝ :=
  F i.2.1 i.2.2 (fourierSchwartzTest i.1)

theorem fieldFourierReadout_measurable (n : ℕ) : Measurable (fieldFourierReadout (n := n)) := by
  apply measurable_pi_lambda
  intro i
  refine (show Measurable (fun F : RawDistribution => F (fourierSchwartzTest i.1)) from ?_).comp
    ((measurable_pi_apply i.2.2).comp (measurable_pi_apply i.2.1))
  exact (measurable_pi_apply (fourierSchwartzTest i.1)).comp
    (Measurable.of_comap_le le_rfl : Measurable (fun F : RawDistribution => fun φ : SchwartzTest => F φ))

private theorem preparation_fourier_readout_ae {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] :
    fieldFourierReadout (n := n) ∘ jointRawReadout =ᵐ[preparationMeasure n μ] elementarySourceMap := by
  unfold preparationMeasure
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((fieldFourierReadout_measurable n).comp (jointRawReadout_measurable n))
    (depthRescale_jointly_measurable n))).2
  exact ae_of_all _ fun ℓ => (ae_rawSample_fourierSchwartzTest n).mono fun X h =>
    funext fun i => h ℓ i.2.1 i.2.2 i.1

/-- The normalized raw fields and the full signed elementary-coordinate law
are related by the exact measurable Fourier readout. -/
theorem interactingRawFieldLaw_fourier_map {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ) :
    (interactingRawFieldLaw B μ g).map fieldFourierReadout = elementarySourceLaw B μ g := by
  rw [interactingRawFieldLaw, elementarySourceLaw, Measure.map_map
    (fieldFourierReadout_measurable n) (jointRawReadout_measurable n)]
  exact Measure.map_congr ((preparation_fourier_readout_ae μ).filter_mono
    (withDensity_absolutelyContinuous (preparationMeasure n μ) _).ae_le)

/-- Spherical finite raw distribution readouts use the same cylindrical
measurable space as the unrestricted raw fields. -/
def cutoffJointRawReadout {n : ℕ} (Λ : ℝ) (p : Preparation n) : RawFields n :=
  fun a c => cutoffRawDistribution Λ p.1 p.2 a c

theorem cutoffJointRawReadout_measurable (n : ℕ) (Λ : ℝ) :
    Measurable (cutoffJointRawReadout (n := n) Λ) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro c
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun p : Preparation n => cutoffRawDistribution Λ p.1 p.2 a c)
    cylinderSpace ≤ _
  rw [cylinderSpace, MeasurableSpace.comap_comp]
  exact (measurable_pi_lambda _ fun φ => cutoffRawDistribution_readout_measurable Λ a c φ).comap_le

def cutoffInteractingRawFieldLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ)
    (g Λ : ℝ) : Measure (RawFields n) :=
  (cutoffGibbsMeasure B μ g Λ).map (cutoffJointRawReadout Λ)

theorem cutoffInteractingRawFieldLaw_probability {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) :
    IsProbabilityMeasure (cutoffInteractingRawFieldLaw B μ g Λ) := by
  letI := cutoffGibbsMeasure_probability B μ hpos hg Λ
  exact Measure.isProbabilityMeasure_map (cutoffJointRawReadout_measurable n Λ).aemeasurable

theorem cutoffInteractingRawFieldLaw_fourier_map {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) :
    (cutoffInteractingRawFieldLaw B μ g Λ).map fieldFourierReadout =
      cutoffElementarySourceLaw B μ g Λ := by
  rw [cutoffInteractingRawFieldLaw, cutoffElementarySourceLaw, Measure.map_map
    (fieldFourierReadout_measurable n) (cutoffJointRawReadout_measurable n Λ)]
  apply congrArg (fun f => Measure.map f (cutoffGibbsMeasure B μ g Λ))
  funext p i
  change cutoffRawDistribution Λ p.1 p.2 i.2.1 i.2.2 (fourierSchwartzTest i.1) = _
  simp only [cutoffRawDistribution_fourierSchwartzTest, mem_retainedModes, cutoffElementarySourceMap]

/-- The continuum marginal on any finite selection of elementary Fourier
components is the marginal of the same raw distribution-valued field. -/
theorem interactingRawFieldLaw_finite_fourier_marginal {n : ℕ}
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (g : ℝ) (S : Finset (ModeSlot n)) :
    (interactingRawFieldLaw B μ g).map (S.restrict ∘ fieldFourierReadout) =
      finiteModeLaw B μ g S := by
  rw [← Measure.map_map (Finset.measurable_restrict S) (fieldFourierReadout_measurable n),
    interactingRawFieldLaw_fourier_map, elementarySourceLaw_finite_marginal]

/-- The finite-cutoff analog uses literal evaluations of the same fixed
Schwartz tests on the truncated raw distributions. -/
theorem cutoffInteractingRawFieldLaw_finite_fourier_marginal {n : ℕ}
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ)
    (g Λ : ℝ) (S : Finset (ModeSlot n)) :
    (cutoffInteractingRawFieldLaw B μ g Λ).map (S.restrict ∘ fieldFourierReadout) =
      cutoffModeLaw B μ g Λ S := by
  rw [← Measure.map_map (Finset.measurable_restrict S) (fieldFourierReadout_measurable n),
    cutoffInteractingRawFieldLaw_fourier_map, cutoffElementarySourceLaw_finite_marginal]

end UV.ContinueCurvatureModes

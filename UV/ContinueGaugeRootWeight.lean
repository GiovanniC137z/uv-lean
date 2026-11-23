import UV.ContinueOpeningGaussianWaves

/-! The change from a positive density to Lebesgue coordinates in the
magnetic oscillator is an onto isometry of the full L² spaces. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace UV.RootMagnetic

abbrev LebesgueFiber := Lp ℂ 2 (volume : Measure ℝ)

def squaredWeightLaw (w : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (w x ^ 2))

private theorem volume_ac_weight {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    (volume : Measure ℝ) ≪ squaredWeightLaw w :=
  withDensity_absolutelyContinuous' ((hw.pow_const 2).ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (hp x) _))

private theorem weight_ac_volume (w : ℝ → ℝ) : squaredWeightLaw w ≪ volume :=
  withDensity_absolutelyContinuous _ _

private theorem weighted_square_integral {w : ℝ → ℝ} (hw : Measurable w) (f : ℝ → ℂ) :
    (∫ x, ‖f x‖ ^ 2 ∂squaredWeightLaw w) = ∫ x, w x ^ 2 * ‖f x‖ ^ 2 := by
  rw [squaredWeightLaw, integral_withDensity_eq_integral_toReal_smul
    (hw.pow_const 2).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

private theorem memLp_weighted {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ x, 0 < w x)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    MemLp f 2 (squaredWeightLaw w) ↔ MemLp (fun x => (w x : ℂ) * f x) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => (w x : ℂ) * f x) (volume : Measure ℝ) :=
    (hw.complex_ofReal.aestronglyMeasurable.mul hf)
  rw [memLp_two_iff_integrable_sq_norm (hf.mono_ac (weight_ac_volume w)), memLp_two_iff_integrable_sq_norm hm]
  rw [squaredWeightLaw, integrable_withDensity_iff_integrable_smul'
    (hw.pow_const 2).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h (x : ℝ) : ((ENNReal.ofReal (w x ^ 2)).toReal : ℝ) • ‖f x‖ ^ 2 =
      ‖(w x : ℂ) * f x‖ ^ 2 := by
    rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hp x).le, mul_pow]
  simp_rw [h]

theorem integral_norm_sq_lp {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : Lp ℂ 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (L2.inner_def (𝕜 := ℂ) f f)
  change RCLike.re (⟪f, f⟫_ℂ) = RCLike.re (∫ x, ⟪f x, f x⟫_ℂ ∂μ) at h
  rw [← integral_re (L2.integrable_inner f f)] at h
  simpa only [← @norm_sq_eq_re_inner ℂ] using h.symm

private def weightedFiberMap {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (f : Lp ℂ 2 (squaredWeightLaw w)) : LebesgueFiber :=
  ((memLp_weighted hw hp ((Lp.stronglyMeasurable f).aestronglyMeasurable)).mp (Lp.memLp f)).toLp _

private theorem weightedFiberMap_ae {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (f : Lp ℂ 2 (squaredWeightLaw w)) :
    ⇑(weightedFiberMap hw hp f) =ᵐ[volume] fun x => (w x : ℂ) * f x :=
  MemLp.coeFn_toLp _

theorem squared_weight_unitary {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    ∃ U : Lp ℂ 2 (squaredWeightLaw w) ≃ₗᵢ[ℂ] LebesgueFiber,
      ∀ f, ⇑(U f) =ᵐ[volume] fun x => (w x : ℂ) * f x := by
  let L : Lp ℂ 2 (squaredWeightLaw w) →ₗᵢ[ℂ] LebesgueFiber := {
    toFun := weightedFiberMap hw hp
    map_add' := fun f g => by
      apply Lp.ext
      filter_upwards [weightedFiberMap_ae hw hp (f+g), weightedFiberMap_ae hw hp f,
        weightedFiberMap_ae hw hp g, (volume_ac_weight hw hp).ae_le (Lp.coeFn_add f g),
        Lp.coeFn_add (weightedFiberMap hw hp f) (weightedFiberMap hw hp g)] with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁, h₄, h₅, Pi.add_apply, h₂, h₃, mul_add]
    map_smul' := fun z f => by
      apply Lp.ext
      filter_upwards [weightedFiberMap_ae hw hp (z • f), weightedFiberMap_ae hw hp f,
        (volume_ac_weight hw hp).ae_le (Lp.coeFn_smul z f),
        Lp.coeFn_smul z (weightedFiberMap hw hp f)] with x h₁ h₂ h₃ h₄
      change weightedFiberMap hw hp (z • f) x = (z • weightedFiberMap hw hp f) x
      simp only [h₁, h₃, h₄, Pi.smul_apply, h₂, smul_eq_mul, mul_left_comm]
    norm_map' := fun f => by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← integral_norm_sq_lp, ← integral_norm_sq_lp, weighted_square_integral hw f]
      apply integral_congr_ae
      filter_upwards [weightedFiberMap_ae hw hp f] with x hx
      change ‖weightedFiberMap hw hp f x‖ ^ 2 = _
      rw [hx, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp x).le, mul_pow] }
  have hsurj : Function.Surjective L := by
    intro g
    let f (x : ℝ) := (w x : ℂ)⁻¹ * g x
    have hfM : AEStronglyMeasurable f volume := hw.complex_ofReal.inv.aestronglyMeasurable.mul
      (Lp.stronglyMeasurable g).aestronglyMeasurable
    have hcancel (x : ℝ) : (w x : ℂ) * f x = g x := by
      dsimp [f]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hp x).ne'), one_mul]
    have hf : MemLp f 2 (squaredWeightLaw w) :=
      (memLp_weighted hw hp hfM).2 ((memLp_congr_ae (Eventually.of_forall hcancel)).mpr (Lp.memLp g))
    refine ⟨hf.toLp f, Lp.ext ?_⟩
    filter_upwards [weightedFiberMap_ae hw hp (hf.toLp f),
      (volume_ac_weight hw hp).ae_le hf.coeFn_toLp] with x hx hy
    change weightedFiberMap hw hp (hf.toLp f) x = g x
    rw [hx, hy, hcancel]
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, weightedFiberMap_ae hw hp⟩

end UV.RootMagnetic

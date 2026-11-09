import UV.SourceCovariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import UV.UnboundedSourceResolvent

/-! Maximal spectral multiplication operators on genuine L2 spaces.
The domain is exactly square integrability after multiplication; no
operator identity or adjoint-domain equality is included as data. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate ENNReal

namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def sourceL2MultiplierDomain (w : X → ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => w x * f x) 2 μ}
  zero_mem' := by
    refine MemLp.ae_eq ?_ (MemLp.zero' : MemLp (fun _ : X => (0 : ℂ)) 2 μ)
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simp only [Pi.zero_apply] at hx
    rw [hx, mul_zero]
  add_mem' := by
    intro f g hf hg
    refine MemLp.ae_eq ?_ (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply, hx, mul_add]
  smul_mem' := by
    intro c f hf
    refine MemLp.ae_eq ?_ (hf.const_smul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    ring

def sourceL2Multiplier (w : X → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := sourceL2MultiplierDomain μ w
  toFun :=
    { toFun := fun f => f.property.toLp (fun x => w x * f.val x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (f+g).property,
          Lp.coeFn_add (f.property.toLp _) (g.property.toLp _),
          MemLp.coeFn_toLp f.property, MemLp.coeFn_toLp g.property,
          Lp.coeFn_add f.val g.val] with x hfg hs hf hg ha
        simp only [Submodule.coe_add] at hfg ⊢
        rw [hfg, hs]
        simp only [Pi.add_apply, ha, hf, hg, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (c • f).property,
          Lp.coeFn_smul c (f.property.toLp _), MemLp.coeFn_toLp f.property,
          Lp.coeFn_smul c f.val] with x hcf hs hf ha
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at hcf hs ha ⊢
        rw [hcf, ha, hs, hf]
        ring }

theorem sourceL2Multiplier_coe (w : X → ℂ) (f : (sourceL2Multiplier μ w).domain) :
    (sourceL2Multiplier μ w f : X → ℂ) =ᵐ[μ] fun x => w x * f.val x :=
  MemLp.coeFn_toLp f.property

theorem sourceL2Multiplier_mem_iff (w : X → ℂ) (f : Lp ℂ 2 μ) :
    f ∈ (sourceL2Multiplier μ w).domain ↔ MemLp (fun x => w x * f x) 2 μ := Iff.rfl

def sourceL2Cut (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  MemLp.toLp (s.indicator (f : X → ℂ)) ((Lp.memLp f).indicator hs)

set_option maxHeartbeats 800000 in
theorem sourceL2Cut_coe (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    (sourceL2Cut μ s hs f : X → ℂ) =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp (f := s.indicator (f : X → ℂ)) ((Lp.memLp f).indicator hs)

theorem sourceL2Cut_mem_multiplier {w : X → ℂ} (hw : AEStronglyMeasurable w μ)
    (s : Set X) (hs : MeasurableSet s) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ s, ‖w x‖ ≤ C) (f : Lp ℂ 2 μ) :
    sourceL2Cut μ s hs f ∈ (sourceL2Multiplier μ w).domain := by
  change MemLp (fun x => w x * sourceL2Cut μ s hs f x) 2 μ
  apply (Lp.memLp f).of_le_mul (c := C)
    (hw.mul (Lp.aestronglyMeasurable _))
  filter_upwards [sourceL2Cut_coe μ s hs f] with x hx
  change ‖w x * sourceL2Cut μ s hs f x‖ ≤ C * ‖f x‖
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x hxs) (norm_nonneg _)
  · simp [indicator_of_notMem hxs, mul_nonneg hC (norm_nonneg (f x))]

/-- Exhausting measurable spectral cuts converge in the actual L2 norm. -/
theorem sourceL2Cut_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, x ∈ s n) (f : Lp ℂ 2 μ) :
    Tendsto (fun n => sourceL2Cut μ (s n) (hs n) f) atTop (𝓝 f) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => (s n).indicator f x-f x) μ :=
    ((Lp.memLp f).indicator (hs n)).aestronglyMeasurable.sub (Lp.aestronglyMeasurable f)
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ∞ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp f).eLpNorm_lt_top).ne
  have hb (n : ℕ) : (fun x => ‖(s n).indicator f x-f x‖ₑ ^ (2 : ℝ)) ≤ᵐ[μ]
      (fun x => ‖f x‖ₑ ^ (2 : ℝ)) := by
    filter_upwards with x
    by_cases hx : x ∈ s n <;> simp [hx]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖(s n).indicator f x-f x‖ₑ ^ (2 : ℝ))
      atTop (𝓝 0) := by
    filter_upwards [hcover] with x hx
    obtain ⟨N, hN⟩ := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [hN n hn]
  have hI := tendsto_lintegral_of_dominated_convergence' _
    (fun n => (hm n).enorm.pow_const (2 : ℝ)) hb hfin hlim
  simp only [lintegral_zero] at hI
  have hnorm : Tendsto (fun n => eLpNorm (fun x => (s n).indicator f x-f x) 2 μ)
      atTop (𝓝 0) := by
    simp only [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat]
    convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp hI using 1
    norm_num
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).mpr
  apply hnorm.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [sourceL2Cut_coe μ (s n) (hs n) f] with x hx
  simp only [Pi.sub_apply, hx]

/-- A locally bounded measurable multiplier has a dense maximal domain. -/
theorem sourceL2Multiplier_dense_domain {w : X → ℂ} (hw : Measurable w) :
    Dense ((sourceL2Multiplier μ w).domain : Set (Lp ℂ 2 μ)) := by
  intro f
  let s : ℕ → Set X := fun n => {x | ‖w x‖ ≤ n}
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_le hw.norm measurable_const
  have hcover : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, x ∈ s n := by
    filter_upwards with x
    obtain ⟨N, hN⟩ := exists_nat_ge ‖w x‖
    exact ⟨N, fun n hn => hN.trans (Nat.cast_le.mpr hn)⟩
  have hmem (n : ℕ) : sourceL2Cut μ (s n) (hs n) f ∈ (sourceL2Multiplier μ w).domain :=
    sourceL2Cut_mem_multiplier μ hw.aestronglyMeasurable (s n) (hs n)
      (Nat.cast_nonneg n) (fun _ hx => hx) f
  exact mem_closure_of_tendsto (sourceL2Cut_tendsto μ s hs hcover f) (Eventually.of_forall hmem)

/-- Real maximal multiplication is symmetric on its actual domain. -/
theorem sourceL2Multiplier_real_symmetric (w : X → ℝ) :
    (sourceL2Multiplier μ (fun x => (w x : ℂ))).IsFormalAdjoint
      (sourceL2Multiplier μ (fun x => (w x : ℂ))) := by
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceL2Multiplier_coe μ (fun x => (w x : ℂ)) f,
    sourceL2Multiplier_coe μ (fun x => (w x : ℂ)) g] with x hf hg
  rw [hf, hg]
  change inner ℂ ((w x : ℂ) • f.val x) (g.val x) =
    inner ℂ (f.val x) ((w x : ℂ) • g.val x)
  simp
  ring

theorem source_real_shift_bounds (u : ℝ) (c : ℂ) (hcRe : c.re = 0) (hcIm : |c.im| = 1) :
    (u : ℂ)+c ≠ 0 ∧ ‖((u : ℂ)+c)⁻¹‖ ≤ 1 ∧
      ‖(u : ℂ)*((u : ℂ)+c)⁻¹‖ ≤ 1 := by
  have him : 1 ≤ ‖(u : ℂ)+c‖ := by
    simpa [hcIm] using Complex.abs_im_le_norm ((u : ℂ)+c)
  have hn : 0 < ‖(u : ℂ)+c‖ := lt_of_lt_of_le zero_lt_one him
  have hne : (u : ℂ)+c ≠ 0 := norm_pos_iff.mp hn
  have hreal : ‖(u : ℂ)‖ ≤ ‖(u : ℂ)+c‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, hcRe] using Complex.abs_re_le_norm ((u : ℂ)+c)
  refine ⟨hne, ?_, ?_⟩
  · rw [norm_inv]
    exact inv_le_one_of_one_le₀ him
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact (div_le_one hn).mpr hreal

/-- The two imaginary resolvents are explicitly onto, using bounded
reciprocal multipliers and their bounded products with the real symbol. -/
theorem sourceL2Multiplier_shift_surjective (w : X → ℝ) (hw : Measurable w)
    (c : ℂ) (hcRe : c.re = 0) (hcIm : |c.im| = 1) :
    Function.Surjective (fun f : (sourceL2Multiplier μ (fun x => (w x : ℂ))).domain =>
      sourceL2Multiplier μ (fun x => (w x : ℂ)) f + c • (f.val : Lp ℂ 2 μ)) := by
  intro g
  let q : X → ℂ := fun x => ((w x : ℂ)+c)⁻¹
  have hwc : Measurable (fun x => (w x : ℂ)) := Complex.measurable_ofReal.comp hw
  have hq : Measurable q := (hwc.add measurable_const).inv
  have hqLp : MemLp (fun x => q x*g x) 2 μ := by
    apply (Lp.memLp g).of_le_mul (c := (1 : ℝ))
      (hq.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    filter_upwards with x
    change ‖q x*g x‖ ≤ 1*‖g x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (source_real_shift_bounds (w x) c hcRe hcIm).2.1 (norm_nonneg _)
  let f : Lp ℂ 2 μ := hqLp.toLp (fun x => q x*g x)
  have hwqLp : MemLp (fun x => ((w x : ℂ)*q x)*g x) 2 μ := by
    apply (Lp.memLp g).of_le_mul (c := (1 : ℝ))
      ((hwc.mul hq).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    filter_upwards with x
    change ‖((w x : ℂ)*q x)*g x‖ ≤ 1*‖g x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (source_real_shift_bounds (w x) c hcRe hcIm).2.2 (norm_nonneg _)
  have hdom : f ∈ (sourceL2Multiplier μ (fun x => (w x : ℂ))).domain := by
    refine MemLp.ae_eq ?_ hwqLp
    filter_upwards [MemLp.coeFn_toLp hqLp] with x hx
    change ((w x : ℂ)*q x)*g x = (w x : ℂ)*f x
    rw [show f x = q x*g x from hx]
    ring
  refine ⟨⟨f,hdom⟩, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (sourceL2Multiplier μ (fun x => (w x : ℂ)) ⟨f,hdom⟩) (c • f),
    sourceL2Multiplier_coe μ (fun x => (w x : ℂ)) ⟨f,hdom⟩,
    Lp.coeFn_smul c f, MemLp.coeFn_toLp hqLp] with x ha ht hs hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hs
  change (sourceL2Multiplier μ (fun x => (w x : ℂ)) ⟨f,hdom⟩ + c • f) x = g x
  rw [ha, ht, hs]
  change (w x : ℂ)*f x+c*f x = g x
  rw [show f x=q x*g x from hf]
  dsimp only [q]
  have hne := (source_real_shift_bounds (w x) c hcRe hcIm).1
  field_simp [hne]

/-- Every measurable real spectral multiplier is genuinely self-adjoint on
its maximal square-integrability domain, including unbounded symbols. -/
theorem sourceL2Multiplier_real_selfAdjoint (w : X → ℝ) (hw : Measurable w) :
    IsSelfAdjoint (sourceL2Multiplier μ (fun x => (w x : ℂ))) := by
  apply unbounded_selfAdjoint_of_imaginary_resolvents'
    (sourceL2Multiplier μ (fun x => (w x : ℂ))) (sourceL2Multiplier_real_symmetric μ w)
  · exact sourceL2Multiplier_shift_surjective μ w hw Complex.I (by simp) (by simp)
  · simpa only [neg_smul, sub_eq_add_neg] using
      sourceL2Multiplier_shift_surjective μ w hw (-Complex.I) (by simp) (by simp)

end UV

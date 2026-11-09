import UV.UnboundedSource
import Mathlib.Analysis.Normed.Group.Bounded

/-! The dense common reducing spectral cut core in an arbitrary-measure
joint multiplier representation. Positive spectral coordinates may approach
zero or infinity; no uniform lower or upper spectral gap is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace UV

variable {X : Type*} [MeasurableSpace X]

def sourceJointSpectralCut (F K : X → ℝ) (n : ℕ) : Set X :=
  {x | ((n : ℝ)+1)⁻¹ ≤ F x ∧ F x ≤ (n : ℝ)+1 ∧
    ((n : ℝ)+1)⁻¹ ≤ K x ∧ K x ≤ (n : ℝ)+1}

theorem sourceJointSpectralCut_measurable {F K : X → ℝ} (hF : Measurable F)
    (hK : Measurable K) (n : ℕ) : MeasurableSet (sourceJointSpectralCut F K n) :=
  (measurableSet_le measurable_const hF).inter ((measurableSet_le hF measurable_const).inter
    ((measurableSet_le measurable_const hK).inter (measurableSet_le hK measurable_const)))

omit [MeasurableSpace X] in
theorem sourceJointSpectralCut_mono (F K : X → ℝ) : Monotone (sourceJointSpectralCut F K) := by
  intro n m hnm x hx
  have hle : (n : ℝ)+1 ≤ (m : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hinv : ((m : ℝ)+1)⁻¹ ≤ ((n : ℝ)+1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)+1) hle
  exact ⟨hinv.trans hx.1, hx.2.1.trans hle, hinv.trans hx.2.2.1, hx.2.2.2.trans hle⟩

omit [MeasurableSpace X] in
theorem sourceJointSpectralCut_eventually_mem {F K : X → ℝ} {x : X}
    (hF : 0 < F x) (hK : 0 < K x) :
    ∃ N : ℕ, ∀ n ≥ N, x ∈ sourceJointSpectralCut F K n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (max (F x) (K x)) (max (F x)⁻¹ (K x)⁻¹))
  have hupperF : F x ≤ (N : ℝ)+1 := (le_max_left _ _).trans ((le_max_left _ _).trans hN) |>.trans (by linarith)
  have hupperK : K x ≤ (N : ℝ)+1 := (le_max_right _ _).trans ((le_max_left _ _).trans hN) |>.trans (by linarith)
  have hinvF : (F x)⁻¹ ≤ (N : ℝ)+1 := (le_max_left _ _).trans ((le_max_right _ _).trans hN) |>.trans (by linarith)
  have hinvK : (K x)⁻¹ ≤ (N : ℝ)+1 := (le_max_right _ _).trans ((le_max_right _ _).trans hN) |>.trans (by linarith)
  have hpos : 0 < (N : ℝ)+1 := by positivity
  refine ⟨N, fun n hn => sourceJointSpectralCut_mono F K hn ?_⟩
  exact ⟨(inv_le_comm₀ hpos hF).mpr hinvF, hupperF,
    (inv_le_comm₀ hpos hK).mpr hinvK, hupperK⟩

variable (μ : Measure X)

def sourceJointCore (F K : X → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∃ n : ℕ, ∀ᵐ x ∂μ, x ∉ sourceJointSpectralCut F K n → f x = 0}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    intro _
    exact hx
  add_mem' := by
    intro f g hf hg
    obtain ⟨n,hn⟩ := hf
    obtain ⟨m,hm⟩ := hg
    refine ⟨max n m, ?_⟩
    filter_upwards [hn,hm,Lp.coeFn_add f g] with x hxf hxg ha
    intro hx
    have hxn : x ∉ sourceJointSpectralCut F K n := fun h => hx (sourceJointSpectralCut_mono F K (le_max_left _ _) h)
    have hxm : x ∉ sourceJointSpectralCut F K m := fun h => hx (sourceJointSpectralCut_mono F K (le_max_right _ _) h)
    simpa only [Pi.add_apply, hxf hxn, hxg hxm, add_zero] using ha
  smul_mem' := by
    intro c f hf
    obtain ⟨n,hn⟩ := hf
    refine ⟨n, ?_⟩
    filter_upwards [hn,Lp.coeFn_smul c f] with x hxf ha
    intro hx
    simpa only [Pi.smul_apply, hxf hx, smul_zero] using ha

theorem sourceJointCore_cut_mem {F K : X → ℝ} (hF : Measurable F) (hK : Measurable K)
    (n : ℕ) (f : Lp ℂ 2 μ) :
    sourceL2Cut μ (sourceJointSpectralCut F K n)
      (sourceJointSpectralCut_measurable hF hK n) f ∈ sourceJointCore μ F K := by
  refine ⟨n, ?_⟩
  filter_upwards [sourceL2Cut_coe μ (sourceJointSpectralCut F K n)
    (sourceJointSpectralCut_measurable hF hK n) f] with x hx
  intro hn
  simpa only [indicator_of_notMem hn] using hx

/-- The actual union of joint bounded cuts is dense, without a positive gap
and without boundedness of either original spectral coordinate. -/
theorem sourceJointCore_dense {F K : X → ℝ} (hF : Measurable F) (hK : Measurable K)
    (hposF : ∀ᵐ x ∂μ, 0 < F x) (hposK : ∀ᵐ x ∂μ, 0 < K x) :
    Dense (sourceJointCore μ F K : Set (Lp ℂ 2 μ)) := by
  intro f
  have hcover : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, x ∈ sourceJointSpectralCut F K n := by
    filter_upwards [hposF,hposK] with x hxF hxK
    exact sourceJointSpectralCut_eventually_mem hxF hxK
  exact mem_closure_of_tendsto
    (sourceL2Cut_tendsto μ (sourceJointSpectralCut F K)
      (sourceJointSpectralCut_measurable hF hK) hcover f)
    (Eventually.of_forall (fun n => sourceJointCore_cut_mem μ hF hK n f))

def sourceCoreAdmissible (F K : X → ℝ) (w : X → ℂ) : Prop :=
  Measurable w ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ sourceJointSpectralCut F K n, ‖w x‖ ≤ C

theorem sourceJointCore_mem_multiplier {F K : X → ℝ} {w : X → ℂ}
    (hw : sourceCoreAdmissible F K w) {f : Lp ℂ 2 μ} (hf : f ∈ sourceJointCore μ F K) :
    f ∈ (sourceL2Multiplier μ w).domain := by
  obtain ⟨n,hn⟩ := hf
  obtain ⟨C,hC⟩ := hw.2 n
  apply (Lp.memLp f).of_le_mul (c := C)
    (hw.1.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hn] with x hx
  change ‖w x*f x‖ ≤ C*‖f x‖
  by_cases hxs : x ∈ sourceJointSpectralCut F K n
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x hxs) (norm_nonneg _)
  · simp [hx hxs]

theorem sourceJointCore_multiplier_mem {F K : X → ℝ} {w : X → ℂ}
    (hw : sourceCoreAdmissible F K w) {f : Lp ℂ 2 μ} (hf : f ∈ sourceJointCore μ F K) :
    sourceL2Multiplier μ w ⟨f, sourceJointCore_mem_multiplier μ hw hf⟩ ∈ sourceJointCore μ F K := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n, ?_⟩
  filter_upwards [hn, sourceL2Multiplier_coe μ w
    ⟨f, sourceJointCore_mem_multiplier μ hw ⟨n,hn⟩⟩] with x hx ht
  intro hxs
  simpa only [hx hxs, mul_zero] using ht

/-- Every continuous real function of the two positive spectral coordinates
is bounded on each joint compact cut. The bound is derived by compactness. -/
theorem sourceCoreAdmissible_of_real_continuousOn {F K : X → ℝ}
    (hF : Measurable F) (hK : Measurable K) {φ : ℝ × ℝ → ℝ} (hm : Measurable φ)
    (hc : ContinuousOn φ (Ioi 0 ×ˢ Ioi 0)) :
    sourceCoreAdmissible F K (fun x => (φ (F x,K x) : ℂ)) := by
  refine ⟨Complex.measurable_ofReal.comp (hm.comp (hF.prodMk hK)), fun n => ?_⟩
  let N : ℝ := (n : ℝ)+1
  have hN : 0 < N := by dsimp [N]; positivity
  have hsub : Icc N⁻¹ N ×ˢ Icc N⁻¹ N ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
    fun p hp => ⟨(inv_pos.mpr hN).trans_le hp.1.1, (inv_pos.mpr hN).trans_le hp.2.1⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨C, fun x hx => ?_⟩
  have hp : (F x,K x) ∈ Icc N⁻¹ N ×ˢ Icc N⁻¹ N :=
    ⟨⟨hx.1,hx.2.1⟩,hx.2.2⟩
  simpa only [Complex.norm_real] using hC (F x,K x) hp

/-- Restriction of the actual maximal operator to the common invariant core. -/
def sourceCoreMul {F K : X → ℝ} {w : X → ℂ} (hw : sourceCoreAdmissible F K w) :
    sourceJointCore μ F K →ₗ[ℂ] sourceJointCore μ F K where
  toFun f := ⟨sourceL2Multiplier μ w ⟨f.val,sourceJointCore_mem_multiplier μ hw f.property⟩,
    sourceJointCore_multiplier_mem μ hw f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact (sourceL2Multiplier μ w).map_add
      ⟨f.val,sourceJointCore_mem_multiplier μ hw f.property⟩
      ⟨g.val,sourceJointCore_mem_multiplier μ hw g.property⟩
  map_smul' c f := by
    apply Subtype.ext
    exact (sourceL2Multiplier μ w).map_smul c
      ⟨f.val,sourceJointCore_mem_multiplier μ hw f.property⟩

theorem sourceCoreMul_coe {F K : X → ℝ} {w : X → ℂ} (hw : sourceCoreAdmissible F K w)
    (f : sourceJointCore μ F K) :
    ((sourceCoreMul μ hw f : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => w x*f.val x :=
  sourceL2Multiplier_coe μ w ⟨f.val,sourceJointCore_mem_multiplier μ hw f.property⟩

/-- Composition identities are checked on the actual maximal multiplier
outputs; all intermediate domain and core obligations have been proved. -/
theorem sourceCoreMul_comp_eq {F K : X → ℝ} {u v w : X → ℂ}
    (hu : sourceCoreAdmissible F K u) (hv : sourceCoreAdmissible F K v)
    (hw : sourceCoreAdmissible F K w) (he : ∀ᵐ x ∂μ, u x*v x=w x)
    (f : sourceJointCore μ F K) : sourceCoreMul μ hu (sourceCoreMul μ hv f) = sourceCoreMul μ hw f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sourceCoreMul_coe μ hu (sourceCoreMul μ hv f), sourceCoreMul_coe μ hv f,
    sourceCoreMul_coe μ hw f, he] with x hu' hv' hw' he'
  rw [hu', hw', hv', ← mul_assoc, he']

end UV

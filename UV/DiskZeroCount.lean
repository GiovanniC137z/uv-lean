import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Perfect

/-! Disk argument principle from actual analytic functions. The zero count is
the finite sum of the existing meromorphic divisor; its contour formula is
proved from finite factorization, the product rule, and Cauchy's formula. -/

noncomputable section
open Set Filter Metric MeromorphicOn MeromorphicAt
open scoped Topology Complex BigOperators

namespace UV

def diskZeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℤ :=
  ∑ᶠ u : ℂ, MeromorphicOn.divisor f (closedBall c r) u

lemma disk_boundary_point {c : ℂ} {r : ℝ} (hr : 0 < r) :
    c + (r : ℂ) ∈ sphere c r := by
  rw [mem_sphere, dist_eq_norm]
  simp [abs_of_pos hr]

lemma disk_closedBall_accPt {c x : ℂ} {r : ℝ} (hr : 0 < r) (hx : x ∈ closedBall c r) :
    AccPt x (𝓟 (closedBall c r)) := by
  have hn : (closedBall c r).Nontrivial := by
    refine ⟨c, by simp [hr.le], c + (r : ℂ), sphere_subset_closedBall (disk_boundary_point hr), ?_⟩
    intro he
    have hzero : (r : ℂ) = 0 := by linear_combination -he
    exact hr.ne' (by exact_mod_cast hzero)
  exact (convex_closedBall c r).isPreconnected.preperfect_of_nontrivial hn x hx

lemma disk_divisor_zero_of_ne {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hz : z ∈ closedBall c r) (hn : f z ≠ 0) :
    MeromorphicOn.divisor f (closedBall c r) z = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq,
    (hf z hz).analyticOrderAt_eq_zero.mpr hn]
  rfl

lemma disk_meromorphic_order_finite {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ z : closedBall c r, meromorphicOrderAt f z ≠ ⊤ := by
  apply (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    ⟨⟨c, by simp [hr.le]⟩, (convex_closedBall c r).isPreconnected⟩).mp
  let w := c + (r : ℂ)
  have hw : w ∈ sphere c r := disk_boundary_point hr
  have hwc := sphere_subset_closedBall hw
  refine ⟨⟨w, hwc⟩, ?_⟩
  rw [(hf w hwc).meromorphicOrderAt_eq,
    (hf w hwc).analyticOrderAt_eq_zero.mpr (hb w hw)]
  simp

lemma disk_factorized_product_eq (d : ℂ → ℤ) (hd : d.support.Finite) :
    (∏ᶠ u : ℂ, (· - u) ^ d u) = fun z : ℂ => ∏ u ∈ hd.toFinset, (z - u) ^ d u := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hd.toFinset)]
  · ext z
    simp only [Finset.prod_apply, Pi.pow_apply]
  · simpa only [Function.FactorizedRational.mulSupport, Set.Finite.coe_toFinset] using
      (Subset.rfl : d.support ⊆ d.support)

lemma disk_logDeriv_zpow_sub (u z : ℂ) (n : ℤ) :
    logDeriv (fun w : ℂ => (w - u) ^ n) z = (n : ℂ) * (z - u)⁻¹ := by
  have hd : deriv (fun w : ℂ => w - u) z = 1 := by
    simpa only [id_eq] using ((hasDerivAt_id z).sub_const u).deriv
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_apply, hd]
  simp [div_eq_mul_inv]

lemma disk_factorized_logDeriv (d : ℂ → ℤ) (hd : d.support.Finite) {z : ℂ}
    (hz : d z = 0) :
    logDeriv (∏ᶠ u : ℂ, (· - u) ^ d u) z =
      ∑ u ∈ hd.toFinset, (d u : ℂ) * (z - u)⁻¹ := by
  rw [disk_factorized_product_eq d hd, logDeriv_prod]
  · exact Finset.sum_congr rfl (fun u _ => disk_logDeriv_zpow_sub u z (d u))
  · intro u hu
    have hdu : d u ≠ 0 := hd.mem_toFinset.mp hu
    have hzu : z ≠ u := by intro he; exact hdu (he ▸ hz)
    exact zpow_ne_zero _ (sub_ne_zero.mpr hzu)
  · intro u hu
    have hdu : d u ≠ 0 := hd.mem_toFinset.mp hu
    have hzu : z ≠ u := by intro he; exact hdu (he ▸ hz)
    exact DifferentiableAt.zpow (by fun_prop) (Or.inl (sub_ne_zero.mpr hzu))

lemma disk_circleIntegral_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    {c : ℂ} {r : ℝ} (hF : ∀ u ∈ s, CircleIntegrable (F u) c r) :
    (∮ z in C(c, r), ∑ u ∈ s, F u z) = ∑ u ∈ s, ∮ z in C(c, r), F u z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | @insert u s hu ih =>
    have hs : ∀ v ∈ s, CircleIntegrable (F v) c r := fun v hv => hF v (Finset.mem_insert_of_mem hv)
    have hsum : CircleIntegrable (fun z => ∑ v ∈ s, F v z) c r := by
      convert CircleIntegrable.sum s hs using 1
      ext z
      simp
    simp only [Finset.sum_insert hu]
    rw [circleIntegral.integral_add (hF u (Finset.mem_insert_self _ _)) hsum, ih hs]

/-- Weighted argument principle on a disk. Its right side is the actual finite
zero divisor of f; neither the count nor the contour identity is assumed. -/
theorem disk_weighted_argument_principle {f w : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hw : AnalyticOnNhd ℂ w (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) :
    (∮ z in C(c, r), w z * logDeriv f z) =
      (2 * Real.pi * Complex.I) *
        ∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall c r) u : ℂ) * w u := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c r)
  have hD := D.finiteSupport (isCompact_closedBall c r)
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ D u
  have hnonneg : ∀ z, 0 ≤ D z := hf.divisor_nonneg
  obtain ⟨g, hg, hgn, hfactor⟩ := hf.meromorphicOn.extract_zeros_poles
    (disk_meromorphic_order_finite hf hr hb) hD
  have hfac : f =ᶠ[codiscreteWithin (closedBall c r)] fun z => φ z * g z := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hfactor
  have hboundary : ∀ z ∈ sphere c r, D z = 0 :=
    fun z hz => disk_divisor_zero_of_ne hf (sphere_subset_closedBall hz) (hb z hz)
  have hins : ∀ u ∈ hD.toFinset, u ∈ ball c r := by
    intro u hu
    have hdu : D u ≠ 0 := hD.mem_toFinset.mp hu
    have huc : u ∈ closedBall c r := D.supportWithinDomain hdu
    change dist u c < r
    apply lt_of_le_of_ne (show dist u c ≤ r from huc)
    intro he
    exact hdu (hboundary u he)
  have hpoint : ∀ z ∈ sphere c r, logDeriv f z =
      (∑ u ∈ hD.toFinset, (D u : ℂ) * (z - u)⁻¹) + logDeriv g z := by
    intro z hz
    have hzc := sphere_subset_closedBall hz
    have hφ : AnalyticAt ℂ φ z := Function.FactorizedRational.analyticAt (hnonneg z)
    have hφn : φ z ≠ 0 := Function.FactorizedRational.ne_zero (hboundary z hz)
    have hfull : f =ᶠ[𝓝 z] fun z => φ z * g z := by
      apply ((hf z hzc).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (hφ.mul (hg z hzc)).continuousAt).mp
      exact (hf z hzc).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (hφ.mul (hg z hzc)).meromorphicAt hzc (disk_closedBall_accPt hr hzc) hfac
    have hlog : logDeriv f z = logDeriv (fun z => φ z * g z) z := by
      simp only [logDeriv_apply]
      rw [hfull.deriv_eq, hfull.self_of_nhds]
    rw [hlog, logDeriv_mul z hφn (hgn ⟨z, hzc⟩) hφ.differentiableAt (hg z hzc).differentiableAt]
    congr 1
    exact disk_factorized_logDeriv D hD (hboundary z hz)
  have hlogg : AnalyticOnNhd ℂ (logDeriv g) (closedBall c r) := by
    intro z hz
    exact (hg.deriv z hz).div (hg z hz) (hgn ⟨z, hz⟩)
  have hrem : (∮ z in C(c, r), w z * logDeriv g z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le (s := ∅) (by simp)
    · exact (hw.mul hlogg).continuousOn
    · intro z hz
      exact (hw.mul hlogg z (ball_subset_closedBall hz.1)).differentiableAt
  let F : ℂ → ℂ → ℂ := fun u z => (D u : ℂ) * ((z - u)⁻¹ * w z)
  have hF : ∀ u ∈ hD.toFinset, CircleIntegrable (F u) c r := by
    intro u hu
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hr]
    dsimp only [F]
    apply continuousOn_const.mul
    apply ContinuousOn.mul _ (hw.continuousOn.mono sphere_subset_closedBall)
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz
    have hun : u ∉ sphere c r := fun hh =>
      (ne_of_lt (show dist u c < r from hins u hu)) (show dist u c = r from hh)
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hun)
  have hremCI : CircleIntegrable (fun z => w z * logDeriv g z) c r := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hr]
    exact (hw.mul hlogg).continuousOn.mono sphere_subset_closedBall

  calc
    _ = ∮ z in C(c, r), (∑ u ∈ hD.toFinset, F u z) + w z * logDeriv g z := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      dsimp only
      rw [hpoint z hz, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      dsimp [F]
      ring
    _ = (∑ u ∈ hD.toFinset, ∮ z in C(c, r), F u z) := by
      rw [circleIntegral.integral_add
        (by
          convert CircleIntegrable.sum hD.toFinset hF using 1
          ext z
          simp) hremCI,
        disk_circleIntegral_finset_sum hD.toFinset F hF, hrem, add_zero]
    _ = (2 * Real.pi * Complex.I) * ∑ u ∈ hD.toFinset, (D u : ℂ) * w u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [F]
      rw [circleIntegral.integral_const_mul,
        show (∮ z in C(c, r), (z - u)⁻¹ * w z) = (2 * Real.pi * Complex.I) * w u by
          simpa only [smul_eq_mul] using hw.differentiableOn.circleIntegral_sub_inv_smul (hins u hu)]
      ring
    _ = _ := by
      congr 1
      symm
      apply finsum_eq_sum_of_support_subset
      intro u hu
      apply hD.mem_toFinset.mpr
      intro hz
      apply hu
      change (D u : ℂ) * w u = 0
      rw [hz]
      simp

theorem disk_argument_principle {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∮ z in C(c, r), logDeriv f z) =
      (diskZeroCount f c r : ℂ) := by
  have h := disk_weighted_argument_principle hf analyticOnNhd_const hr hb (w := fun _ => 1)
  simp only [one_mul, mul_one] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
  unfold diskZeroCount
  exact ((Int.castAddHom ℂ).map_finsum
    ((MeromorphicOn.divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r))).symm

/-- A nonnegative finite integer divisor of total mass one is one simple point. -/
lemma disk_finsum_one_single {α : Type*} (d : α → ℤ) (hd : d.support.Finite)
    (hn : ∀ u, 0 ≤ d u) (hsum : (∑ᶠ u, d u) = 1) :
    ∃ u, d u = 1 ∧ ∀ v, v ≠ u → d v = 0 := by
  classical
  let S := hd.toFinset
  have hs : (∑ u ∈ S, d u) = 1 := by
    rw [← finsum_eq_sum d hd]
    exact hsum
  obtain ⟨u, hu, hup⟩ := (Finset.sum_pos_iff_of_nonneg (fun u _ => hn u)).mp
    (show (0 : ℤ) < ∑ u ∈ S, d u by rw [hs]; norm_num)
  have hule : d u ≤ 1 := by
    simpa only [hs] using Finset.single_le_sum (fun v _ => hn v) hu
  have huone : d u = 1 := by omega
  refine ⟨u, huone, ?_⟩
  have herase : (∑ v ∈ S.erase u, d v) = 0 := by
    have h := Finset.sum_erase_add S d hu
    rw [hs, huone] at h
    omega
  intro v hv
  by_cases hv0 : d v = 0
  · exact hv0
  have hvs : v ∈ S := hd.mem_toFinset.mpr hv0
  have hve : v ∈ S.erase u := Finset.mem_erase.mpr ⟨hv, hvs⟩
  have hvle := Finset.single_le_sum (s := S.erase u) (f := d) (fun v _ => hn v) hve
  rw [herase] at hvle
  exact le_antisymm hvle (hn v)

lemma disk_order_zero_of_divisor_zero {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) (hz : z ∈ closedBall c r)
    (hd : MeromorphicOn.divisor f (closedBall c r) z = 0) : meromorphicOrderAt f z = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz] at hd
  have ho := WithTop.coe_untop₀_of_ne_top (disk_meromorphic_order_finite hf hr hb ⟨z, hz⟩)
  rw [hd] at ho
  exact ho.symm

lemma disk_divisor_zero_iff {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) (hz : z ∈ closedBall c r) :
    MeromorphicOn.divisor f (closedBall c r) z = 0 ↔ f z ≠ 0 := by
  constructor
  · intro hd
    exact (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      (disk_order_zero_of_divisor_zero hf hr hb hz hd)
  · exact disk_divisor_zero_of_ne hf hz

/-- Analytic order one gives both the actual zero and a nonzero derivative. -/
lemma disk_simple_of_order_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (ho : meromorphicOrderAt f z = (1 : ℤ)) : f z = 0 ∧ deriv f z ≠ 0 := by
  obtain ⟨g, hg, hgn, hfac⟩ := (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).mp ho
  have hp : f =ᶠ[𝓝[≠] z] fun w => (w - z) * g w := by
    simpa only [zpow_one, smul_eq_mul] using hfac
  have hfull : f =ᶠ[𝓝 z] fun w => (w - z) * g w :=
    (hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((analyticAt_id.sub analyticAt_const).mul hg).continuousAt).mp hp
  constructor
  · simpa using hfull.self_of_nhds
  · have hd : HasDerivAt (fun w : ℂ => (w - z) * g w) (g z) z := by
      convert ((hasDerivAt_id z).sub_const z).mul hg.differentiableAt.hasDerivAt using 1
      simp
    rw [hfull.deriv_eq, hd.deriv]
    exact hgn

lemma disk_order_one_of_simple {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z = 0) (hd : deriv f z ≠ 0) : meromorphicOrderAt f z = (1 : ℤ) := by
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt ℂ (dslope f z) z := ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have ho : analyticOrderAt f z = (1 : ℕ) := by
    apply hp.analyticAt.analyticOrderAt_eq_natCast.mpr
    refine ⟨dslope f z, hg, ?_, Eventually.of_forall fun w => ?_⟩
    · simpa only [dslope_same] using hd
    · simpa only [pow_one, hz, sub_zero] using (sub_smul_dslope f z w).symm
  rw [hp.analyticAt.meromorphicOrderAt_eq, ho]
  rfl

/-- Count one means exactly one interior zero, and that zero is simple. -/
theorem disk_zeroCount_one_unique_simple {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) (hcount : diskZeroCount f c r = 1) :
    ∃ z ∈ ball c r, f z = 0 ∧ deriv f z ≠ 0 ∧ ∀ w ∈ ball c r, f w = 0 → w = z := by
  let D := MeromorphicOn.divisor f (closedBall c r)
  obtain ⟨z, hz, honly⟩ := disk_finsum_one_single D (D.finiteSupport (isCompact_closedBall c r))
    hf.divisor_nonneg hcount
  have hzs : z ∈ D.support := by change D z ≠ 0; omega
  have hzc : z ∈ closedBall c r := D.supportWithinDomain hzs
  have horder : meromorphicOrderAt f z = (1 : ℤ) := by
    have ho := WithTop.coe_untop₀_of_ne_top (disk_meromorphic_order_finite hf hr hb ⟨z, hzc⟩)
    have hd : (meromorphicOrderAt f z).untop₀ = 1 := by
      simpa only [D, MeromorphicOn.divisor_apply hf.meromorphicOn hzc] using hz
    rw [hd] at ho
    exact ho.symm
  have hsimple := disk_simple_of_order_one (hf z hzc) horder
  have hzb : z ∈ ball c r := by
    change dist z c < r
    apply lt_of_le_of_ne (show dist z c ≤ r from hzc)
    intro he
    exact hb z he hsimple.1
  refine ⟨z, hzb, hsimple.1, hsimple.2, ?_⟩
  intro w hw hwzero
  by_contra hwz
  have hd0 : D w = 0 := honly w hwz
  exact (disk_divisor_zero_iff hf hr hb (ball_subset_closedBall hw)).mp hd0 hwzero

/-- An actually isolated simple zero has total disk divisor one. -/
theorem disk_zeroCount_eq_one_of_unique_simple {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (_hr : 0 < r)
    (hb : ∀ w ∈ sphere c r, f w ≠ 0) (hz : z ∈ ball c r)
    (hzero : f z = 0) (hd : deriv f z ≠ 0)
    (honly : ∀ w ∈ ball c r, f w = 0 → w = z) : diskZeroCount f c r = 1 := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c r)
  have hzc := ball_subset_closedBall hz
  have hDz : D z = 1 := by
    dsimp [D]
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzc,
      disk_order_one_of_simple (hf z hzc) hzero hd]
    rfl
  have hDother : ∀ w, w ≠ z → D w = 0 := by
    intro w hwz
    by_cases hw : w ∈ closedBall c r
    · apply disk_divisor_zero_of_ne hf hw
      by_cases hwb : w ∈ ball c r
      · intro hzero
        exact hwz (honly w hwb hzero)
      · have hws : w ∈ sphere c r := by
          change dist w c = r
          exact le_antisymm (show dist w c ≤ r from hw) (le_of_not_gt hwb)
        exact hb w hws
    · simp [D, hw]
  unfold diskZeroCount
  change (∑ᶠ w, D w) = 1
  rw [finsum_eq_sum_of_support_subset (s := {z})]
  · simpa only [Finset.sum_singleton] using hDz
  · intro w hw
    simp only [Finset.coe_singleton, mem_singleton_iff]
    by_contra hwz
    exact hw (hDother w hwz)

/-- The actual first log-derivative contour moment. -/
def diskRootMoment (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∮ z in C(c, r), z * logDeriv f z)

/-- When the actual disk count is one, its contour moment is its unique zero. -/
theorem diskRootMoment_eq_of_count_one {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ w ∈ sphere c r, f w ≠ 0) (hcount : diskZeroCount f c r = 1)
    (hz : z ∈ ball c r) (hzero : f z = 0) : diskRootMoment f c r = z := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c r)
  obtain ⟨u, hu, honly⟩ := disk_finsum_one_single D (D.finiteSupport (isCompact_closedBall c r))
    hf.divisor_nonneg hcount
  have hzu : z = u := by
    by_contra hne
    have hd0 : D z = 0 := honly z hne
    exact (disk_divisor_zero_iff hf hr hb (ball_subset_closedBall hz)).mp hd0 hzero
  have hmoment : (∑ᶠ v : ℂ, (D v : ℂ) * v) = z := by
    rw [hzu, finsum_eq_sum_of_support_subset (s := {u})]
    · simp [hu]
    · intro v hv
      simp only [Finset.coe_singleton, mem_singleton_iff]
      by_contra hvu
      apply hv
      dsimp only
      rw [honly v hvu]
      simp
  have h := disk_weighted_argument_principle hf analyticOnNhd_id hr hb (w := fun v => v)
  unfold diskRootMoment
  rw [h]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ((2 * Real.pi * Complex.I) * ∑ᶠ v : ℂ, (D v : ℂ) * v) = z
  rw [hmoment, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

end UV

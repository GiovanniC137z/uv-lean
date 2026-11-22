import UV.RevisionSourceTransfer
import UV.UnboundedSourceResolution
import Mathlib.MeasureTheory.PiSystem

/-! Commutation with the square-root transfer recovers all Borel projections
of the supplied nonnegative normal spectral resolution. Rational functions
of the transfer approximate the spectral cuts strongly. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : SourcePVM H}

private theorem sourceBorel_operator_one (B : SourceBorelCalculus P) :
    B.operator (fun _ => 1) = 1 := by
  simpa [P.univ] using B.indicator univ MeasurableSet.univ

private theorem sourceBorel_const (a : ℝ) : sourceBoundedBorel (fun _ => a) :=
  ⟨measurable_const, |a|, abs_nonneg _, fun _ => le_rfl⟩

private theorem sourceBorel_operator_const (B : SourceBorelCalculus P) (a : ℝ) :
    B.operator (fun _ => a) = (a : ℂ) • 1 := by
  simpa only [mul_one, sourceBorel_operator_one] using B.smul a (fun _ => 1) sourceBoundedBorel_one

private theorem sourceBorel_power {f : ℝ → ℝ} (hf : sourceBoundedBorel f) (n : ℕ) :
    sourceBoundedBorel (fun u => f u ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using sourceBoundedBorel_one
  | succ n ihn => simpa only [pow_succ] using sourceBoundedBorel_mul ihn hf

private theorem sourceBorel_operator_power (B : SourceBorelCalculus P) {f : ℝ → ℝ}
    (hf : sourceBoundedBorel f) (n : ℕ) :
    B.operator (fun u => f u ^ n) = B.operator f ^ n := by
  induction n with
  | zero => simp only [pow_zero, sourceBorel_operator_one]
  | succ n ihn =>
    simp only [pow_succ, B.mul _ _ (sourceBorel_power hf n) hf, ihn]

private theorem sourceBorel_smul_one_commute (C : H →L[ℂ] H) (a : ℝ) :
    Commute C ((a : ℂ) • (1 : H →L[ℂ] H)) := by
  show C * ((a : ℂ) • 1) = ((a : ℂ) • 1) * C
  simp

omit [CompleteSpace H] in
private theorem sourceBorel_inverse_commute (C D E : H →L[ℂ] H)
    (hCD : Commute C D) (hDE : D * E = 1) (hED : E * D = 1) : Commute C E := by
  show C * E = E * C
  calc
    C * E = (E * D) * C * E := by rw [hED, one_mul]
    _ = E * (D * C) * E := by rw [mul_assoc E D C]
    _ = E * C := by rw [← hCD.eq]; simp only [mul_assoc, hDE, mul_one]

omit [CompleteSpace H] in
private theorem sourceBorel_strong_limit_commute {A : ℕ → H →L[ℂ] H} {F C : H →L[ℂ] H}
    (h : ∀ n, Commute C (A n)) (ht : ∀ x : H, Tendsto (fun n => A n x) atTop (𝓝 (F x))) :
    Commute C F := by
  show C * F = F * C
  ext x
  have hleft : Tendsto (fun n => C (A n x)) atTop (𝓝 (C (F x))) :=
    (C.continuous.tendsto (F x)).comp (ht x)
  have hright : Tendsto (fun n => C (A n x)) atTop (𝓝 (F (C x))) := by
    refine (ht (C x)).congr' (.of_forall fun n => ?_)
    exact (congrArg (fun F' : H →L[ℂ] H => F' x) (h n).eq).symm
  exact tendsto_nhds_unique hleft hright

/-- The inverse of a strictly positive bounded symbol with constant lower
bound is a genuine inverse in the Borel calculus. -/
private theorem sourceBorel_operator_inv_commute (B : SourceBorelCalculus P)
    (C : H →L[ℂ] H) {f : ℝ → ℝ} (hf : sourceBoundedBorel f)
    {a : ℝ} (ha : 0 < a) (hfa : ∀ u, a ≤ f u) (hcomm : Commute C (B.operator f)) :
    Commute C (B.operator (fun u => (f u)⁻¹)) := by
  have hi : sourceBoundedBorel (fun u => (f u)⁻¹) := by
    refine ⟨hf.1.inv, a⁻¹, by positivity, fun u => ?_⟩
    rw [abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (hfa u)))]
    exact inv_anti₀ ha (hfa u)
  have heq : (fun u => f u * (f u)⁻¹) = fun _ => (1 : ℝ) := by
    funext u
    exact mul_inv_cancel₀ (ha.trans_le (hfa u)).ne'
  have heq' : (fun u => (f u)⁻¹ * f u) = fun _ => (1 : ℝ) := by
    funext u
    exact inv_mul_cancel₀ (ha.trans_le (hfa u)).ne'
  apply sourceBorel_inverse_commute C (B.operator f) _ hcomm
  · rw [← B.mul _ _ hf hi, heq, sourceBorel_operator_one]
  · rw [← B.mul _ _ hi hf, heq', sourceBorel_operator_one]

private def sourceCutFraction (a : ℝ) (n : ℕ) (y : ℝ) : ℝ := y ^ n / (y ^ n + a ^ n)

private theorem sourceCutFraction_mem {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ sourceCutFraction a n y ∧ sourceCutFraction a n y ≤ 1 := by
  have hp : 0 < y ^ n + a ^ n := add_pos_of_nonneg_of_pos (pow_nonneg hy n) (pow_pos ha n)
  exact ⟨div_nonneg (pow_nonneg hy n) hp.le,
    (div_le_one hp).mpr (le_add_of_nonneg_right (pow_nonneg ha.le n))⟩

private theorem sourceCutFraction_tendsto_lt {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (h : y < a) :
    Tendsto (fun n => sourceCutFraction a n y) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hy ha.le) ((div_lt_one ha).mpr h)
  have ht' := ht.div (ht.add_const 1) (by norm_num : (0 : ℝ) + 1 ≠ 0)
  simpa only [zero_div] using ht'.congr' (.of_forall fun n => by
    simp only [sourceCutFraction, div_pow, Pi.div_apply]
    field_simp [ne_of_gt (pow_pos ha n), ne_of_gt (add_pos_of_nonneg_of_pos (pow_nonneg hy n) (pow_pos ha n))])

private theorem sourceCutFraction_tendsto_gt {a y : ℝ} (ha : 0 < a) (h : a < y) :
    Tendsto (fun n => sourceCutFraction a n y) atTop (𝓝 1) := by
  have hy := ha.trans h
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha.le hy.le) ((div_lt_one hy).mpr h)
  have ht' := (tendsto_const_nhds (x := (1 : ℝ))).div (ht.const_add 1)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa only [add_zero, div_one] using ht'.congr' (.of_forall fun n => by
    simp only [sourceCutFraction, div_pow, Pi.div_apply]
    field_simp [ne_of_gt (pow_pos hy n), ne_of_gt (add_pos (pow_pos hy n) (pow_pos ha n))])

private def sourceCutPolynomial (a : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  2 * sourceCutFraction a n y ^ 2 - sourceCutFraction a n y

private theorem sourceCutPolynomial_tendsto {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    Tendsto (fun n => sourceCutPolynomial a n y) atTop
      (𝓝 ((Ioi a).indicator (fun _ => (1 : ℝ)) y)) := by
  rcases lt_trichotomy y a with h | heq | h
  · have ht := sourceCutFraction_tendsto_lt ha hy h
    simpa [sourceCutPolynomial, not_lt_of_ge h.le] using ((ht.pow 2).const_mul 2).sub ht
  · subst y
    have he : ∀ n, sourceCutFraction a n a = 1 / 2 := by
      intro n
      unfold sourceCutFraction
      field_simp [ne_of_gt (pow_pos ha n), ne_of_gt (add_pos (pow_pos ha n) (pow_pos ha n))]
      ring
    have hnot : a ∉ Ioi a := by simp
    norm_num [sourceCutPolynomial, he, hnot]
  · have ht := sourceCutFraction_tendsto_gt ha h
    have hc := ((ht.pow 2).const_mul 2).sub ht
    norm_num at hc
    simpa [sourceCutPolynomial, h] using hc

private theorem sourceBorel_operator_smul_commute (B : SourceBorelCalculus P)
    (C : H →L[ℂ] H) (a : ℝ) {f : ℝ → ℝ} (hf : sourceBoundedBorel f)
    (hc : Commute C (B.operator f)) : Commute C (B.operator (fun u => a * f u)) := by
  rw [B.smul _ _ hf]
  show C * ((a : ℂ) • B.operator f) = ((a : ℂ) • B.operator f) * C
  rw [mul_smul_comm, smul_mul_assoc, hc.eq]

/-- Sharp upper cuts of a nonnegative bounded Borel symbol commute with any
operator commuting with its spectral integral. -/
theorem sourceBorel_commute_upper_cut (B : SourceBorelCalculus P) (C : H →L[ℂ] H)
    {f : ℝ → ℝ} (hf : sourceBoundedBorel f) (hn : ∀ u, 0 ≤ f u)
    (hcf : Commute C (B.operator f)) {a : ℝ} (ha : 0 < a) :
    Commute C (P.projection (f ⁻¹' Ioi a)) := by
  let q := fun n u => sourceCutFraction a n (f u)
  let g := fun n u => sourceCutPolynomial a n (f u)
  have hq (n : ℕ) : sourceBoundedBorel (q n) := by
    refine ⟨(hf.1.pow_const n).div ((hf.1.pow_const n).add measurable_const), 1, zero_le_one, ?_⟩
    intro u
    rw [abs_of_nonneg (sourceCutFraction_mem ha (hn u) n).1]
    exact (sourceCutFraction_mem ha (hn u) n).2
  have hqc (n : ℕ) : Commute C (B.operator (q n)) := by
    let d := fun u => f u ^ n + a ^ n
    let p := fun u => f u ^ n
    have hp : sourceBoundedBorel p := sourceBorel_power hf n
    have hd : sourceBoundedBorel d := sourceBoundedBorel_add hp (sourceBorel_const (a ^ n))
    have hdc : Commute C (B.operator d) := by
      unfold d
      rw [B.add _ _ hp (sourceBorel_const (a ^ n)), sourceBorel_operator_power B hf n,
        sourceBorel_operator_const]
      exact (hcf.pow_right n).add_right (sourceBorel_smul_one_commute C _)
    have hda : ∀ u, 0 < d u := fun u =>
      add_pos_of_nonneg_of_pos (pow_nonneg (hn u) n) (pow_pos ha n)
    have hden (u : ℝ) : a ^ n ≤ d u := by
      exact le_add_of_nonneg_left (pow_nonneg (hn u) n)
    have hi : sourceBoundedBorel (fun u => (d u)⁻¹) := by
      refine ⟨hd.1.inv, (a ^ n)⁻¹, by positivity, fun u => ?_⟩
      rw [abs_of_nonneg (inv_nonneg.mpr (hda u).le)]
      exact inv_anti₀ (pow_pos ha n) (hden u)
    have he : q n = fun u => p u * (d u)⁻¹ := by
      funext u
      exact div_eq_mul_inv _ _
    rw [he, B.mul _ _ hp hi]
    have hpc : Commute C (B.operator p) := by
      simpa only [p, sourceBorel_operator_power B hf n] using hcf.pow_right n
    exact hpc.mul_right (sourceBorel_operator_inv_commute B C hd (pow_pos ha n) hden hdc)
  have hform (n : ℕ) : g n = fun u => 2 * q n u ^ 2 + (-1) * q n u := by
    funext u
    change 2 * q n u ^ 2 - q n u = _
    ring
  have hgc (n : ℕ) : Commute C (B.operator (g n)) := by
    have h₂ := sourceBorel_power (hq n) 2
    rw [hform n, B.add _ _ (sourceBoundedBorel_smul 2 h₂)
      (sourceBoundedBorel_smul (-1) (hq n))]
    exact (sourceBorel_operator_smul_commute B C 2 h₂
      (by rw [sourceBorel_operator_power B (hq n) 2]; exact (hqc n).pow_right 2)).add_right
      (sourceBorel_operator_smul_commute B C (-1) (hq n) (hqc n))
  have hgm (n : ℕ) : Measurable (g n) := by
    rw [hform n]
    exact (sourceBoundedBorel_add (sourceBoundedBorel_smul 2 (sourceBorel_power (hq n) 2))
      (sourceBoundedBorel_smul (-1) (hq n))).1
  let s := f ⁻¹' Ioi a
  have hs : MeasurableSet s := hf.1 measurableSet_Ioi
  have hbound (n : ℕ) (u : ℝ) : |g n u| ≤ 3 := by
    obtain ⟨h₀, h₁⟩ := sourceCutFraction_mem ha (hn u) n
    change 0 ≤ q n u at h₀
    change q n u ≤ 1 at h₁
    have h₂ : q n u ^ 2 ≤ 1 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]
    change |2 * q n u ^ 2 - q n u| ≤ 3
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (q n u)], by linarith⟩
  have hlim (u : ℝ) : Tendsto (fun n => g n u) atTop
      (𝓝 (s.indicator (fun _ => (1 : ℝ)) u)) := by
    simpa only [g, s, indicator, mem_preimage] using sourceCutPolynomial_tendsto ha (hn u)
  rw [← B.indicator s hs]
  apply sourceBorel_strong_limit_commute hgc
  exact B.strong_limit g _ 3 hgm (measurable_const.indicator hs) (by norm_num) hbound hlim

/-- If the half-line projections commute with an operator, then so do all
Borel projections. Countable disjoint unions use strong additivity. -/
theorem sourcePVM_commute_of_commute_lower_cuts (P : SourcePVM H) (C : H →L[ℂ] H)
    (hl : ∀ a : ℝ, Commute C (P.projection (Iio a))) :
    ∀ s, MeasurableSet s → Commute C (P.projection s) := by
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Commute C (P.projection s))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio ?_ ?_ ?_ ?_
  · change Commute C (P.projection ∅)
    rw [P.empty]
    exact Commute.zero_right _
  · rintro _ ⟨a, rfl⟩
    exact hl a
  · intro s hs hc
    have hs' : P.projection (sᶜ) = 1 - P.projection s := by
      apply eq_sub_iff_add_eq.mpr
      rw [← sourcePVM_disjoint_union P hs.compl hs disjoint_compl_left, compl_union_self, P.univ]
    change Commute C (P.projection sᶜ)
    rw [hs']
    exact (Commute.one_right _).sub_right hc
  · intro s hd hs hc
    let A := fun n => ∑ i ∈ Finset.range n, P.projection (s i)
    apply sourceBorel_strong_limit_commute (A := A)
    · intro n
      unfold A
      apply Commute.sum_right _ _
      intro i hi
      exact hc i
    · intro x
      simpa only [A, ContinuousLinearMap.sum_apply] using (P.countable s hs hd x).tendsto_sum_nat

/-- Conversely, commutation with all Borel projections implies commutation
with every bounded Borel spectral integral by simple approximation. -/
theorem sourceBorel_commute_of_commute_projections (B : SourceBorelCalculus P)
    (C : H →L[ℂ] H) {f : ℝ → ℝ} (hf : sourceBoundedBorel f)
    (h : ∀ s, MeasurableSet s → Commute C (P.projection s)) : Commute C (B.operator f) := by
  obtain ⟨hf, R, hR, hR'⟩ := hf
  let q (n : ℕ) := (sourceCoordinateApprox n).comp f hf
  have hq (n : ℕ) : Commute C (B.operator (q n)) := by
    rw [sourceBorel_simple]
    unfold sourceSimpleSpectralIntegral
    apply Commute.sum_right _ _
    intro v hv
    have hc := h ((q n) ⁻¹' {v}) ((q n).measurableSet_fiber v)
    show C * ((v : ℂ) • P.projection ((q n) ⁻¹' {v})) =
      ((v : ℂ) • P.projection ((q n) ⁻¹' {v})) * C
    rw [mul_smul_comm, smul_mul_assoc, hc.eq]
  apply sourceBorel_strong_limit_commute hq
  apply B.strong_limit _ f (2 * R) (fun n => (q n).measurable) hf (by positivity)
  · intro n u
    exact (sourceCoordinateApprox_bound n (f u)).trans (by linarith [hR' u])
  · exact fun u => sourceCoordinateApprox_tendsto (f u)

/-- Strictly positive bounded symbols have injective spectral integrals,
even when their inverse is unbounded. The regularized inverse exhausts
all spectral values by the strong normality law. -/
theorem sourceBorel_injective_of_pos (B : SourceBorelCalculus P) {f : ℝ → ℝ}
    (hf : sourceBoundedBorel f) (hpos : ∀ u, 0 < f u) : Function.Injective (B.operator f) := by
  apply (B.operator f).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  change B.operator f x = 0 at hx
  let e := fun n : ℕ => ((n : ℝ) + 1)⁻¹
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he₀ : Tendsto e atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  let g := fun n u => f u / (f u + e n)
  have hgm (n : ℕ) : Measurable (g n) := hf.1.div (hf.1.add measurable_const)
  have hbound (n : ℕ) (u : ℝ) : |g n u| ≤ 1 := by
    have hp := add_pos (hpos u) (he n)
    rw [abs_of_nonneg (div_nonneg (hpos u).le hp.le)]
    exact (div_le_one hp).mpr (le_add_of_nonneg_right (he n).le)
  have hlim (u : ℝ) : Tendsto (fun n => g n u) atTop (𝓝 (1 : ℝ)) := by
    have ht := (tendsto_const_nhds (x := f u)).div (he₀.const_add (f u))
      (by simpa using (hpos u).ne')
    simpa [g, (hpos u).ne'] using ht
  have hcalc (n : ℕ) : B.operator (g n) x = 0 := by
    let d := fun u => f u + e n
    have hd : Measurable d := hf.1.add measurable_const
    have hda (u : ℝ) : e n ≤ d u := le_add_of_nonneg_left (hpos u).le
    have hi : sourceBoundedBorel (fun u => (d u)⁻¹) := by
      refine ⟨hd.inv, (e n)⁻¹, by positivity, fun u => ?_⟩
      rw [abs_of_nonneg (inv_nonneg.mpr ((he n).le.trans (hda u)))]
      exact inv_anti₀ (he n) (hda u)
    have hprod : g n = fun u => (d u)⁻¹ * f u := by
      funext u
      exact div_eq_inv_mul _ _
    rw [hprod, B.mul _ _ hi hf, ContinuousLinearMap.mul_apply, hx, map_zero]
  have ht := B.strong_limit g (fun _ => 1) 1 hgm measurable_const zero_le_one hbound hlim x
  rw [sourceBorel_operator_one, ContinuousLinearMap.one_apply] at ht
  exact (tendsto_nhds_unique (ht.congr' (.of_forall hcalc)) tendsto_const_nhds)

/-- The normalized O-QED transfer symbol, extended to the whole spectral
line using the endpoint value at zero. -/
def sourceSquareRootTransferSymbol (r M u : ℝ) : ℝ := kernel r M (max u 0)

private theorem sourceSquareRootTransfer_borel {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) :
    sourceBoundedBorel (sourceSquareRootTransferSymbol r M) := by
  refine ⟨?_, 1, zero_le_one, fun u => ?_⟩
  · unfold sourceSquareRootTransferSymbol kernel depthProfile
    fun_prop
  · rw [sourceSquareRootTransferSymbol, abs_of_nonneg (kernel_pos _ _ _).le]
    exact kernel_le_one hr.le hM (le_max_right _ _)

private theorem kernel_lt_kernel_of_lt {r M x y : ℝ} (hr : 0 < r) (hx : 0 ≤ x)
    (hxy : x < y) : kernel r M y < kernel r M x := by
  have h := Real.sqrt_lt_sqrt (show 0 ≤ x + M ^ 2 by positivity)
    (add_lt_add_right hxy (M ^ 2))
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left (sub_lt_sub_right h M) (neg_lt_zero.mpr hr))

/-- Commutation with the exact positive-depth square-root transfer is
equivalent to commutation with all Borel projections of the supplied
nonnegative normal spectral resolution. -/
theorem square_root_transfer_commute_iff_projections (B : SourceBorelCalculus P)
    (hP : P.projection (Ici 0) = 1) (C : H →L[ℂ] H) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) :
    Commute C (B.operator (sourceSquareRootTransferSymbol r M)) ↔
      ∀ s, MeasurableSet s → Commute C (P.projection s) := by
  let f := sourceSquareRootTransferSymbol r M
  have hf : sourceBoundedBorel f := sourceSquareRootTransfer_borel hr hM
  constructor
  · intro hC
    apply sourcePVM_commute_of_commute_lower_cuts P C
    intro a
    let s := f ⁻¹' Ioi (f a)
    have hs : MeasurableSet s := hf.1 measurableSet_Ioi
    have hs' : s ∩ Ici 0 = Iio a ∩ Ici 0 := by
      ext u
      simp only [s, mem_inter_iff, mem_preimage, mem_Ici, mem_Iio, mem_Ioi]
      constructor
      · rintro ⟨hu, hu₀⟩
        refine ⟨?_, hu₀⟩
        by_contra! h
        have h' : max a 0 ≤ u := max_le h hu₀
        have hle : f u ≤ f a := by
          rcases h'.eq_or_lt with e | e
          · simp [f, sourceSquareRootTransferSymbol, max_eq_left hu₀, e]
          · exact (by simpa only [f, sourceSquareRootTransferSymbol, max_eq_left hu₀] using
              kernel_lt_kernel_of_lt (M := M) hr (le_max_right a 0) e : f u < f a).le
        exact (not_lt_of_ge hle) hu
      · rintro ⟨hu, hu₀⟩
        have ha₀ : 0 ≤ a := hu₀.trans hu.le
        exact ⟨by simpa only [f, sourceSquareRootTransferSymbol, max_eq_left hu₀,
          max_eq_left ha₀] using kernel_lt_kernel_of_lt (M := M) hr hu₀ hu, hu₀⟩
    have hcut := sourceBorel_commute_upper_cut B C hf (fun u => (kernel_pos r M (max u 0)).le)
      hC (kernel_pos r M (max a 0))
    have hproj : P.projection s = P.projection (Iio a) := by
      have h := congrArg P.projection hs'
      simpa only [P.inter s (Ici 0) hs measurableSet_Ici,
        P.inter (Iio a) (Ici 0) measurableSet_Iio measurableSet_Ici, hP, mul_one] using h
    change Commute C (P.projection s) at hcut
    simpa only [hproj] using hcut
  · exact sourceBorel_commute_of_commute_projections B C hf

/-- The exact one-sided virtual-covariance condition with no bounded
inverse assumption, through the actual supplied spectral resolution. -/
theorem square_root_transfer_covariance_iff_projections (B : SourceBorelCalculus P)
    (hP : P.projection (Ici 0) = 1) (C : H →L[ℂ] H) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) :
    let T := B.operator (sourceSquareRootTransferSymbol r M)
    T * C * T = T ^ 2 * C ↔ ∀ s, MeasurableSet s → Commute C (P.projection s) := by
  dsimp only
  rw [transferred_covariance_eq_iff_of_injective _ _
    (sourceBorel_injective_of_pos B (sourceSquareRootTransfer_borel hr hM) (fun _ => kernel_pos _ _ _))]
  exact square_root_transfer_commute_iff_projections B hP C hr hM

private theorem sourceBorel_nonnegative_inner (B : SourceBorelCalculus P)
    {f : ℝ → ℝ} (hf : sourceBoundedBorel f) (hn : ∀ u, 0 ≤ f u) (x : H) :
    0 ≤ (inner ℂ x (B.operator f x)).re := by
  obtain ⟨R,hR,hR'⟩ := hf.2
  let g := fun u => Real.sqrt (f u)
  have hg : sourceBoundedBorel g := by
    refine ⟨hf.1.sqrt, Real.sqrt R, Real.sqrt_nonneg _, fun u => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hR' u))
  have he : (fun u => g u * g u) = f := by
    funext u
    simpa only [g, pow_two] using Real.sq_sqrt (hn u)
  rw [← he, B.mul _ _ hg hg, ContinuousLinearMap.mul_apply]
  have h := (B.operator g).adjoint_inner_right x (B.operator g x)
  rw [(B.selfAdjoint g hg).adjoint_eq] at h
  rw [h]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- A bounded cut separated from zero on the negative spectral axis vanishes
when the coordinate operator has a nonnegative quadratic form. -/
theorem sourceResolution_negative_cut_zero {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K)
    (hK : ∀ x y : H, (x, y) ∈ K.graph → 0 ≤ (inner ℂ x y).re)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : R.measure.projection (Icc (-b) (-a)) = 0 := by
  let s := Icc (-b) (-a)
  let ι := s.indicator (fun _ => (1 : ℝ))
  let f := fun u => u * ι u
  let g := fun u => (-a - u) * ι u
  have hs : MeasurableSet s := measurableSet_Icc
  have hι : sourceBoundedBorel ι := sourceBoundedBorel_indicator hs
  have hf : sourceBoundedBorel f := by
    refine ⟨measurable_id.mul hι.1, b, hb, fun u => ?_⟩
    by_cases hu : u ∈ s
    · change -b ≤ u ∧ u ≤ -a at hu
      have hu' : u ∈ s := hu
      simpa only [f, ι, indicator_of_mem hu', mul_one] using
        abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
    · simpa only [f, ι, indicator_of_notMem hu, mul_zero, abs_zero] using hb
  have hg : sourceBoundedBorel g := by
    refine ⟨(measurable_const.sub measurable_id).mul hι.1, b, hb, fun u => ?_⟩
    by_cases hu : u ∈ s
    · have hu' : -b ≤ u ∧ u ≤ -a := hu
      have hnu : 0 ≤ -a - u := by linarith
      simp only [g, ι, indicator_of_mem hu, mul_one, abs_of_nonneg hnu]
      linarith
    · simpa only [g, ι, indicator_of_notMem hu, mul_zero, abs_zero] using hb
  have hgn (u : ℝ) : 0 ≤ g u := by
    by_cases hu : u ∈ s
    · have hu' : -b ≤ u ∧ u ≤ -a := hu
      simp only [g, ι, indicator_of_mem hu, mul_one]
      linarith
    · simp only [g, ι, indicator_of_notMem hu, mul_zero, le_refl]
  have he : (fun u => -a * ι u + (-1) * f u) = g := by
    funext u
    unfold f g
    ring
  have ho : R.calculus.operator g = ((-a : ℝ) : ℂ) • R.measure.projection s -
      R.calculus.operator f := by
    rw [← he, R.calculus.add _ _ (sourceBoundedBorel_smul _ hι) (sourceBoundedBorel_smul _ hf),
      R.calculus.smul _ _ hι, R.calculus.smul _ _ hf, show R.calculus.operator ι =
        R.measure.projection s from R.calculus.indicator s hs]
    simp [sub_eq_add_neg]
  ext x
  let y := R.measure.projection s x
  have hy : R.measure.projection s y = y := by
    simpa only [y, ContinuousLinearMap.mul_apply] using
      congrArg (fun A : H →L[ℂ] H => A x) (sourcePVM_idempotent R.measure hs)
  have hp := sourceResolution_borel_graph R ι hι hf y
  have hp' : (y, R.calculus.operator f y) ∈ K.graph := by
    simpa only [show R.calculus.operator ι = R.measure.projection s from R.calculus.indicator s hs,
      hy, f] using hp
  have hpos := hK _ _ hp'
  have hneg := sourceBorel_nonnegative_inner R.calculus hg hgn y
  rw [ho, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, hy, inner_sub_right,
    inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul] at hneg
  have hn : (inner ℂ y y).re = ‖y‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  rw [hn] at hneg
  have hy' : y = 0 := by
    by_contra hyne
    have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    have hlt : 0 < a * ‖y‖ ^ 2 := mul_pos ha (pow_pos hy_norm _)
    linarith
  exact hy'

/-- Nonnegativity of the actual coordinate quadratic form forces the PVM
onto the nonnegative spectral half-line. -/
theorem sourceResolution_support_nonnegative {K : H →ₗ.[ℂ] H} (R : SourceSpectralResolution K)
    (hK : ∀ x y : H, (x, y) ∈ K.graph → 0 ≤ (inner ℂ x y).re) :
    R.measure.projection (Ici 0) = 1 := by
  let s := fun n => (fun u : ℝ => -u) ⁻¹' sourcePositiveSpectralCut n
  have hs (n : ℕ) : MeasurableSet (s n) :=
    measurable_neg (sourcePositiveSpectralCut_measurable n)
  have hmono : Monotone s := fun i j hij => preimage_mono (sourcePositiveSpectralCut_mono hij)
  have hset : (⋃ n, s n) = Iio 0 := by
    simp only [s, ← preimage_iUnion, sourcePositiveSpectralCut_iUnion]
    ext u
    simp only [mem_preimage, mem_Ioi, mem_Iio, neg_pos]
  have hzero (n : ℕ) : R.measure.projection (s n) = 0 := by
    have heq : s n = Icc (-((n : ℝ) + 1)) (-((n : ℝ) + 1)⁻¹) := by
      ext u
      simp only [s, sourcePositiveSpectralCut, mem_preimage, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [heq]
    exact sourceResolution_negative_cut_zero R hK (by positivity) (by positivity)
  have hc : R.measure.projection (Iio 0) = 0 := by
    ext x
    have ht := sourcePVM_tendsto_iUnion R.measure s hs hmono x
    rw [hset] at ht
    simp only [hzero, ContinuousLinearMap.zero_apply] at ht ⊢
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hd : Disjoint (Iio (0 : ℝ)) (Ici 0) :=
    disjoint_left.mpr fun u hu₁ hu₂ => (not_lt_of_ge (mem_Ici.mp hu₂)) (mem_Iio.mp hu₁)
  have ht := (sourcePVM_disjoint_union R.measure measurableSet_Iio measurableSet_Ici hd).symm
  simpa only [Iio_union_Ici, R.measure.univ, hc, zero_add] using ht

/-- The transfer equivalence stated on the spectral resolution of the
nonnegative, possibly unbounded normal coordinate operator. -/
theorem normal_transfer_covariance_iff_projections {K : H →ₗ.[ℂ] H}
    (R : SourceSpectralResolution K) (hK : ∀ x y : H, (x, y) ∈ K.graph →
      0 ≤ (inner ℂ x y).re) (C : H →L[ℂ] H) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) :
    let T := R.calculus.operator (sourceSquareRootTransferSymbol r M)
    T * C * T = T ^ 2 * C ↔ ∀ s, MeasurableSet s → Commute C (R.measure.projection s) :=
  square_root_transfer_covariance_iff_projections R.calculus
    (sourceResolution_support_nonnegative R hK) C hr hM

end UV

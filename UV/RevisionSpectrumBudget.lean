import UV.StableMomentThreshold
import Mathlib.MeasureTheory.Function.L2Space

/-! Weighted diagonal bounds and a divergent diagonal bubble of a positive
matrix Stieltjes representation. The density formulation uses a common
positive dominating measure, with the cross total variation given by the
norm of the cross density. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The positive weight at the sampling point (x). -/
def stieltjesWeight (x s : ℝ) : ℝ := (x+s)⁻¹

/-- A weighted Stieltjes transform of a real density. -/
def stieltjes (μ : Measure α) (s f : α → ℝ) (x : ℝ) : ℝ :=
  ∫ t, stieltjesWeight x (s t) * f t ∂μ

/-- The kernel bound transferring finite weighted mass from one positive
reference point to any other. -/
theorem weight_comparison {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 ≤ s) :
    stieltjesWeight x s ≤ max 1 (y/x) * stieltjesWeight y s := by
  unfold stieltjesWeight
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  have h₁ : y ≤ max 1 (y/x) * x :=
    (div_le_iff₀ hx).mp (le_max_right _ _)
  have h₂ : s ≤ max 1 (y/x) * s := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (y/x)) hs
  nlinarith

theorem stieltjesWeight_pos {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    0 < stieltjesWeight x s := by unfold stieltjesWeight; positivity

theorem stieltjes_integrable {s f : α → ℝ} (hs : Measurable s)
    (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t) (hf : AEStronglyMeasurable f μ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (href : Integrable (fun t => stieltjesWeight y (s t) * f t) μ) :
    Integrable (fun t => stieltjesWeight x (s t) * f t) μ := by
  apply (href.const_mul (max 1 (y/x))).mono
    (((measurable_const.add hs).inv.aestronglyMeasurable).mul hf)
  filter_upwards [hs₀] with t ht
  change ‖stieltjesWeight x (s t) * f t‖ ≤ ‖max 1 (y/x) * (stieltjesWeight y (s t) * f t)‖
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_pos (stieltjesWeight_pos hx ht), abs_of_pos (stieltjesWeight_pos hy ht),
    abs_of_nonneg (show 0 ≤ max 1 (y/x) from le_trans zero_le_one (le_max_left _ _))]
  exact (mul_le_mul_of_nonneg_right (weight_comparison hx hy ht) (abs_nonneg (f t))).trans_eq
    (by ring)

theorem stieltjes_nonneg {s f : α → ℝ} (hs : ∀ᵐ t ∂μ, 0 ≤ s t)
    (hf : ∀ᵐ t ∂μ, 0 ≤ f t) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ stieltjes μ s f x := by
  apply integral_nonneg_of_ae
  filter_upwards [hs, hf] with t ht hft
  unfold stieltjesWeight
  positivity

/-- The spectral product and sum budgets, with independently varying
diagonals. The proof applies to complex cross densities. -/
theorem positive_density_budget {a b : α → ℝ} {c : α → ℂ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : AEStronglyMeasurable c μ)
    (hpos : ∀ᵐ t ∂μ, 0 ≤ a t ∧ 0 ≤ b t ∧ ‖c t‖^2 ≤ a t * b t) :
    Integrable (fun t => ‖c t‖) μ ∧
    (∫ t, ‖c t‖ ∂μ)^2 ≤ (∫ t, a t ∂μ) * (∫ t, b t ∂μ) ∧
    2 * (∫ t, ‖c t‖ ∂μ) ≤ (∫ t, a t ∂μ) + (∫ t, b t ∂μ) := by
  have haa : ∀ᵐ t ∂μ, 0 ≤ a t := hpos.mono fun _ h => h.1
  have hbb : ∀ᵐ t ∂μ, 0 ≤ b t := hpos.mono fun _ h => h.2.1
  have hhalf : ∀ᵐ t ∂μ, ‖c t‖ ≤ (a t+b t)/2 := by
    filter_upwards [hpos] with t ⟨ha', hb', hc'⟩
    have h := sq_nonneg (a t-b t)
    have h' : 0 ≤ ‖c t‖ := norm_nonneg _
    by_contra! hlt
    have hlt2 := mul_self_lt_mul_self (show 0 ≤ (a t + b t)/2 by positivity) hlt
    nlinarith
  have hsumInt : Integrable (fun t => (a t + b t)/2) μ := (ha.add hb).div_const 2
  have hint := hsumInt.mono' hc.norm (hhalf.mono fun t ht => by
    simpa only [Real.norm_of_nonneg (norm_nonneg (c t))] using ht)
  have hsum := integral_mono_ae hint hsumInt hhalf
  rw [integral_div, integral_add ha hb] at hsum
  refine ⟨hint, ?_, by linarith⟩
  have hroot_int (f : α → ℝ) (hf : Integrable f μ) (hf₀ : ∀ᵐ t ∂μ, 0 ≤ f t) :
      MemLp (fun t => Real.sqrt (f t)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).2
    refine hf.congr ?_
    filter_upwards [hf₀] with t ht using (Real.sq_sqrt ht).symm
  have hl := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun t => Real.sqrt_nonneg (a t))
    (Eventually.of_forall fun t => Real.sqrt_nonneg (b t))
    (by simpa using hroot_int a ha haa) (by simpa using hroot_int b hb hbb)
  simp only [← Real.sqrt_eq_rpow, Real.rpow_two] at hl
  have hfa : (∫ t, (Real.sqrt (a t))^2 ∂μ) = ∫ t, a t ∂μ := by
    apply integral_congr_ae
    filter_upwards [haa] with t ht using Real.sq_sqrt ht
  have hfb : (∫ t, (Real.sqrt (b t))^2 ∂μ) = ∫ t, b t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hbb] with t ht using Real.sq_sqrt ht
  rw [hfa, hfb] at hl
  have hprod : Integrable (fun t => Real.sqrt (a t) * Real.sqrt (b t)) μ :=
    (hroot_int a ha haa).integrable_mul (hroot_int b hb hbb)
  have hle : (∫ t, ‖c t‖ ∂μ) ≤ Real.sqrt (∫ t, a t ∂μ) * Real.sqrt (∫ t, b t ∂μ) := by
    apply le_trans (integral_mono_ae hint hprod ?_) hl
    filter_upwards [hpos] with t ⟨ha', hb', hc'⟩
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt ha', Real.sq_sqrt hb'] using hc'
  have hcle : 0 ≤ ∫ t, ‖c t‖ ∂μ := integral_nonneg fun t => norm_nonneg _
  have hs := (sq_le_sq₀ hcle (by positivity)).mpr hle
  simpa only [mul_pow, Real.sq_sqrt (integral_nonneg_of_ae haa),
    Real.sq_sqrt (integral_nonneg_of_ae hbb)] using hs

theorem positive_stieltjes_budget {s a b : α → ℝ} {c : α → ℂ} {x : ℝ}
    (hx : 0 < x) (hs : Measurable s) (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t)
    (ha : Integrable (fun t => stieltjesWeight x (s t) * a t) μ)
    (hb : Integrable (fun t => stieltjesWeight x (s t) * b t) μ)
    (hc : AEStronglyMeasurable c μ)
    (hpos : ∀ᵐ t ∂μ, 0 ≤ a t ∧ 0 ≤ b t ∧ ‖c t‖^2 ≤ a t * b t) :
    Integrable (fun t => stieltjesWeight x (s t) * ‖c t‖) μ ∧
    (stieltjes μ s (fun t => ‖c t‖) x)^2 ≤ stieltjes μ s a x * stieltjes μ s b x ∧
    2 * stieltjes μ s (fun t => ‖c t‖) x ≤ stieltjes μ s a x + stieltjes μ s b x := by
  let w := fun t => stieltjesWeight x (s t)
  have hw : Measurable w := (measurable_const.add hs).inv
  have hw₀ : ∀ᵐ t ∂μ, 0 ≤ w t := by
    filter_upwards [hs₀] with t ht
    exact (stieltjesWeight_pos hx ht).le
  have hnorm : (fun t => ‖(w t : ℂ)*c t‖) =ᵐ[μ] (fun t => w t * ‖c t‖) := by
    filter_upwards [hw₀] with t ht
    simp [Complex.norm_real, Real.norm_of_nonneg ht]
  obtain ⟨hint, hmul, hadd⟩ := positive_density_budget ha hb
    ((Complex.continuous_ofReal.measurable.comp hw).aestronglyMeasurable.mul hc)
    (c := fun t => (w t : ℂ)*c t) (by
      filter_upwards [hw₀, hpos] with t ht ⟨hat, hbt, hct⟩
      refine ⟨mul_nonneg ht hat, mul_nonneg ht hbt, ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht, mul_pow]
      calc
        w t ^ 2 * ‖c t‖^2 ≤ w t ^ 2 * (a t*b t) :=
          mul_le_mul_of_nonneg_left hct (sq_nonneg _)
        _ = _ := by ring)
  rw [integral_congr_ae hnorm] at hmul hadd
  exact ⟨hint.congr hnorm, hmul, hadd⟩

/-- Positivity forces the cross density to vanish where its first diagonal
vanishes, including for independent complex cross channels. -/
theorem cross_density_supported_at_pole {s a b : α → ℝ} {c : α → ℂ} {m : ℝ}
    (hdiag : ∀ᵐ t ∂μ, s t ≠ m → a t = 0)
    (hpos : ∀ᵐ t ∂μ, ‖c t‖^2 ≤ a t*b t) :
    ∀ᵐ t ∂μ, s t ≠ m → c t = 0 := by
  filter_upwards [hdiag, hpos] with t hd hp ht
  rw [hd ht, zero_mul] at hp
  apply norm_eq_zero.mp
  exact le_antisymm (by nlinarith [norm_nonneg (c t)]) (norm_nonneg _)

/-- A pure-pole diagonal, stated as an equality of its weighted positive
measure on Borel sets, forces a pure-pole cross transform. -/
theorem pure_pole_cross {s a b : α → ℝ} {c : α → ℂ} {m y Z : ℝ}
    (hy : 0 < y) (hs : Measurable s) (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t)
    (ha₀ : ∀ᵐ t ∂μ, 0 ≤ a t)
    (hpos : ∀ᵐ t ∂μ, ‖c t‖^2 ≤ a t*b t)
    (ha : Integrable (fun t => stieltjesWeight y (s t)*a t) μ)
    (hpole : ∀ B : Set ℝ, MeasurableSet B →
      (∫ t in s ⁻¹' B, stieltjesWeight y (s t)*a t ∂μ) =
        Z * stieltjesWeight y m * B.indicator (fun _ => (1:ℝ)) m) :
    ∃ coeff : ℂ, ∀ x : ℝ,
      (∫ t, (stieltjesWeight x (s t) : ℂ)*c t ∂μ) = coeff / (↑x + ↑m) := by
  let B := ({m} : Set ℝ)ᶜ
  have hB : MeasurableSet B := (measurableSet_singleton m).compl
  have hBB := hs hB
  have hzero : (∫ t in s ⁻¹' B, stieltjesWeight y (s t)*a t ∂μ) = 0 := by
    simpa [B] using hpole B hB
  have hnonneg : ∀ᵐ t ∂μ, 0 ≤ stieltjesWeight y (s t) * a t := by
    filter_upwards [hs₀, ha₀] with t hst hat
    exact mul_nonneg (stieltjesWeight_pos hy hst).le hat
  have hzero' := (integral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_ae hnonneg) ha.integrableOn).mp hzero
  have hdiag : ∀ᵐ t ∂μ, s t ≠ m → a t = 0 := by
    change ∀ᵐ t ∂μ.restrict (s ⁻¹' B), stieltjesWeight y (s t) * a t = 0 at hzero'
    rw [ae_restrict_iff' hBB] at hzero'
    filter_upwards [hs₀, hzero'] with t hst ht hneq
    exact (mul_eq_zero.mp (ht hneq)).resolve_left
      (stieltjesWeight_pos hy hst).ne'
  have hcross := cross_density_supported_at_pole hdiag hpos
  refine ⟨∫ t, c t ∂μ, fun x => ?_⟩
  calc
    _ = ∫ t, (stieltjesWeight x m : ℂ)*c t ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcross] with t ht
      by_cases heq : s t = m
      · rw [heq]
      · rw [ht heq, mul_zero, mul_zero]
    _ = _ := by rw [integral_const_mul]; simp [stieltjesWeight, div_eq_mul_inv, mul_comm]

theorem stieltjes_antitone {s f : α → ℝ} (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t)
    (hf₀ : ∀ᵐ t ∂μ, 0 ≤ f t) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hxInt : Integrable (fun t => stieltjesWeight x (s t)*f t) μ)
    (hyInt : Integrable (fun t => stieltjesWeight y (s t)*f t) μ) :
    stieltjes μ s f y ≤ stieltjes μ s f x := by
  apply integral_mono_ae hyInt hxInt
  filter_upwards [hs₀, hf₀] with t hst hft
  apply mul_le_mul_of_nonneg_right _ hft
  unfold stieltjesWeight
  exact inv_anti₀ (by linarith) (by linarith)

theorem stieltjes_scaled_lower {s f : α → ℝ} (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t)
    (hf₀ : ∀ᵐ t ∂μ, 0 ≤ f t) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hxInt : Integrable (fun t => stieltjesWeight x (s t)*f t) μ)
    (hyInt : Integrable (fun t => stieltjesWeight y (s t)*f t) μ) :
    (y/x) * stieltjes μ s f y ≤ stieltjes μ s f x := by
  unfold stieltjes
  rw [← integral_const_mul]
  apply integral_mono_ae (hyInt.const_mul _) hxInt
  filter_upwards [hs₀, hf₀] with t ht hft
  simp only [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hft
  have hxp : 0 < x := hy.trans_le hyx
  unfold stieltjesWeight
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hxp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hyx) ht]

private def fourDimensionalInverseTail (R : ℝ) (q : ScalarMomentum) : ℝ :=
  if R ≤ ‖q‖ then (‖q‖^4)⁻¹ else 0

private theorem fourDimensionalInverseTail_nonintegrable {R : ℝ} (hR : 0 < R) :
    ¬ Integrable (fourDimensionalInverseTail R) := by
  intro hi
  have hradial := (integrable_fun_norm_addHaar (E := ScalarMomentum) volume
    (f := fun r : ℝ => if R ≤ r then (r^4)⁻¹ else 0)).mp hi
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] at hradial
  have hinv : IntegrableOn (fun r : ℝ => r ^ (-(1:ℝ))) (Ioi R) := by
    apply (hradial.mono_set (Ioi_subset_Ioi hR.le)).congr_fun _ measurableSet_Ioi
    intro r hr
    change R < r at hr
    dsimp only
    rw [if_pos hr.le, Real.rpow_neg_one]
    field_simp [(hR.trans hr).ne']
  have h := (integrableOn_Ioi_rpow_iff hR).mp hinv
  norm_num at h

/-- The completed bubble diverges for any nonzero cross covariance within
the matrix-density representation, a stronger conclusion than for the
particular shifted square-root family. Finite weighted mass at one reference
point is sufficient. -/
theorem completed_bubble_nonintegrable {s a b : α → ℝ} {c : α → ℂ} {y : ℝ}
    (hy : 0 < y) (hs : Measurable s) (hs₀ : ∀ᵐ t ∂μ, 0 ≤ s t)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ)
    (haInt : Integrable (fun t => stieltjesWeight y (s t)*a t) μ)
    (hbInt : Integrable (fun t => stieltjesWeight y (s t)*b t) μ)
    (hpos : ∀ᵐ t ∂μ, 0 ≤ a t ∧ 0 ≤ b t ∧ ‖c t‖^2 ≤ a t*b t)
    (hcross : (∫ t, (stieltjesWeight y (s t) : ℂ)*c t ∂μ) ≠ 0)
    (p : ScalarMomentum) :
    ¬ Integrable (fun q : ScalarMomentum => stieltjes μ s a (‖q‖^2) *
      stieltjes μ s b (‖q+p‖^2)) := by
  let d := stieltjes μ s (fun t => ‖c t‖) y
  obtain ⟨hdy, -, -⟩ := positive_stieltjes_budget hy hs hs₀ haInt hbInt hc hpos
  have hd : 0 < d := by
    have hnorm := norm_integral_le_integral_norm (μ := μ) (fun t => (stieltjesWeight y (s t) : ℂ)*c t)
    have heq : (∫ t, ‖(stieltjesWeight y (s t) : ℂ)*c t‖ ∂μ) = d := by
      apply integral_congr_ae
      filter_upwards [hs₀] with t ht
      simp [Real.norm_of_nonneg (stieltjesWeight_pos hy ht).le]
    rw [heq] at hnorm
    exact (norm_pos_iff.mpr hcross).trans_le hnorm
  have haIntAll {x : ℝ} (hx : 0 < x) := stieltjes_integrable hs hs₀ ha hx hy haInt
  have hbIntAll {x : ℝ} (hx : 0 < x) := stieltjes_integrable hs hs₀ hb hx hy hbInt
  let R := 3 * ‖p‖ + Real.sqrt y + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let coefficient := (y*d)^2/2
  have hcoeff : 0 < coefficient := by dsimp [coefficient]; positivity
  intro hInt
  apply fourDimensionalInverseTail_nonintegrable hR
  apply (hInt.const_mul coefficient⁻¹).mono'
  · unfold fourDimensionalInverseTail
    exact (Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (by fun_prop) measurable_const).aestronglyMeasurable
  · filter_upwards with q
    by_cases hr : R ≤ ‖q‖
    · have hq : 0 < ‖q‖ := hR.trans_le hr
      have hpn : 3*‖p‖ < ‖q‖ := by dsimp [R] at hr; linarith [Real.sqrt_nonneg y]
      have hq' : 0 < ‖q + p‖ := by
        have hh := norm_sub_le (q+p) p
        rw [add_sub_cancel_right] at hh
        linarith [norm_nonneg p]
      have hsqmin : y ≤ ‖q‖^2 := by
        rw [← Real.sq_sqrt hy.le]
        apply (sq_le_sq₀ (Real.sqrt_nonneg y) (norm_nonneg q)).mpr
        dsimp [R] at hr
        linarith [norm_nonneg p]
      have hsqshift : ‖q+p‖^2 ≤ 2*‖q‖^2 := by
        have h := norm_add_le q p
        have hle := (sq_le_sq₀ (norm_nonneg (q+p))
          (add_nonneg (norm_nonneg q) (norm_nonneg p))).mpr h
        have hp := (sq_le_sq₀ (norm_nonneg p) (by positivity : 0 ≤ ‖q‖/3)).mpr
          (by linarith : ‖p‖ ≤ ‖q‖/3)
        have hpq := mul_le_mul_of_nonneg_right (show ‖p‖ ≤ ‖q‖/3 by linarith)
          (norm_nonneg q)
        nlinarith
      let x := ‖q‖^2
      let x' := ‖q+p‖^2
      have hx : 0 < x := by dsimp [x]; positivity
      have hx' : 0 < x' := by dsimp [x']; positivity
      have h2x : 0 < 2*x := by linarith
      have ha₀ := hpos.mono fun _ h => h.1
      have hb₀ := hpos.mono fun _ h => h.2.1
      obtain ⟨hdInt, hbud, -⟩ := positive_stieltjes_budget hx hs hs₀
        (haIntAll hx) (hbIntAll hx) hc hpos
      have hhalf := stieltjes_scaled_lower hs₀ hb₀ hx (show x ≤ 2*x by linarith)
        (hbIntAll h2x) (hbIntAll hx)
      have hfactor : x/(2*x) = 1/2 := by field_simp
      rw [hfactor] at hhalf
      have hmon := stieltjes_antitone hs₀ hb₀ hx' hsqshift (hbIntAll hx') (hbIntAll h2x)
      have hlower := stieltjes_scaled_lower hs₀
        (Eventually.of_forall fun t => norm_nonneg (c t)) hy hsqmin hdInt hdy
      have hsquare := (sq_le_sq₀ (show 0 ≤ (y/x)*d by positivity)
        (stieltjes_nonneg hs₀ (Eventually.of_forall fun t => norm_nonneg (c t)) hx.le)).mpr hlower
      have hnonneg := stieltjes_nonneg hs₀ ha₀ hx.le
      have hprod := mul_le_mul_of_nonneg_left (hhalf.trans hmon) hnonneg
      have hbound :
          coefficient * (‖q‖^4)⁻¹ ≤ stieltjes μ s a x * stieltjes μ s b x' := by
        have heq : coefficient * (‖q‖^4)⁻¹ = (((y/x)*d)^2)/2 := by
          dsimp [coefficient, x]
          field_simp
        rw [heq]
        nlinarith
      rw [fourDimensionalInverseTail, if_pos hr, Real.norm_of_nonneg (by positivity)]
      change (‖q‖^4)⁻¹ ≤ coefficient⁻¹ * (stieltjes μ s a x * stieltjes μ s b x')
      rw [← div_eq_inv_mul, le_div_iff₀ hcoeff]
      simpa only [mul_comm coefficient] using hbound
    · rw [fourDimensionalInverseTail, if_neg hr, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hcoeff.le) (mul_nonneg
        (stieltjes_nonneg hs₀ (hpos.mono fun _ h => h.1) (sq_nonneg _))
        (stieltjes_nonneg hs₀ (hpos.mono fun _ h => h.2.1) (sq_nonneg _)))

end UV.RevisionSpectrum

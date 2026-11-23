import UV.ContinueHeatLinkLambert
import UV.ContinueHeatLinkPoles

/-! Classification of the complex zeros of the fixed-width heat-link
denominator. At positive argument the branch indices are fixed by the
principal phase in log w + w = log A + 2π i n. -/

noncomputable section

namespace UV.HeatMaxwell

open Real Set
open scoped ComplexConjugate

private theorem heat_upper_arg {w : ℂ} (hw : 0 < w.im) :
    w.arg = π/2 - Real.arctan (w.re/w.im) := by
  have hs : √(1+(w.re/w.im)^2) = ‖w‖/w.im := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (norm_nonneg _) hw.le)).mpr
    simp only [div_pow,Complex.sq_norm,Complex.normSq_apply]
    field_simp
    ring
  rw [Complex.arg_of_im_pos hw]
  apply Real.arccos_eq_of_eq_cos
  · linarith only [Real.arctan_lt_pi_div_two (w.re/w.im)]
  · linarith only [Real.neg_pi_div_two_lt_arctan (w.re/w.im)]
  · rw [Real.cos_pi_div_two_sub,Real.sin_arctan,hs]
    field_simp

theorem heatLambert_upper_exhaustive {w : ℂ} {A : ℝ} (hA : 0 < A)
    (hw : w*Complex.exp w = (A:ℂ)) (hb : 0 < w.im) :
    ∃ n : ℕ, w = heatLambertUpper n A := by
  have hne : w ≠ 0 := by intro h; simp [h] at hb
  have he : Complex.exp (Complex.log w + w) = Complex.exp ((Real.log A:ℝ):ℂ) := by
    rw [Complex.exp_add,Complex.exp_log hne,hw,← Complex.ofReal_exp,Real.exp_log hA]
  obtain ⟨j,hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hphase := congrArg Complex.im hj
  norm_num [Complex.mul_im,Complex.mul_re,Complex.log_im] at hphase
  let t := w.re/w.im
  have harg := heat_upper_arg hb
  have hjpos : 0 < (j:ℝ) := by
    apply pos_of_mul_pos_left (b := 2*π)
    · rw [← hphase]
      linarith only [harg,hb,Real.arctan_lt_pi_div_two t]
    · positivity
  have hjpos' : 0 < j := by exact_mod_cast hjpos
  obtain ⟨n,hn⟩ : ∃ n : ℕ, j = (n:ℤ)+1 := ⟨j.toNat-1,by omega⟩
  rw [hn] at hphase
  push_cast at hphase
  have hb' : w.im = heatBranchHeight n t := by
    unfold heatBranchHeight
    change w.arg = π/2 - Real.arctan t at harg
    linarith only [hphase,harg]
  have hp : w = heatBranchPoint n t := by
    apply Complex.ext
    · change w.re = t*heatBranchHeight n t
      rw [← hb']
      exact (div_mul_cancel₀ _ hb.ne').symm
    · exact hb'
  have hlog : heatBranchLog n t = Real.log A := by
    apply Real.exp_injective
    rw [Real.exp_log hA]
    have heq := heatBranchPoint_mul_exp n t
    rw [← hp,hw,Complex.ofReal_inj] at heq
    exact heq.symm
  have ht : t = Function.surjInv (heatBranchLog_bijective n).surjective (Real.log A) :=
    (heatBranchLog_bijective n).injective
      (hlog.trans (Function.rightInverse_surjInv (heatBranchLog_bijective n).surjective _).symm)
  exact ⟨n,hp.trans (congrArg (heatBranchPoint n) ht)⟩

private theorem principal_lambert_exists {A : ℝ} (hA : 0 < A) :
    ∃! t : ℝ, 0 < t ∧ t*Real.exp t = A := by
  let f := fun t : ℝ => t*Real.exp t
  have hc : Continuous f := continuous_id.mul Real.continuous_exp
  have hhi := le_mul_of_one_le_right hA.le (Real.one_le_exp hA.le)
  obtain ⟨t,ht,hf⟩ := intermediate_value_Icc hA.le hc.continuousOn
    (show A ∈ Icc (f 0) (f A) from ⟨by simpa only [f,zero_mul] using hA.le,hhi⟩)
  have hp : 0 < t := pos_of_mul_pos_left (hf.symm ▸ hA) (Real.exp_pos _).le
  refine ⟨t,⟨hp,hf⟩,?_⟩
  intro s hs
  have hmon : StrictMonoOn f (Ici 0) := fun x hx y _ hxy =>
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hxy (Real.exp_le_exp.mpr hxy.le) hx (Real.exp_pos _)
  exact hmon.injOn hs.1.le hp.le (hs.2.trans hf.symm)

/-- Positive-argument Lambert branches. The upper strip numbered k in
the construction has conventional index k+1. Its conjugate has index
−(k+1), and index zero is the positive real branch. -/
def heatLambertBranch (A : ℝ) (hA : 0 < A) : ℤ → ℂ
  | .ofNat 0 => ((principal_lambert_exists hA).exists.choose : ℝ)
  | .ofNat (n+1) => heatLambertUpper n A
  | .negSucc n => conj (heatLambertUpper n A)

theorem heatLambertBranch_spec {A : ℝ} (hA : 0 < A) (j : ℤ) :
    heatLambertBranch A hA j * Complex.exp (heatLambertBranch A hA j) = (A:ℂ) := by
  cases j with
  | ofNat n =>
    cases n with
    | zero =>
      change ((_ : ℝ):ℂ) * Complex.exp ((_ : ℝ):ℂ) = _
      rw [← Complex.ofReal_exp,← Complex.ofReal_mul]
      exact congrArg Complex.ofReal (principal_lambert_exists hA).exists.choose_spec.2
    | succ n => exact (heatLambertUpper_spec n hA).1
  | negSucc n =>
    change conj _ * Complex.exp (conj _) = _
    rw [Complex.exp_conj,← map_mul,(heatLambertUpper_spec n hA).1,Complex.conj_ofReal]

theorem heatLambert_all_branches {A : ℝ} (hA : 0 < A) (w : ℂ) :
    w*Complex.exp w = (A:ℂ) ↔ ∃ j : ℤ, w = heatLambertBranch A hA j := by
  constructor
  · intro hw
    rcases lt_trichotomy 0 w.im with hb | hb | hb
    · obtain ⟨n,hn⟩ := heatLambert_upper_exhaustive hA hw hb
      exact ⟨.ofNat (n+1),hn⟩
    · have he : w = (w.re:ℂ) := Complex.ext rfl hb.symm
      rw [he,← Complex.ofReal_exp,← Complex.ofReal_mul,Complex.ofReal_inj] at hw
      have hr := pos_of_mul_pos_left (hw.symm ▸ hA) (Real.exp_pos _).le
      refine ⟨0,he.trans (congrArg Complex.ofReal ?_)⟩
      exact (principal_lambert_exists hA).unique ⟨hr,hw⟩ (principal_lambert_exists hA).exists.choose_spec
    · have hc : conj w * Complex.exp (conj w) = (A:ℂ) := by
        rw [Complex.exp_conj,← map_mul,hw,Complex.conj_ofReal]
      obtain ⟨n,hn⟩ := heatLambert_upper_exhaustive hA hc (show 0 < (conj w).im from neg_pos.mpr hb)
      exact ⟨.negSucc n,by simpa only [map_star,star_star,starRingEnd_apply] using congrArg (starRingEnd ℂ) hn⟩
  · rintro ⟨j,rfl⟩
    exact heatLambertBranch_spec hA j

/-- Equation s6-freepole with all integer sheets at positive mass and width. -/
theorem heatFreeVector_full_pole_locus {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (z : ℂ) :
    heatVectorDenominator m a z = 0 ↔
      ∃ j : ℤ, z = -heatLambertBranch (2*a^2*m^2) (by positivity) j / (2*(a:ℂ)^2) := by
  have hc : 2*(a:ℂ)^2 ≠ 0 := by exact_mod_cast (show 2*a^2 ≠ 0 by positivity)
  rw [heatVector_zero_iff_lambert ha,heatLambert_all_branches (show 0 < 2*a^2*m^2 by positivity)]
  exact exists_congr fun j => by
    rw [eq_div_iff hc]
    constructor <;> intro h <;> linear_combination -h

end UV.HeatMaxwell

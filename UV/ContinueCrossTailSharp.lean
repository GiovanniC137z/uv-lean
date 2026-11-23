import UV.ContinueCrossTailDensity
import UV.ContinueCrossTailTransfer
import UV.ContinueCrossTailPeriodic
import Mathlib.Analysis.Asymptotics.Defs

/-! The sharp logarithmic price of the admitted signed cross law
(equation `eq:update-cross-cost-tail`). The intrinsic Euclidean variable
(x) and spectral variable (s) are both mass squared on the fixed
sector plane. The positive depth (a) is held fixed. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Asymptotics Topology

namespace UV.RevisionSpectrum

private theorem crossTail_log_coordinate_bound {a M K R : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hKR : K ≤ R) :
    |2*Real.log R - Real.log (a^2*(R^2+M^2))| ≤
      |Real.log (a^2)| + Real.log (1+M^2/K^2) := by
  have hR := hK.trans_le hKR
  have hx : 0 < R^2+M^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hR) (sq_nonneg _)
  have hq : 0 < R^2 := sq_pos_of_pos hR
  have hd : 1 ≤ (R^2+M^2)/R^2 :=
    (le_div_iff₀ hq).2 (by nlinarith [sq_nonneg M])
  have hupper : (R^2+M^2)/R^2 ≤ 1+M^2/K^2 := by
    rw [add_div, div_self hq.ne']
    exact add_le_add_left (div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos hK) ((sq_le_sq₀ hK.le hR.le).2 hKR)) _
  have he : 2*Real.log R - Real.log (a^2*(R^2+M^2)) =
      -Real.log (a^2) - Real.log ((R^2+M^2)/R^2) := by
    rw [Real.log_mul (sq_pos_of_pos ha).ne' hx.ne', Real.log_div hx.ne' hq.ne', Real.log_pow]
    norm_num
    ring
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (Real.log_nonneg hd)]
  exact add_le_add_left (Real.log_le_log (lt_of_lt_of_le zero_lt_one hd) hupper) _

/-- The sharp cutoff growth of the actual total variation of the signed
atom-plus-continuum spectral measure. -/
theorem crossTailVariation_cutoff_sharp_log {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    ∃ C ≥ 0, ∀ᶠ x : ℝ in atTop,
      |(crossTailVariation a M m₂).real (Iic x) -
        (2*Real.exp (a*M)/Real.pi^2)*Real.log (a^2*x)| ≤ C := by
  let K := Real.sqrt (2*|M^2-m₂|+1)
  have hK : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hKsq : K^2 = 2*|M^2-m₂|+1 := Real.sq_sqrt (by positivity)
  have hlarge : 2*|M^2-m₂| ≤ K^2 := by rw [hKsq]; linarith
  let T := K^2+M^2
  let B := 2*Real.exp (a*M)/Real.pi
  let A := 2*Real.exp (a*M)/Real.pi^2
  let f := crossTailDensity a M m₂
  let L := |verifyCrossResidue a M m₂| + ∫ s in Iic T, f s
  let Llog := |Real.log (a^2)| + Real.log (1+M^2/K^2)
  have hL : 0 ≤ L := add_nonneg (abs_nonneg _)
    (setIntegral_nonneg measurableSet_Iic (fun s _ => crossTailDensity_nonneg a M m₂ s))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoeff : B*(2/Real.pi) = 2*A := by dsimp [B, A]; ring
  have hlog : 0 ≤ Llog := by
    dsimp [Llog]
    exact add_nonneg (abs_nonneg _) (Real.log_nonneg (le_add_of_nonneg_right (by positivity)))
  have hmT : m₂ ≤ T := by
    change m₂ ≤ K^2+M^2
    rw [hKsq]
    linarith [neg_abs_le (M^2-m₂), abs_nonneg (M^2-m₂)]
  obtain ⟨C,hC,hCbound⟩ := crossTailDensity_cutoff_error_bound (a:=a) hK hlarge
  obtain ⟨E,hE,hEbound⟩ := UV.ContinueCrossTailPeriodic.abs_sine_div_log_remainder_bound a K ha hK
  refine ⟨L+C+B*E+A*Llog, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with x hx
  have hX : 0 ≤ x-M^2 := by dsimp [T] at hx; linarith [sq_nonneg K]
  let R := Real.sqrt (x-M^2)
  have hRsq : R^2 = x-M^2 := Real.sq_sqrt hX
  have hKR : K ≤ R := by
    apply (sq_le_sq₀ hK.le (Real.sqrt_nonneg _)).1
    rw [hRsq]
    dsimp [T] at hx
    linarith
  have hxR : x = R^2+M^2 := by linarith
  have hcut : (crossTailVariation a M m₂).real (Iic x) = L+∫ s in Ioc T x, f s := by
    have hI := crossTailDensity_integrableOn_Iic ha hm₂ hadm x
    rw [crossTailVariation_cutoff_eq ha hm₂ hadm (hmT.trans hx), ← Iic_union_Ioc_eq_Iic hx,
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (hI.mono_set (Iic_subset_Iic.mpr hx)) (hI.mono_set Ioc_subset_Iic_self)]
    exact (add_assoc _ _ _).symm
  let P := ∫ k in K..R, |Real.sin (a*k)|/k
  have h₁ : |(∫ s in Ioc T x, f s)-B*P| ≤ C := by
    rw [hxR]
    exact hCbound R hKR
  have h₂ : |B*P - 2*A*Real.log R| ≤ B*E := by
    rw [← hcoeff, mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left (hEbound R hKR) hB
  have h₃ : |2*A*Real.log R-A*Real.log (a^2*x)| ≤ A*Llog := by
    rw [show 2*A*Real.log R = A*(2*Real.log R) by ring, ← mul_sub, abs_mul, abs_of_nonneg hA, hxR]
    exact mul_le_mul_of_nonneg_left (crossTail_log_coordinate_bound ha hK hKR) hA
  rw [hcut]
  change |L+(∫ s in Ioc T x, f s)-A*Real.log (a^2*x)| ≤ _
  rw [add_sub_assoc]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hL]
  have hfour := (abs_sub_le (∫ s in Ioc T x, f s) (B*P) (A*Real.log (a^2*x))).trans
    (add_le_add h₁ ((abs_sub_le (B*P) (2*A*Real.log R) (A*Real.log (a^2*x))).trans
      (add_le_add h₂ h₃)))
  linarith

/-- The source uses the interval `[0,x]`; the signed spectral variation is
concentrated in nonnegative mass squared. -/
theorem crossTailVariation_nonnegative_cutoff_sharp_log {a M m₂ : ℝ} (ha : 0 < a)
    (hm₂ : 0 ≤ m₂) (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    ∃ C ≥ 0, ∀ᶠ x : ℝ in atTop,
      |(crossTailVariation a M m₂).real (Icc 0 x) -
        (2*Real.exp (a*M)/Real.pi^2)*Real.log (a^2*x)| ≤ C := by
  simpa only [crossTailVariation_cutoff_Icc_eq_Iic hm₂] using
    crossTailVariation_cutoff_sharp_log ha hm₂ hadm

/-- The exact coefficient in the source's (D_c(x)) asymptotic and a
genuine (O(x^{-1})) remainder. No minimum depth or mass-gap premise is
added to the manuscript's ordinary signed spectral admission criterion. -/
theorem crossTailTransform_sharp_log {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    (fun x : ℝ => crossTailTransform a M m₂ x -
      (2*Real.exp (a*M)/Real.pi^2)*Real.log (a^2*x)/x) =O[atTop] (fun x : ℝ => x⁻¹) := by
  obtain ⟨B,hB,hB'⟩ := crossTailTransform_cutoff_bound ha hm₂ hadm
  obtain ⟨C,hC,hC'⟩ := crossTailVariation_cutoff_sharp_log ha hm₂ hadm
  refine Asymptotics.IsBigO.of_bound (B+C) ?_
  filter_upwards [hB',hC',eventually_gt_atTop (0:ℝ)] with x hcut hlog hx
  let A := 2*Real.exp (a*M)/Real.pi^2
  have hmain : |x*crossTailTransform a M m₂ x - A*Real.log (a^2*x)| ≤ B+C :=
    (abs_sub_le _ ((crossTailVariation a M m₂).real (Iic x)) _).trans (add_le_add hcut hlog)
  have he : crossTailTransform a M m₂ x - A*Real.log (a^2*x)/x =
      (x*crossTailTransform a M m₂ x - A*Real.log (a^2*x))/x := by
    field_simp
  change ‖crossTailTransform a M m₂ x - A*Real.log (a^2*x)/x‖ ≤ (B+C)*‖x⁻¹‖
  rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hx,
    Real.norm_of_nonneg (inv_nonneg.mpr hx.le), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hmain hx.le

end UV.RevisionSpectrum

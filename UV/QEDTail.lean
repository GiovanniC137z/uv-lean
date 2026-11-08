import UV.WardCommonCutoff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The finite-momentum converse in the bare QED integrability criterion.
The only integrability assumption concerns the original tensor components. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise

namespace UV

theorem qedTail_square_image_Ioi : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    change 0 < r at hr
    exact sq_pos_of_pos hr
  · intro hu
    change 0 < u at hu
    exact ⟨Real.sqrt u, Real.sqrt_pos.mpr hu, Real.sq_sqrt hu.le⟩

theorem qedTail_integrableOn_square_substitution (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => 2 * r * g (r ^ 2)) (Ioi 0) := by
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun r : ℝ => r ^ 2) (f' := fun r : ℝ => 2 * r)
    measurableSet_Ioi (fun r _ => (show HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r from
      by simpa using (hasDerivAt_id r).pow 2).hasDerivWithinAt)
    (show InjOn (fun r : ℝ => r ^ 2) (Ioi 0) from
      fun r hr s hs hrs => (sq_eq_sq₀ hr.le hs.le).mp hrs) g
  rw [qedTail_square_image_Ioi] at hh
  apply hh.trans
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only
  rw [abs_of_pos (by positivity : 0 < 2 * r), smul_eq_mul]

/-- A regular denominator at the origin is enough to recover the exact
one-dimensional square-integrability criterion through polar coordinates. -/
theorem qedTail_square_integrable_of_regularized_radial {F : ℝ → ℝ}
    (hF : Continuous F)
    (hR : Integrable (fun k : DiracMomentum => F (‖k‖ ^ 2) ^ 2 / (1 + ‖k‖ ^ 2))) :
    IntegrableOn (fun u => F u ^ 2) (Ioi 0) := by
  have hr : IntegrableOn
      (fun r : ℝ => r ^ 3 * (F (r ^ 2) ^ 2 / (1 + r ^ 2))) (Ioi 0) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] using
      (integrable_fun_norm_addHaar (E := DiracMomentum) volume
        (f := fun r : ℝ => F (r ^ 2) ^ 2 / (1 + r ^ 2))).mp hR
  have hg : Continuous (fun r : ℝ => r * F (r ^ 2) ^ 2) := by fun_prop
  have hlocal : IntegrableOn (fun r : ℝ => r * F (r ^ 2) ^ 2) (Icc 0 1) :=
    hg.continuousOn.integrableOn_compact isCompact_Icc
  have htail : IntegrableOn (fun r : ℝ => r * F (r ^ 2) ^ 2) (Ioi 1) := by
    apply ((hr.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).const_mul 2).mono'
      hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 1 < r at hr
    have hr0 : 0 ≤ r := by linarith
    have hden : 0 < 1 + r ^ 2 := by positivity
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    have hr3 : r ≤ r ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hr2 hr0]
    have hb : r ≤ 2 * r ^ 3 / (1 + r ^ 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0 (sq_nonneg _))]
    calc
      r * F (r ^ 2) ^ 2 ≤ (2 * r ^ 3 / (1 + r ^ 2)) * F (r ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hb (sq_nonneg _)
      _ = 2 * (r ^ 3 * (F (r ^ 2) ^ 2 / (1 + r ^ 2))) := by ring
  have hgIoi : IntegrableOn (fun r : ℝ => r * F (r ^ 2) ^ 2) (Ioi 0) :=
    (hlocal.union htail).mono_set (by
      intro r hr
      by_cases h : r ≤ 1
      · exact Or.inl ⟨hr.le, h⟩
      · exact Or.inr (lt_of_not_ge h))
  apply (qedTail_integrableOn_square_substitution (fun u => F u ^ 2)).mpr
  change Integrable (fun r : ℝ => 2 * r * F (r ^ 2) ^ 2) (volume.restrict (Ioi 0))
  exact (hgIoi.const_mul (2 : ℝ)).congr (Eventually.of_forall (fun r => by ring))

/-- The scaled diagonal trace forces integrability of a radial envelope.
The regular denominator makes the argument valid also at zero mass. -/
theorem laplace_bare_ward_regularized_envelope_integrable (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 ≤ m)
    (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν)) :
    Integrable (fun k : DiracMomentum =>
      wardLaplaceKernel ρ 1 (‖k‖ ^ 2) ^ 2 / (1 + ‖k‖ ^ 2)) := by
  let G : DiracMomentum → ℝ := fun k =>
    wardLaplaceKernel ρ 1 (‖k‖ ^ 2) ^ 2 / (1 + ‖k‖ ^ 2)
  have hG : Continuous G := by
    dsimp [G]
    apply Continuous.div
    · exact ((wardLaplaceKernel_continuous ρ hp 1).comp (by fun_prop)).pow 2
    · fun_prop
    · intro k
      positivity
  have hsum : Integrable (fun k : DiracMomentum => ∑ μ,
      bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ k) :=
    integrable_finset_sum _ (fun μ _ => hH μ μ)
  have hmajor : Integrable (fun k : DiracMomentum =>
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖) :=
    (hsum.comp_smul (by norm_num : (1 / 8 : ℝ) ≠ 0)).norm
  let K : ℝ := 16 * ‖Q‖ + 8 * m + 1
  have hlocal : IntegrableOn G (closedBall (0 : DiracMomentum) K) :=
    hG.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have htail : IntegrableOn G (closedBall (0 : DiracMomentum) K)ᶜ := by
    apply hmajor.integrableOn.mono' hG.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with k hk
    have hknorm : K < ‖k‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hk
    have hkpos : 0 < ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hQk : 16 * ‖Q‖ ≤ ‖k‖ := by dsimp [K] at hknorm; linarith
    have hmk : 8 * m ≤ ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hF0 (u : ℝ) : 0 ≤ laplace ρ u := integral_nonneg (fun _ => Real.exp_nonneg _)
    have hmono := nonnegative_laplace_antitone ρ hp
      (show 0 ≤ ‖k‖ ^ 2 / 8 by positivity)
      (show ‖k‖ ^ 2 / 8 ≤ ‖k‖ ^ 2 by nlinarith [sq_nonneg ‖k‖])
    have hsq : laplace ρ (‖k‖ ^ 2) ^ 2 ≤ laplace ρ (‖k‖ ^ 2 / 8) ^ 2 :=
      pow_le_pow_left₀ (hF0 _) hmono 2
    have hcoeff : 1 / (1 + ‖k‖ ^ 2) ≤ 32 / ‖k‖ ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ‖k‖]
    have hbound := mul_le_mul hcoeff hsq (sq_nonneg _) (by positivity : 0 ≤ 32 / ‖k‖ ^ 2)
    have hnonneg : 0 ≤ G k := by dsimp [G]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp [G]
    rw [wardLaplaceKernel_eq ρ 1 (sq_nonneg _)]
    simp only [one_pow, one_mul]
    calc
      _ = (1 / (1 + ‖k‖ ^ 2)) * laplace ρ (‖k‖ ^ 2) ^ 2 := by ring
      _ ≤ _ := hbound
      _ ≤ _ := laplace_bare_ward_scaled_tensor_lower ρ hp hm Q k hkpos hQk hmk
  have hall := hlocal.union htail
  simpa only [union_compl_self, integrableOn_univ] using hall

/-- Finite absolute integrability of the original bare tensor at any real
external momentum implies the exact radial square-integrability criterion.
This includes the massless case and retains the literal dimensional scale. -/
theorem wardLaplaceKernel_square_integrable_of_tensor (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν)) :
    IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0) := by
  rw [wardLaplaceKernel_pushforward] at hH ⊢
  let σ := ρ.map (fun τ : ℝ => a ^ 2 * τ)
  have hσ : ∀ᵐ τ ∂σ, 0 ≤ τ := ward_heat_support_nonnegative ρ hp a
  exact qedTail_square_integrable_of_regularized_radial
    (wardLaplaceKernel_continuous σ hσ 1)
    (laplace_bare_ward_regularized_envelope_integrable σ hσ hm Q hH)

end UV

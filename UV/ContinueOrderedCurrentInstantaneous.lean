import UV.ContinueOrderedCurrentOverlap
import UV.ContinueOrderedEnvelopeSewing
import Mathlib.Probability.Distributions.Gaussian.Real

/-! At each fixed spatial transfer, inverse Fourier integration in the
carrier frequency recovers the charge-density square in carrier time.
The time density is the signed sum of the actual occupied intervals. -/

noncomputable section

open MeasureTheory Finset Set ProbabilityTheory
open scoped ComplexConjugate RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

private def window (a b : ℝ) : ℝ → ℂ := (Ioc a b).indicator (fun _ => 1)

private theorem window_product (a b c u : ℝ) :
    window a b u * window a c u = window a (min b c) u := by
  simp only [window,Set.indicator_apply,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all

private theorem window_integrable (a b : ℝ) : Integrable (window a b) :=
  (integrableOn_const (C := (1:ℂ)) (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

private theorem window_integral {a b : ℝ} (hab : a ≤ b) : (∫ u, window a b u) = ((b-a:ℝ):ℂ) := by
  simp [window,Real.volume_real_Ioc,hab,Complex.real_smul]

/-- Signed indicator of a directed carrier interval. -/
def occupation (b₀ b₁ u : ℝ) : ℂ :=
  (if u ≤ b₁ then 1 else 0) - (if u ≤ b₀ then 1 else 0)

theorem occupation_anchor {a b c : ℝ} (hb : a ≤ b) (hc : a ≤ c) (u : ℝ) :
    occupation b c u = window a c u-window a b u := by
  by_cases hu : a < u
  · simp [occupation,window,Set.indicator_apply,hu]
  · have h := le_of_not_gt hu
    simp [occupation,window,hu,h.trans hb,h.trans hc]

theorem occupation_pair (b₀ b₁ c₀ c₁ : ℝ) :
    Integrable (fun u => occupation b₀ b₁ u*occupation c₀ c₁ u) ∧
      (∫ u, occupation b₀ b₁ u*occupation c₀ c₁ u) = (signedOverlap b₀ b₁ c₀ c₁:ℂ) := by
  let a := min (min b₀ b₁) (min c₀ c₁)
  have hb₀ : a ≤ b₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hb₁ : a ≤ b₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc₀ : a ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₁ : a ≤ c₁ := (min_le_right _ _).trans (min_le_right _ _)
  have he (u : ℝ) : occupation b₀ b₁ u*occupation c₀ c₁ u =
      window a (min b₁ c₁) u - window a (min b₁ c₀) u - window a (min b₀ c₁) u + window a (min b₀ c₀) u := by
    rw [occupation_anchor hb₀ hb₁,occupation_anchor hc₀ hc₁]
    simp only [mul_sub,sub_mul,window_product]
    ring
  simp only [he]
  have hi : Integrable (fun u => window a (min b₁ c₁) u - window a (min b₁ c₀) u) :=
    (window_integrable _ _).sub (window_integrable _ _)
  have hj : Integrable (fun u => window a (min b₁ c₁) u - window a (min b₁ c₀) u - window a (min b₀ c₁) u) :=
    hi.sub (window_integrable _ _)
  refine ⟨hj.add (window_integrable _ _),?_⟩
  rw [integral_add hj (window_integrable _ _),integral_sub hi (window_integrable _ _),
    integral_sub (window_integrable _ _) (window_integrable _ _),window_integral (le_min hb₁ hc₁),
    window_integral (le_min hb₁ hc₀),window_integral (le_min hb₀ hc₁),window_integral (le_min hb₀ hc₀)]
  simp only [signedOverlap,Complex.ofReal_add,Complex.ofReal_sub]
  ring

/-- Between hopping times each signed charge sits at its own spatial vertex. -/
def timeDensity (P : OrderedTwoBandPath) (u : ℝ) (p : Spatial) : ℂ :=
  ∑ j ∈ range P.hops, spatialWave p (P.position j)*occupation (P.time j) (P.time (j+1)) u

theorem time_density_pair (P R : OrderedTwoBandPath) (p : Spatial) :
    Integrable (fun u => P.timeDensity u p*R.timeDensity u (-p)) ∧
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, P.density ω p*R.density (-ω) (-p)) =
      ∫ u, P.timeDensity u p*R.timeDensity u (-p) := by
  let W := fun j k => spatialWave p (P.position j)*spatialWave (-p) (R.position k)
  let F := fun j k (u : ℝ) => W j k * (occupation (P.time j) (P.time (j+1)) u *
    occupation (R.time k) (R.time (k+1)) u)
  have hF (j k : ℕ) : Integrable (F j k) := (occupation_pair ..).1.const_mul _
  have he (u : ℝ) : P.timeDensity u p*R.timeDensity u (-p) =
      ∑ j ∈ range P.hops, ∑ k ∈ range R.hops, F j k u := by
    rw [timeDensity,timeDensity,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _
  have hj (j : ℕ) : Integrable (fun u => ∑ k ∈ range R.hops, F j k u) :=
    integrable_finset_sum _ (fun k _ => hF j k)
  simp only [he]
  refine ⟨integrable_finset_sum _ (fun j _ => hj j),?_⟩
  rw [(P.density_pair_covariance R p).2,integral_finset_sum _ (fun j _ => hj j)]
  apply sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => hF j k)]
  apply sum_congr rfl
  intro k _
  simp only [F,W,integral_const_mul,(occupation_pair ..).2]

theorem time_density_opposite (P : OrderedTwoBandPath) (u : ℝ) (p : Spatial) :
    P.timeDensity u (-p) = conj (P.timeDensity u p) := by
  unfold timeDensity
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  simp only [map_mul,spatialWave,inner_neg_left,Complex.ofReal_neg,←Complex.exp_conj,map_sub,occupation]
  split_ifs <;> simp [mul_comm]

theorem coulomb_time_square (P : OrderedTwoBandPath) (a : ℝ) (p : Spatial) :
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, OrderedPhotonKind.coulomb.sewn a P P (ω,p)) =
      (Real.exp (-(2*a*‖p‖))/‖p‖^2:ℝ) * ((∫ u, Complex.normSq (P.timeDensity u p)):ℝ) := by
  simp only [OrderedPhotonKind.sewn,integral_const_mul]
  rw [mul_left_comm,(P.time_density_pair P p).2]
  congr 1
  simp only [P.time_density_opposite,Complex.mul_conj]
  exact integral_complex_ofReal

end UV.SectorPlane.OrderedTwoBandPath

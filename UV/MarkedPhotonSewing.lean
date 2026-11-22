import UV.MarkedPhotonMonomial
import UV.RevisionSpectrumSewing

/-! Absolute integrability of the continuum contraction after marking an
oriented pair in a finite collection of complete photon pairings. -/

noncomputable section

namespace UV.MarkedPhoton

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

variable {X Y Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Each marked first slot specifies an entire pair in its parent pairing.
Every coordinate change carries the integration measure of that same parent. -/
def sewnMarks (s : Finset J) (r : J → ℕ) (A : J → Ω → ℝ)
    (e : (j : J) → Fin (r j) → X × Y ≃ᵐ Ω) (ν : Measure Y) (x : X) : ℝ :=
  ∑ j ∈ s, ∑ i : Fin (r j), ∫ y, A j (e j i (x,y)) ∂ν

theorem marked_sewing_absolute (s : Finset J) (r : J → ℕ) (A : J → Ω → ℝ)
    (e : (j : J) → Fin (r j) → X × Y ≃ᵐ Ω) (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (ρ : J → Measure Ω) (he : ∀ j ∈ s, ∀ i, MeasurePreserving (e j i) (μ.prod ν) (ρ j))
    (hA : ∀ j ∈ s, Integrable (A j) (ρ j)) :
    Integrable (sewnMarks s r A e ν) μ ∧
    (∫ x, ‖sewnMarks s r A e ν x‖ ∂μ) ≤ ∑ j ∈ s, (r j : ℝ) * ∫ w, ‖A j w‖ ∂ρ j := by
  have H (j : J) (hj : j ∈ s) (i : Fin (r j)) : Integrable (fun z => A j (e j i z)) (μ.prod ν) :=
    (he j hj i).integrable_comp_of_integrable (hA j hj)
  have hnorm (j : J) (hj : j ∈ s) (i : Fin (r j)) := (H j hj i).integral_norm_prod_left
  have hpair (j : J) (hj : j ∈ s) (i : Fin (r j)) :
      (∫ x, ∫ y, ‖A j (e j i (x,y))‖ ∂ν ∂μ) = ∫ w, ‖A j w‖ ∂ρ j := by
    rw [← integral_prod (fun z : X × Y => ‖A j (e j i z)‖) (H j hj i).norm]
    exact (he j hj i).integral_comp' (fun w => ‖A j w‖)
  have hi : Integrable (sewnMarks s r A e ν) μ :=
    integrable_finset_sum s (fun j hj => integrable_finset_sum Finset.univ (fun i _ => (H j hj i).integral_prod_left))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, ∑ j ∈ s, ∑ i : Fin (r j), ∫ y, ‖A j (e j i (x,y))‖ ∂ν ∂μ := by
      apply integral_mono hi.norm (integrable_finset_sum s (fun j hj =>
        integrable_finset_sum Finset.univ (fun i _ => hnorm j hj i)))
      intro x
      exact (norm_sum_le s _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le Finset.univ _).trans
        (Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _))
    _ = _ := by
      rw [integral_finset_sum s (fun j hj => integrable_finset_sum Finset.univ (fun i _ => hnorm j hj i))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum Finset.univ (fun i _ => hnorm j hj i)]
      simp_rw [hpair j hj]
      simp

/-- A measured radial Hessian identical to the specified direct positive-band
sewing cannot have an absolutely integrable parent at every marking. -/
theorem positive_band_excludes_marked_sewing (s : Finset J) (r : J → ℕ) (A : J → Ω → ℝ)
    (e : (j : J) → Fin (r j) → ℝ × Y ≃ᵐ Ω) (ν : Measure Y) [SFinite ν] (ρ : J → Measure Ω)
    (spectrum : Measure ℝ) (D : ℝ → ℝ) {s₀ s₁ c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hb : s₁ ≤ R) (hs : ∀ᵐ t ∂spectrum, 0 ≤ t) (hm : spectrum (Icc s₀ s₁) ≠ ⊤)
    (hp : spectrum (Icc s₀ s₁) ≠ 0) (hD : ∀ X ≥ R, c/X ≤ D X)
    (hI : ∀ X ≥ R, Integrable (fun t => X/(t+X)) spectrum)
    (he : ∀ j ∈ s, ∀ i, MeasurePreserving (e j i) ((volume.restrict (Ioi R)).prod ν) (ρ j))
    (hid : sewnMarks s r A e ν =ᵐ[volume.restrict (Ioi R)] fun X => X * D X * ∫ t, X/(t+X) ∂spectrum) :
    ∃ j ∈ s, ¬Integrable (A j) (ρ j) := by
  by_contra! hall
  have h := (marked_sewing_absolute s r A e _ ν ρ he hall).1.congr hid
  exact UV.RevisionSpectrum.positive_band_unsubtracted_sewing_diverges spectrum D hs hc hR hb hm hp hD hI h

end UV.MarkedPhoton

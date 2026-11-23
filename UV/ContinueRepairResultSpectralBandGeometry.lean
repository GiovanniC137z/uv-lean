import UV.ContinueRepairResultBoostTail

/-! Passage from the full positive spectral tensor measure to its compact
invariant-mass band. Nonzero trace measure on the band supplies a
compact set of nonzero integrated tensor weight; the full Lorentz law
induces precisely the compact-set congruence used in the two no-go proofs. -/

noncomputable section
open Set MeasureTheory Metric Matrix
open scoped ENNReal Matrix ComplexOrder

namespace UV.ContinuationBoostSpectrum

def currentSpectralBand (s₁ s₂ : ℝ) : Set CurrentMomentum :=
  (fun k => k.1^2-‖k.2‖^2) ⁻¹' Icc s₁ s₂

theorem currentSpectralBand_closed (s₁ s₂ : ℝ) : IsClosed (currentSpectralBand s₁ s₂) :=
  isClosed_Icc.preimage ((continuous_fst.pow 2).sub (continuous_snd.norm.pow 2))

theorem currentBoost_continuous (i : Fin 3) (b : ℝ) : Continuous (currentBoost i b) := by
  apply Continuous.prodMk
  · exact (continuous_const.mul continuous_fst).add
      (continuous_const.mul ((PiLp.continuous_apply 2 _ i).comp continuous_snd))
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro j
    by_cases h : j=i
    · subst j
      simp only [Function.update_self]
      exact (continuous_const.mul continuous_fst).add
        (continuous_const.mul ((PiLp.continuous_apply 2 _ i).comp continuous_snd))
    · simp only [Function.update_of_ne h]
      exact (PiLp.continuous_apply 2 _ j).comp continuous_snd

/-- A compact spectral set of strictly positive trace exists whenever
a closed invariant band has nonzero trace measure, including bands
with singular or atomic scalar spectrum. -/
theorem nonzero_compact_in_spectral_band (σ : Measure CurrentMomentum) [IsFiniteMeasureOnCompacts σ]
    {s₁ s₂ : ℝ} (hσ : σ (currentSpectralBand s₁ s₂) ≠ 0) :
    ∃ K : Set CurrentMomentum, IsCompact K ∧ K ⊆ currentSpectralBand s₁ s₂ ∧ 0 < σ.real K := by
  let B := currentSpectralBand s₁ s₂
  have hBC := currentSpectralBand_closed s₁ s₂
  have he : B = ⋃ n : ℕ, B ∩ closedBall 0 (n:ℝ) := by rw [←inter_iUnion,iUnion_closedBall_nat,inter_univ]
  have hn : ∃ n : ℕ, σ (B ∩ closedBall 0 (n:ℝ)) ≠ 0 := by
    by_contra! h
    exact hσ (he ▸ (measure_iUnion_null_iff.mpr h) : σ B=0)
  obtain ⟨n,hn⟩ := hn
  have hc : IsCompact (B ∩ closedBall 0 (n:ℝ)) := (isCompact_closedBall _ _).inter_left hBC
  exact ⟨_,hc,inter_subset_left,ENNReal.toReal_pos hn (hc.measure_lt_top.ne)⟩

theorem restricted_time_boost (μ : Measure CurrentMomentum) {s₁ s₂ : ℝ}
    {K : Set CurrentMomentum} (hK : IsCompact K) (hKB : K ⊆ currentSpectralBand s₁ s₂)
    (i : Fin 3) (b : ℝ) :
    (μ.restrict (currentSpectralBand s₁ s₂)).real (currentBoost i b '' K) = μ.real (currentBoost i b '' K) := by
  have hsub : currentBoost i b '' K ⊆ currentSpectralBand s₁ s₂ := by
    rintro _ ⟨k,hk,rfl⟩
    change (currentBoost i b k).1^2-‖(currentBoost i b k).2‖^2 ∈ Icc s₁ s₂
    rw [currentBoost_preserves_mass]
    exact hKB hk
  rw [Measure.real,Measure.restrict_apply (hK.image (currentBoost_continuous i b)).measurableSet,
    inter_eq_left.mpr hsub,Measure.real]

/-- Positive nonzero trace on a timelike band is impossible when a
covariant current has the canonical identity-shift marginal, in any
finite number of slots. -/
theorem finite_slot_no_positive_timelike_trace {E : Type*} [Norm E] {d : ℕ} (diamond : SectorPlane.Plane E)
    (P : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (h₀ : P₀ᴴ=P₀) (h₀₀ : P₀*P₀=P₀) (hm : ∀ i j, Measurable (fun k => P diamond k i j))
    (ha : ∀ k, (P diamond k)ᴴ = P diamond k) (hi : ∀ k, P diamond k*P diamond k=P diamond k)
    (hL : Integrable (fun k => chargeInclusiveSquare (P diamond k-P₀)))
    (μ σ : Measure CurrentMomentum) [IsFiniteMeasureOnCompacts σ]
    (hMarg : Measure.map Prod.snd μ = volume.withDensity (fun p => ENNReal.ofReal (canonicalDensity (P diamond) p)))
    (T : Set CurrentMomentum → DiracMatrix) (hT : ∀ K, IsCompact K → (T K).PosSemidef)
    (hTrace : ∀ K, IsCompact K → (T K).trace.re = σ.real K)
    (hCov : ∀ K, IsCompact K → ∀ i b, μ.real (currentBoost i b '' K) =
      (boostTimeRow i b ⬝ᵥ (T K *ᵥ boostTimeRow i b)).re) (s₁ s₂ : ℝ) :
    σ (currentSpectralBand s₁ s₂) = 0 := by
  by_contra hσ
  obtain ⟨K,hK,_,hp⟩ := nonzero_compact_in_spectral_band σ hσ
  have hz := finite_slot_lorentz_spectral_tensor_vanishes diamond P P₀ h₀ h₀₀ hm ha hi hL μ hMarg hK (T K) (hT K hK) (hCov K hK)
  rw [←hTrace K hK,hz,Matrix.trace_zero,Complex.zero_re] at hp
  exact hp.false

end UV.ContinuationBoostSpectrum

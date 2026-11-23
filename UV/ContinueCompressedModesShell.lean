import UV.ContinueCompressedModes
import UV.ContinueFiveBallSharp

/-! Actual A4 charged circulation estimates at every insertion count. The
normal mode is a freely summed integer at each closed loop. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator ENNReal

namespace UV

variable {ι : Type*} [Fintype ι]

theorem compressed_full_readout_cubic (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : WilsonBallSpace ι, ‖normalShellCharacteristic a‖ ≤ B/(1+‖a‖)^3 := by
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  exact normal_shell_characteristic_cubic ι hd

theorem compressed_actual_line_decay {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ (u : UnitVector OSFourSpace) p,
      ‖compressedMarkedLine m L T ξ u p‖ ≤ C/(1+L*‖normalBallJoin ξ p‖)^7 := by
  obtain ⟨B,hB,h⟩ := compressed_full_readout_cubic T
  exact compressed_line_radial_bound hm hL T hB h

/-- With a (K−1)-dimensional shell the complete marked internal line
has precisely the manuscript's inverse (K+1)-power majorant. -/
theorem compressed_actual_line_sharp {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ (u : UnitVector OSFourSpace) p,
      ‖compressedMarkedLine m L T ξ u p‖ ≤ C/(1+L*‖normalBallJoin ξ p‖)^(Fintype.card ι+2) := by
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  obtain ⟨B,hB,hh⟩ := normal_shell_pair_sharp ι (by omega)
  refine ⟨B*(m⁻¹+L),by positivity,fun ξ u p => ?_⟩
  let P := normalBallJoin ξ p
  let X := 1+L*‖P‖
  have h := hh (L • T P)
  rw [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le] at h
  have hf : |normalLegForm L T ξ p|^2 ≤ B/X^(Fintype.card ι+1) :=
    (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2).trans h
  apply (compressed_line_norm_le m L T ξ u p).trans
  apply (mul_le_mul hf (compressed_frequency_radial_bound hm hL ξ p) (norm_nonneg _) (by dsimp [X]; positivity)).trans_eq
  rw [div_mul_div_comm,pow_succ _ (Fintype.card ι+1)]

theorem compressed_loop_volume_budget {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin (n+1) → UnitVector OSFourSpace) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ξ : ℝ) (s : Fin (n+1) → OSFourSpace),
      let F := fun k => compressedLoopTrace m L T ξ u (fun i => k+s i)
      Integrable F ∧ (∫ k, ‖F k‖) ≤ B*normalPhotonWeight 2 ξ :=
  compressed_loop_budget_of_decay hm hL T u volume compressed_volume_carrier_bound (compressed_full_readout_cubic T)

theorem compressed_loop_lattice_budget (b : NormalReciprocalBasis) {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin (n+1) → UnitVector OSFourSpace) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ξ : ℝ) (s : Fin (n+1) → OSFourSpace),
      let F := fun k => compressedLoopTrace m L T ξ u (fun i => k+s i)
      Integrable F (normalLatticeMeasure b) ∧ (∫ k, ‖F k‖ ∂normalLatticeMeasure b) ≤ B*normalPhotonWeight 2 ξ :=
  compressed_loop_budget_of_decay hm hL T u _ (compressed_lattice_carrier_bound b) (compressed_full_readout_cubic T)

/-- At each vertex the incoming and outgoing leg have their own compression.
The successor is any permutation, in particular the directed cyclic successor.
All matrix factors retain their original order in the trace. -/
theorem compressed_cyclic_vertex_trace {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) (next : Equiv.Perm (Fin (n+1))) :
    let f := fun j => (normalLegForm L T ξ (p j) : ℂ)
    let V := fun j => (Complex.I*f j*f (next j)) • diracSlash (u j).val
    (normalOrderedWord (fun j => normalDiracFrequency m (p j) ξ*V j)).trace = compressedLoopTrace m L T ξ u p := by
  let f := fun j => (normalLegForm L T ξ (p j) : ℂ)
  let A := fun j => normalDiracFrequency m (p j) ξ*diracSlash (u j).val
  change (normalOrderedWord (fun j => normalDiracFrequency m (p j) ξ*((Complex.I*f j*f (next j)) • diracSlash (u j).val))).trace =
    (normalOrderedWord (fun j => (Complex.I*(f j)^2) • A j)).trace
  simp only [mul_smul_comm,normal_ordered_word_smul,Finset.prod_mul_distrib,pow_two,mul_assoc,A]
  rw [Equiv.prod_comp next f]

private theorem compressed_fubini {X : Type*} [MeasurableSpace X] (σ : Measure X) [SFinite σ]
    (F : ℤ × X → ℂ) (hF : Measurable F) (g : ℤ → ℝ) (hg : Integrable g Measure.count)
    (hi : ∀ j : ℤ, Integrable (fun k => F (j,k)) σ) (hle : ∀ j : ℤ, (∫ k, ‖F (j,k)‖ ∂σ) ≤ g j) :
    Integrable F ((Measure.count : Measure ℤ).prod σ) ∧ (∫ z, ‖F z‖ ∂(Measure.count : Measure ℤ).prod σ) ≤ ∫ j, g j ∂Measure.count := by
  have hI : Integrable (fun j => ∫ k, ‖F (j,k)‖ ∂σ) Measure.count := hg.mono' (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun j => by simpa only [Real.norm_of_nonneg (integral_nonneg (fun k => norm_nonneg (F (j,k))))] using hle j)
  have hJ : Integrable F ((Measure.count : Measure ℤ).prod σ) :=
    (integrable_prod_iff hF.aestronglyMeasurable).mpr ⟨Eventually.of_forall hi,hI⟩
  refine ⟨hJ,?_⟩
  rw [integral_prod _ hJ.norm]
  exact integral_mono hI hg hle

/-- Integrated norm on the entire normal-mode/carrier product, uniformly
in even mode-dependent carrier shifts. The measure may be Euclidean volume
or the counting measure on an arbitrary full reciprocal four-lattice. -/
theorem compressed_loop_all_modes {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin (n+1) → UnitVector OSFourSpace)
    (σ : Measure OSFourSpace) [SFinite σ] (hσ : CompressedCarrierBound σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℤ → Fin (n+1) → OSFourSpace,
      let F := fun z : ℤ × OSFourSpace => compressedLoopTrace m L T (normalLegFrequency L θ z.1) u (fun i => z.2+s z.1 i)
      let μ := (Measure.count : Measure ℤ).prod σ
      Integrable F μ ∧ (∫ z, ‖F z‖ ∂μ) ≤ M := by
  obtain ⟨B,hB,h⟩ := compressed_loop_budget_of_decay hm hL T u σ hσ (compressed_full_readout_cubic T)
  let w := fun j => normalPhotonWeight 2 (normalLegFrequency L θ j)
  have hw (j) : 0 ≤ w j := by dsimp [w,normalPhotonWeight]; positivity
  have hs := (normal_shifted_frequency_summable hL θ).mul_left B
  have hib : Integrable (fun j => B*w j) (Measure.count : Measure ℤ) := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (mul_nonneg hB (hw _))] using hs
  refine ⟨∫ j, B*w j ∂Measure.count,integral_nonneg (fun j => mul_nonneg hB (hw j)),fun s => ?_⟩
  let F := fun z : ℤ × OSFourSpace => compressedLoopTrace m L T (normalLegFrequency L θ z.1) u (fun i => z.2+s z.1 i)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro j
    exact compressed_loop_measurable hm L T (normalLegFrequency L θ j) u (p := fun k i => k+s j i) (fun i => measurable_id.add_const (s j i))
  exact compressed_fubini σ F hF (fun j => B*w j) hib (fun j => (h (normalLegFrequency L θ j) (s j)).1)
    (fun j => (h (normalLegFrequency L θ j) (s j)).2)

end UV

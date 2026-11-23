import UV.ContinueThinCurrentTrace

/-! The exact positive slice coefficient for the smooth radial window. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators InnerProductSpace Topology ENNReal NNReal

namespace UV

def thinStandardBasis : ThinCurrentBasis := EuclideanSpace.basisFun (Fin 4) ℝ

/-- The coefficient (c_\varphi), integrated with three-dimensional
Lebesgue measure in the standard orthonormal transverse coordinates. -/
def thinWindowPerimeterCoefficient (φ : ThinCurrentPlane → ℝ) : ℝ :=
  (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * ∫ q : ThinFrequencyThree,
    φ (thinFrequencyPoint thinStandardBasis 0 q)

/-- Radiality is equality on each sphere in the physical plane. -/
def thinRadialWindow (φ : ThinCurrentPlane → ℝ) : Prop :=
  ∀ p q, ‖p‖ = ‖q‖ → φ p = φ q

private theorem thinCurrentBasis_first (v : ThinCurrentPlane) (h : ‖v‖ = 1) :
    ∃ b : ThinCurrentBasis, b 0 = v := by
  let vs : Fin 4 → ThinCurrentPlane := fun _ => v
  have horth : Orthonormal ℝ (({0} : Set (Fin 4)).restrict vs) := by
    rw [orthonormal_iff_ite]
    intro i j
    have he : i = j := Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
      (Set.mem_singleton_iff.mp j.2).symm)
    subst j
    simp [vs, real_inner_self_eq_norm_sq, h]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp [ThinCurrentPlane])
  exact ⟨b, hb 0 (Set.mem_singleton _)⟩

private theorem thinRadialWindow_slice_independent {φ : ThinCurrentPlane → ℝ}
    (hrad : thinRadialWindow φ) (b : ThinCurrentBasis) (s : ℝ) (q : ThinFrequencyThree) :
    φ (thinFrequencyPoint b s q) = φ (thinFrequencyPoint thinStandardBasis s q) := by
  apply hrad
  simp [thinFrequencyPoint]

private theorem thinWindow_compact_of_support {φ : ThinCurrentPlane → ℝ}
    (hs : ∀ p, φ p ≠ 0 → ‖p‖ < 2) : HasCompactSupport φ := by
  apply (isCompact_closedBall (0 : ThinCurrentPlane) 2).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro p hp
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (hs p hp).le)

private theorem thinWindow_real_bound {φ : ThinCurrentPlane → ℝ}
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, |φ p| ≤ B := by
  obtain ⟨B, hB, Hb⟩ := (hc.toSchwartzMap hsm).decay 0 0
  refine ⟨B, hB.le, ?_⟩
  intro p
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    using Hb p

private theorem thinWindow_slice_pos {φ : ThinCurrentPlane → ℝ}
    (hφ : Continuous φ) (hnn : ∀ p, 0 ≤ φ p) (hne : ∃ p, φ p ≠ 0)
    (hrad : thinRadialWindow φ) (hs : ∀ p, φ p ≠ 0 → ‖p‖ < 2) :
    0 < thinWindowPerimeterCoefficient φ := by
  let f : ThinFrequencyThree → ℝ := fun q => φ (thinFrequencyPoint thinStandardBasis 0 q)
  have hcont : Continuous f := by
    exact hφ.comp ((thinFrequencyPoint_continuous thinStandardBasis).comp (continuous_const.prodMk continuous_id))
  have hcs : HasCompactSupport f := by
    apply (isCompact_closedBall (0 : ThinFrequencyThree) 2).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro q hq
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (thinFrequency_norm_le thinStandardBasis 0 q).trans (hs _ hq).le
  obtain ⟨p, hp⟩ := hne
  let q : ThinFrequencyThree := fun i => if i = 0 then ‖p‖ else 0
  have hpoint : (WithLp.toLp 2 (Fin.cons 0 q) : ThinCurrentPlane) =
      EuclideanSpace.single (Fin.succ (0 : Fin 3)) ‖p‖ := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [EuclideanSpace.single_apply, Fin.cons_zero]
    · have hj : j.succ = (1 : Fin 4) ↔ j = 0 := by
        change j.succ = (0 : Fin 3).succ ↔ j = 0
        exact Fin.succ_inj
      simp [q, EuclideanSpace.single_apply, Fin.cons_succ, hj]
  have hq : f q ≠ 0 := by
    change φ (thinFrequencyPoint thinStandardBasis 0 q) ≠ 0
    rw [hrad _ p (by simp [thinFrequencyPoint, hpoint, EuclideanSpace.norm_single])]
    exact hp
  have hI : 0 < ∫ q : ThinFrequencyThree, f q :=
    integral_pos_of_integrable_nonneg_nonzero hcont
      (hcont.integrable_of_hasCompactSupport hcs) (fun q => hnn _) hq
  change 0 < (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * ∫ q : ThinFrequencyThree, f q
  exact mul_pos (by positivity) hI

/-- The exact perimeter limit of the original annular momentum shell.
Each supplied edge carries its actual arclength unit tangent. -/
theorem thinCurrentShell_radial_perimeter {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (hprep : thinCurrentPrepared edges)
    {φ : ThinCurrentPlane → ℝ} (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hnn : ∀ p, 0 ≤ φ p)
    (hrad : thinRadialWindow φ) (hs : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2) :
    Tendsto (fun R : ℝ => (thinCurrentShell edges φ R).toReal / R^3) atTop
      (𝓝 (thinWindowPerimeterCoefficient φ * thinCurrentPerimeter edges)) := by
  have hs' (p : ThinCurrentPlane) (hp : φ p ≠ 0) : ‖p‖ < 2 := (hs p hp).2
  have hc := thinWindow_compact_of_support hs'
  have hI : Integrable φ (volume : Measure ThinCurrentPlane) :=
    hsm.continuous.integrable_of_hasCompactSupport hc
  obtain ⟨B, _, hB⟩ := thinWindow_real_bound hsm hc
  obtain ⟨K, hK⟩ := thinWindowInverse_isSchwartz hsm hc
  obtain ⟨hvanish, dom, hdi, hdom⟩ := thinSchwartz_kernel_controls K
  refine thinCurrentShell_perimeter_of_line_trace edges hprep hsm.continuous hI hnn
    (by rw [hK]; exact K.continuous) (by rw [hK]; exact hvanish)
    (by rw [hK]; exact hdom) hdi ?_
  intro v hv
  obtain ⟨b, hb⟩ := thinCurrentBasis_first v hv
  rw [← hb, thinWindowInverse_lineTrace b hsm.continuous hI hB hs' ⟨K,hK⟩]
  unfold thinFrequencyMarginal thinWindowPerimeterCoefficient
  simp_rw [thinRadialWindow_slice_independent hrad b]
  rw [integral_complex_ofReal, Complex.real_smul, Complex.ofReal_mul]

/-- The positive-spectral response of a prepared nonzero thin current
diverges with its original Abelian line-coupling normalization. -/
theorem thinCurrent_uv_infinite {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (hprep : thinCurrentPrepared edges)
    (hnet : ∃ e, (edges e).multiplicity ≠ 0 ∧ 0 < (edges e).length)
    {φ : ThinCurrentPlane → ℝ} (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ) (hnn : ∀ p, 0 ≤ φ p)
    (hne : ∃ p, φ p ≠ 0) (hrad : thinRadialWindow φ)
    (hs : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2)
    (ρ : Measure ℝ≥0) (hρ : ρ ≠ 0) :
    thinCurrentResponse edges (thinCurrentSpectrum ρ) = ⊤ := by
  have hs' (p : ThinCurrentPlane) (hp : φ p ≠ 0) : ‖p‖ < 2 := (hs p hp).2
  obtain ⟨B, hB, hb⟩ := thinWindow_real_bound hsm (thinWindow_compact_of_support hs')
  exact thinCurrentResponse_eq_top_of_perimeter edges φ ρ hρ hB
    (fun p => (le_abs_self _).trans (hb p)) hs
    (thinWindow_slice_pos hsm.continuous hnn hne hrad hs') hnet
    (thinCurrentShell_radial_perimeter edges hprep hsm hnn hrad hs)

/-- A nonzero momentum-space current must contain a positive-length
piece with nonzero net signed multiplicity. -/
theorem thinCurrent_nonzero_has_piece {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment)
    (hnet : ∃ p, thinCurrentNormSq edges p ≠ 0) :
    ∃ e, (edges e).multiplicity ≠ 0 ∧ 0 < (edges e).length := by
  obtain ⟨p, hp⟩ := hnet
  by_contra hn
  apply hp
  have hzero (k : Fin 4) : thinCurrent edges p k = 0 := by
    unfold thinCurrent
    apply Finset.sum_eq_zero
    intro j _
    by_cases hm : (edges j).multiplicity = 0
    · simp [hm]
    · have hL : (edges j).length = 0 := le_antisymm
        (le_of_not_gt fun ht => hn ⟨j, hm, ht⟩) (edges j).length_nonneg
      simp [thinCurrentSegmentWave, hL]
  simp [thinCurrentNormSq, hzero]

end UV

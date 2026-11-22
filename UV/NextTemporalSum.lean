import UV.NextTemporalObstruction
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Common-scale ordinary fermion sums are represented by a finite
orthogonal direct sum of their actual marked pencils. -/

noncomputable section
open Complex Filter Matrix MeasureTheory Set
open scoped Topology Matrix Matrix.Norms.Elementwise

namespace UV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev TemporalSumDimension (d : ι → ℕ) := Fintype.card (Σ i, Fin (d i))

private def temporalSumIndex (d : ι → ℕ) : (Σ i, Fin (d i)) ≃ Fin (TemporalSumDimension d) :=
  Fintype.equivFin _

def temporalSumMatrix (d : ι → ℕ) :
    (∀ i, TemporalMatrix (d i)) →+* TemporalMatrix (TemporalSumDimension d) :=
  (Matrix.reindexAlgEquiv ℂ ℂ (temporalSumIndex d)).toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun i => Fin (d i)) ℂ)

private theorem temporalSumMatrix_eq {d : ι → ℕ} (M : ∀ i, TemporalMatrix (d i)) :
    temporalSumMatrix d M = (Matrix.blockDiagonal' M).submatrix
      (temporalSumIndex d).symm (temporalSumIndex d).symm := rfl

private theorem temporalSumMatrix_apply {d : ι → ℕ}
    (M : ∀ i, TemporalMatrix (d i)) (i : ι) (j k : Fin (d i)) :
    temporalSumMatrix d M (temporalSumIndex d ⟨i, j⟩) (temporalSumIndex d ⟨i, k⟩) = M i j k := by
  simp only [temporalSumMatrix_eq, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.blockDiagonal'_apply_eq]

private theorem temporalSumMatrix_continuous (d : ι → ℕ) :
    Continuous (temporalSumMatrix d) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun M : ∀ i, TemporalMatrix (d i) =>
    Matrix.blockDiagonal' M ((temporalSumIndex d).symm i) ((temporalSumIndex d).symm j))
  generalize (temporalSumIndex d).symm i = i'
  generalize (temporalSumIndex d).symm j = j'
  obtain ⟨i, r⟩ := i'
  obtain ⟨j, s⟩ := j'
  by_cases he : i = j
  · subst j
    simp only [Matrix.blockDiagonal'_apply_eq]
    exact (continuous_apply s).comp ((continuous_apply r).comp (continuous_apply i))
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ he, continuous_const]

private theorem temporalSumMatrix_smul (d : ι → ℕ) (z : ℂ)
    (M : ∀ i, TemporalMatrix (d i)) :
    temporalSumMatrix d (fun i => z • M i) = z • temporalSumMatrix d M := by
  rw [temporalSumMatrix_eq, temporalSumMatrix_eq]
  have hb : Matrix.blockDiagonal' (fun i => z • M i) = z • Matrix.blockDiagonal' M := by
    ext ⟨i, r⟩ ⟨j, s⟩
    by_cases he : i = j
    · subst j
      simp [Matrix.blockDiagonal'_apply_eq]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ he]
  rw [hb]
  rfl

private theorem temporalSumMatrix_adjoint (d : ι → ℕ) (M : ∀ i, TemporalMatrix (d i)) :
    temporalSumMatrix d (fun i => (M i)ᴴ) = (temporalSumMatrix d M)ᴴ := by
  rw [temporalSumMatrix_eq, temporalSumMatrix_eq, ← Matrix.blockDiagonal'_conjTranspose,
    Matrix.conjTranspose_submatrix]

private theorem temporalSumMatrix_hermitian (d : ι → ℕ) (M : ∀ i, TemporalMatrix (d i))
    (hM : ∀ i, (M i).IsHermitian) : (temporalSumMatrix d M).IsHermitian := by
  change (temporalSumMatrix d M)ᴴ = _
  rw [← temporalSumMatrix_adjoint]
  congr 1
  exact funext fun i => (hM i).eq

private theorem temporalSumMatrix_trace (d : ι → ℕ) (M : ∀ i, TemporalMatrix (d i)) :
    (temporalSumMatrix d M).trace = ∑ i, (M i).trace := by
  rw [temporalSumMatrix_eq, ← Matrix.trace_blockDiagonal']
  unfold Matrix.trace Matrix.diag
  exact Equiv.sum_comp (temporalSumIndex d).symm
    (fun i => Matrix.blockDiagonal' M i i)

private theorem temporalSumMatrix_diagonal (d : ι → ℕ) (ε : ∀ i, Fin (d i) → ℂ) :
    temporalSumMatrix d (fun i => diagonal (ε i)) =
      diagonal (fun j =>
        let s := (temporalSumIndex d).symm j
        ε s.1 s.2) := by
  rw [temporalSumMatrix_eq, Matrix.blockDiagonal'_diagonal]
  ext i j
  by_cases he : i = j
  · subst j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply_eq]
  · rw [Matrix.submatrix_apply, diagonal_apply_ne _ ((temporalSumIndex d).symm.injective.ne he),
      diagonal_apply_ne _ he]

private theorem temporalSumMatrix_pencil (d : ι → ℕ)
    (A : ∀ i, TemporalMatrix (d i)) (z : ℂ) :
    temporalSumMatrix d (fun i => furtherTemporalPencil (A i) z) =
      furtherTemporalPencil (temporalSumMatrix d A) z := by
  change temporalSumMatrix d ((fun _ => z • 1) + A) = _
  rw [map_add, temporalSumMatrix_smul]
  change z • temporalSumMatrix d 1 + temporalSumMatrix d A = _
  rw [map_one]
  rfl

private theorem temporalSumMatrix_resolvent (d : ι → ℕ) (A : ∀ i, TemporalMatrix (d i))
    (hA : ∀ i, (A i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    temporalSumMatrix d (fun i => furtherTemporalResolvent (A i) z) =
      furtherTemporalResolvent (temporalSumMatrix d A) z := by
  symm
  unfold furtherTemporalResolvent
  apply Matrix.inv_eq_left_inv
  rw [← temporalSumMatrix_pencil, ← map_mul]
  convert (temporalSumMatrix d).map_one using 2
  funext i
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (furtherTemporalPencil_isUnit_of_im_ne_zero (hA i) hz))

/-- The ordinary log-determinant coefficients of the separate charged slots
add as traces on their orthogonal direct sum at each nonreal frequency. -/
theorem temporalSumMatrix_coefficient (d : ι → ℕ)
    (A B C Q : ∀ i, TemporalMatrix (d i)) (hA : ∀ i, (A i).IsHermitian)
    (hB : ∀ i, (B i).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    furtherTemporalCoefficient (temporalSumMatrix d A) (temporalSumMatrix d B)
      (temporalSumMatrix d C) (temporalSumMatrix d Q) z =
      ∑ i, furtherTemporalCoefficient (A i) (B i) (C i) (Q i) z := by
  unfold furtherTemporalCoefficient
  rw [← temporalSumMatrix_resolvent d A hA hz, ← temporalSumMatrix_resolvent d B hB hz,
    ← temporalSumMatrix_adjoint]
  simp only [← map_mul, temporalSumMatrix_trace, Pi.mul_apply, Finset.sum_sub_distrib]

private theorem temporalSumMatrix_nonzero_block (d : ι → ℕ)
    (M : ∀ i, TemporalMatrix (d i)) (j : ι) (h : M j ≠ 0) :
    temporalSumMatrix d M ≠ 0 := by
  intro hz
  apply h
  ext r s
  rw [← temporalSumMatrix_apply M j r s, hz, Matrix.zero_apply, Matrix.zero_apply]

private theorem temporalSumMatrix_bounded (d : ι → ℕ)
    (C : ℝ → ∀ i, TemporalMatrix (d i))
    (hC : ∀ i, ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖C t i‖ ≤ M) :
    ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖temporalSumMatrix d (C t)‖ ≤ M := by
  choose M hM using hC
  let S : Set (∀ i, TemporalMatrix (d i)) :=
    {C | ∀ i, C i ∈ Metric.closedBall 0 (M i)}
  have hs : IsCompact S := isCompact_pi_infinite (fun _ => isCompact_closedBall _ _)
  obtain ⟨K, hK⟩ := (hs.image (temporalSumMatrix_continuous d)).isBounded.exists_norm_le
  have hm := eventually_all.mpr hM
  exact ⟨K, hm.mono fun t ht => hK _ ⟨C t, fun i => by simpa using ht i, rfl⟩⟩

private theorem temporalSumMatrix_projection (d : ι → ℕ)
    (ε : ∀ i, Fin (d i) → ℝ) (E : ℝ) :
    temporalSumMatrix d (fun i => temporalEnergyProjection (ε i) E) =
      temporalEnergyProjection (fun j =>
        let s := (temporalSumIndex d).symm j
        ε s.1 s.2) E := by
  unfold temporalEnergyProjection
  exact temporalSumMatrix_diagonal d _

/-- A common-scale finite sum has the same strictly positive rescaled
absolute band bound when one equal-energy block survives. The absolute
value is taken after the ordinary fermion log-determinant traces add. -/
theorem temporal_contact_finite_sum_ray_band_lower {Sector : Type*} (b : Bool) (plane : ChargePlane Sector)
    (d : ι → ℕ) (A B : ∀ i, ℝ → TemporalHermitian (d i))
    (C Q : ∀ i, ℝ → TemporalMatrix (d i)) (scale : ℝ → ℝ)
    (hs : ∀ᶠ t in (atTop : Filter ℝ), 0 < scale t)
    (H : ∀ i, TemporalHermitian (d i)) (Q₀ : ∀ i, TemporalMatrix (d i))
    (hA : ∀ i, Tendsto (fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (A i t).1) atTop (𝓝 (H i).1))
    (hB : ∀ i, Tendsto (fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (B i t).1) atTop (𝓝 (H i).1))
    (hQ : ∀ i, Tendsto (Q i) atTop (𝓝 (Q₀ i)))
    (hC : ∀ i, ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), scale t * ‖C i t‖ ≤ M)
    (j : ι) (E : ℝ) (hq : furtherTemporalEnergyProjection (H j).2 E * Q₀ j *
      furtherTemporalEnergyProjection (H j).2 E ≠ 0) :
    ∃ c > (0 : ℝ), ∀ᶠ t in (atTop : Filter ℝ),
      c ≤ scale t * ∫ ω in Icc (scale t) (2 * scale t),
        ‖∑ i, furtherTemporalCoefficient (A i t).1 (B i t).1 (C i t) (Q i t)
          (furtherTemporalFrequency b ω)‖ := by
  let U : ∀ i, TemporalUnitary (d i) := fun i => (H i).2.eigenvectorUnitary
  let D : (i : ι) → TemporalMatrix (d i) → TemporalMatrix (d i) := fun i => temporalBasis (U i)
  let e : (i : ι) → Fin (d i) → ℝ := fun i => (H i).2.eigenvalues
  let ε : ChargePlane Sector → Fin (TemporalSumDimension d) → ℝ := fun _ j =>
    let s := (temporalSumIndex d).symm j
    e s.1 s.2
  let combine (Z : ∀ i, ℝ → TemporalHermitian (d i)) (t : ℝ) :
      TemporalHermitian (TemporalSumDimension d) :=
    ⟨temporalSumMatrix d (fun i => D i (Z i t).1),
      temporalSumMatrix_hermitian d _ (fun i => temporalBasis_hermitian (U i) (Z i t).2)⟩
  let charge (t : ℝ) := temporalSumMatrix d (fun i => D i (Q i t))
  let contact (t : ℝ) := temporalSumMatrix d (fun i => D i (C i t))
  let charge₀ : ChargePlane Sector → TemporalMatrix (TemporalSumDimension d) :=
    fun _ => temporalSumMatrix d (fun i => D i (Q₀ i))
  let rescale (Z : ∀ i, ℝ → TemporalHermitian (d i)) (i : ι) (t : ℝ) : TemporalHermitian (d i) :=
    ⟨(((scale t)⁻¹ : ℝ) : ℂ) • (Z i t).1, temporal_hermitian_real_smul (Z i t).2 _⟩
  let scaledContact (t : ℝ) := (scale t : ℂ) • contact t
  have hLim (Z : ∀ i, ℝ → TemporalHermitian (d i))
      (hZ : ∀ i, Tendsto (fun t => (((scale t)⁻¹ : ℝ) : ℂ) • (Z i t).1) atTop (𝓝 (H i).1)) :
      Tendsto (fun t => (combine (rescale Z) t).1) atTop (𝓝 (diagonal fun i => (ε plane i : ℂ))) := by
    rw [← temporalSumMatrix_diagonal d (fun i j => (e i j : ℂ))]
    apply (temporalSumMatrix_continuous d).continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro i
    have hd : D i (H i).1 = diagonal (fun j => (e i j : ℂ)) := (H i).2.star_mul_self_mul_eq_diagonal
    rw [← hd]
    exact (continuous_temporalBasis (U i)).continuousAt.tendsto.comp (hZ i)
  have hCharge : Tendsto charge atTop (𝓝 (charge₀ plane)) := by
    apply (temporalSumMatrix_continuous d).continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr fun i => (continuous_temporalBasis (U i)).continuousAt.tendsto.comp (hQ i)
  have hContact : ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖scaledContact t‖ ≤ M := by
    have hb (i : ι) : ∃ M : ℝ, ∀ᶠ t in (atTop : Filter ℝ),
        ‖D i ((scale t : ℂ) • C i t)‖ ≤ M := by
      apply temporalBasis_bounded (U i)
      obtain ⟨M, hM⟩ := hC i
      exact ⟨M, (hs.and hM).mono fun t ht => by
        simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2⟩
    obtain ⟨M, hM⟩ := temporalSumMatrix_bounded d (fun t i => D i ((scale t : ℂ) • C i t)) hb
    exact ⟨M, hM.mono fun t ht => by
      change ‖(scale t : ℂ) • temporalSumMatrix d (fun i => D i (C i t))‖ ≤ M
      simpa only [D, temporalBasis_smul, temporalSumMatrix_smul] using ht⟩
  have hSurvives : temporalEnergyProjection (ε plane) E * charge₀ plane *
      temporalEnergyProjection (ε plane) E ≠ 0 := by
    rw [← temporalSumMatrix_projection d e E]
    change temporalSumMatrix d _ * temporalSumMatrix d _ * temporalSumMatrix d _ ≠ 0
    rw [← map_mul, ← map_mul]
    exact temporalSumMatrix_nonzero_block d _ j (temporalBasis_nonzero_energy_block (H j).2 E (Q₀ j) hq)
  obtain ⟨c, hc, hb⟩ := temporal_contact_rescaled_ray_bound b ε plane
    (combine (rescale A)) (combine (rescale B)) scaledContact charge (hLim A hA) (hLim B hB)
    charge₀ hCharge hContact E hSurvives
  refine ⟨c, hc, (hs.and hb).mono fun t ht => ?_⟩
  have hscale (Z : ∀ i, ℝ → TemporalHermitian (d i)) :
      (combine (rescale Z) t).1 = (((scale t)⁻¹ : ℝ) : ℂ) • (combine Z t).1 := by
    change temporalSumMatrix d (fun i => D i ((((scale t)⁻¹ : ℝ) : ℂ) • (Z i t).1)) = _
    simp only [D, temporalBasis_smul, temporalSumMatrix_smul]
    rfl
  have hrescale (Z : ∀ i, ℝ → TemporalHermitian (d i)) :
      combine (rescale Z) t =
        ⟨(((scale t)⁻¹ : ℝ) : ℂ) • (combine Z t).1,
          temporal_hermitian_real_smul (combine Z t).2 _⟩ := Subtype.ext (hscale Z)
  have hlim := ht.2
  rw [hrescale A, hrescale B] at hlim
  change c ≤ furtherTemporalBand b _ _ ((scale t : ℂ) • contact t) (charge t) at hlim
  rw [temporalBand_scale b (combine A t).2 (combine B t).2 (contact t) (charge t) ht.1] at hlim
  refine hlim.trans_eq (congrArg (fun x : ℝ => scale t * x) ?_)
  apply setIntegral_congr_fun measurableSet_Icc
  intro ω hω
  have hn := furtherTemporalFrequency_im_ne_zero b (ht.1.trans_le hω.1)
  change ‖furtherTemporalCoefficient (temporalSumMatrix d (fun i => D i (A i t).1))
    (temporalSumMatrix d (fun i => D i (B i t).1)) (contact t) (charge t)
    (furtherTemporalFrequency b ω)‖ = _
  rw [temporalSumMatrix_coefficient d _ _ _ _
    (fun i => temporalBasis_hermitian (U i) (A i t).2)
    (fun i => temporalBasis_hermitian (U i) (B i t).2) hn]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (temporalBasis_coefficient (U i)
    (A i t).2 (B i t).2 (C i t) (Q i t) hn).symm

end UV

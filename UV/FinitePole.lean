import UV.Response
import UV.MatrixAdjugate
import UV.PoleCertificates
import UV.DiskHomotopy
import UV.MatrixPencilAnalytic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Neumann control of actual finite matrix pencils in the spectral norm.
The boundary inverse is derived from the margin, not included as data for
the perturbed matrix. -/

noncomputable section
open Set Metric Complex
open scoped Topology Matrix.Norms.L2Operator

namespace UV

/-- Actual homotopy zero counts construct the enclosed simple endpoint root
and its rate certificate. No endpoint root is supplied for the second pencil. -/
theorem disk_family_finite_pole_enclosure {F : ℝ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (F t) (closedBall c r))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c r, F t z ≠ 0)
    (hc : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c r))
    (hd : ContinuousOn (fun p : ℝ × ℂ => deriv (F p.1) p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c r))
    (hzero : F 0 c = 0) (hsimple : deriv (F 0) c ≠ 0)
    (honly : ∀ z ∈ ball c r, F 0 z = 0 → z = c) :
    ∃ p ∈ ball c r, F 1 p = 0 ∧ deriv (F 1) p ≠ 0 ∧
      (∀ z ∈ ball c r, F 1 z = 0 → z = p) ∧
      ∀ baseline : ℂ,
        |poleShiftRate (p-baseline)-poleShiftRate (c-baseline)| < 2*r ∧
        (2*r < poleShiftRate (c-baseline) → 0 < poleShiftRate (p-baseline)) := by
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hcount0 := disk_zeroCount_eq_one_of_unique_simple (hF 0 ht0) hr
    (hb 0 ht0) (mem_ball_self hr) hzero hsimple honly
  have hcount1 : diskZeroCount (F 1) c r = 1 :=
    (disk_zeroCount_homotopy hr hF hb hc hd 1 ht1).trans hcount0
  obtain ⟨p, hp, hpzero, hpderiv, hpuniq⟩ :=
    disk_zeroCount_one_unique_simple (hF 1 ht1) hr (hb 1 ht1) hcount1
  refine ⟨p, hp, hpzero, hpderiv, hpuniq, fun baseline => ?_⟩
  have hrate : |poleShiftRate (p-baseline)-poleShiftRate (c-baseline)| < 2*r :=
    finite_pole_rate_enclosure (by simpa only [mem_ball, dist_eq_norm] using hp)
  exact ⟨hrate, fun hpos => by have hlow := (abs_lt.mp hrate).1; linarith⟩

theorem pencil_neumann_unit {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    [CompleteSpace R] {A E : R} (hA : IsUnit A) {l : ℂ}
    (hmargin : ‖l‖ * ‖Ring.inverse A * E‖ < 1) : IsUnit (A + l • E) := by
  have hnorm : ‖-(l • (Ring.inverse A * E))‖ < 1 := by
    simpa only [norm_neg, norm_smul] using hmargin
  have hunit := isUnit_one_sub_of_norm_lt_one hnorm
  have hfactor : A * (1 - -(l • (Ring.inverse A * E))) = A + l • E := by
    rw [sub_neg_eq_add, mul_add, mul_one, mul_smul_comm, ← mul_assoc,
      Ring.mul_inverse_cancel A hA, one_mul]
  rw [← hfactor]
  exact hA.mul hunit

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem finite_pencil_boundary_nonzero {K D : ℂ → Matrix n n ℂ}
    {c : ℂ} {r θ : ℝ}
    (hK : ∀ z ∈ sphere c r, (K z).det ≠ 0)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (K z) * D z‖ ≤ θ)
    {l : ℂ} (hl : ‖l‖ * θ < 1) :
    ∀ z ∈ sphere c r, (K z + l • D z).det ≠ 0 := by
  intro z hz
  have hunit : IsUnit (K z) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (hK z hz))
  have hbound : ‖l‖ * ‖Ring.inverse (K z) * D z‖ < 1 :=
    (mul_le_mul_of_nonneg_left (hmargin z hz) (norm_nonneg l)).trans_lt hl
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (pencil_neumann_unit hunit hbound)).ne_zero

/-- The separate inverse/error bounds in the endpoint source certificate
give the actual matrix inverse throughout the real homotopy. -/
theorem finite_endpoint_homotopy_boundary_nonzero {KX KY : ℂ → Matrix n n ℂ}
    {c : ℂ} {r : ℝ} {E : ℂ → ℝ}
    (hKY : ∀ z ∈ sphere c r, (KY z).det ≠ 0)
    (hE : ∀ z ∈ sphere c r, ‖KX z-KY z‖ ≤ E z)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (KY z)‖ * E z < 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ∀ z ∈ sphere c r, (KY z + (t : ℂ) • (KX z-KY z)).det ≠ 0 := by
  intro z hz
  have hunit : IsUnit (KY z) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (hKY z hz))
  have hprod : ‖Ring.inverse (KY z) * (KX z-KY z)‖ < 1 :=
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hE z hz)
      (norm_nonneg _))).trans_lt (hmargin z hz)
  have hlt : ‖(t : ℂ)‖ * ‖Ring.inverse (KY z) * (KX z-KY z)‖ < 1 := by
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
    exact (mul_le_of_le_one_left (norm_nonneg _) htNorm).trans_lt hprod
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (pencil_neumann_unit hunit hlt)).ne_zero

/-- The source finite retained-matrix enclosure. Entrywise holomorphy is
the usual finite-matrix holomorphy condition. The original matrix norm
margin constructs boundary inverses, preserves the actual zero count and
produces the unique simple endpoint root and both rate conclusions. -/
theorem oqed_finite_pole_enclosure {KX KY : ℂ → Matrix n n ℂ}
    {c : ℂ} {r : ℝ} {E : ℂ → ℝ} (hr : 0 < r)
    (hX : ∀ i j, AnalyticOnNhd ℂ (fun z => KX z i j) (closedBall c r))
    (hY : ∀ i j, AnalyticOnNhd ℂ (fun z => KY z i j) (closedBall c r))
    (hKY : ∀ z ∈ sphere c r, (KY z).det ≠ 0)
    (hzero : (KY c).det = 0) (hsimple : deriv (fun z => (KY z).det) c ≠ 0)
    (honly : ∀ z ∈ ball c r, (KY z).det = 0 → z = c)
    (hE : ∀ z ∈ sphere c r, ‖KX z-KY z‖ ≤ E z)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (KY z)‖ * E z < 1) :
    ∃ p ∈ ball c r, (KX p).det = 0 ∧ deriv (fun z => (KX z).det) p ≠ 0 ∧
      (∀ z ∈ ball c r, (KX z).det = 0 → z = p) ∧
      ∀ baseline : ℂ,
        |poleShiftRate (p-baseline)-poleShiftRate (c-baseline)| < 2*r ∧
        (2*r < poleShiftRate (c-baseline) → 0 < poleShiftRate (p-baseline)) := by
  let F : ℝ → ℂ → ℂ := fun t z => (KY z + (t : ℂ) • (KX z-KY z)).det
  have hF0 : F 0 = fun z => (KY z).det := by funext z; simp [F]
  have hF1 : F 1 = fun z => (KX z).det := by funext z; simp [F]
  have hD : ∀ i j, AnalyticOnNhd ℂ (fun z => (KX z-KY z) i j) (closedBall c r) :=
    fun i j => (hX i j).sub (hY i j)
  obtain ⟨hA, hC, hD'⟩ := matrix_pencil_closedDisk_boundary_data hY hD
  have hres := disk_family_finite_pole_enclosure (F := F) hr (fun t _ => hA t)
    (fun _ ht => finite_endpoint_homotopy_boundary_nonzero hKY hE hmargin ht) hC hD'
    (by simpa only [hF0] using hzero) (by simpa only [hF0] using hsimple)
    (by simpa only [hF0] using honly)
  simpa only [hF1] using hres

end UV

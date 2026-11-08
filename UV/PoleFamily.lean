import UV.FinitePole
import UV.MatrixPencilCount
import UV.DiskRootFamily

/-! The source's complex pole family is constructed from its contour moment.
The matrix margin derives actual zero counts and hence the simple roots;
the contour integral derives holomorphy of that same family. -/

noncomputable section
open Set Metric Complex
open scoped Topology Matrix.Norms.L2Operator

namespace UV

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixPoleRoot (K D : ℂ → Matrix n n ℂ) (c : ℂ) (r : ℝ) : ℂ → ℂ :=
  diskRootFamily (matrixPencilDet K D) c r

/-- A complex norm margin constructs the actual holomorphic root family on
the full certified parameter disk, without a pre-existing root branch. -/
theorem matrix_pole_holomorphic_family {K D : ℂ → Matrix n n ℂ}
    {c : ℂ} {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ)
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) (closedBall c r))
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) (closedBall c r))
    (hb : ∀ z ∈ sphere c r, (K z).det ≠ 0)
    (hzero : (K c).det = 0) (hsimp : deriv (fun z => (K z).det) c ≠ 0)
    (honly : ∀ z ∈ ball c r, (K z).det = 0 → z = c)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (K z) * D z‖ ≤ θ) :
    AnalyticOnNhd ℂ (matrixPoleRoot K D c r) (ball 0 θ⁻¹) ∧
      matrixPoleRoot K D c r 0 = c ∧
      ∀ l ∈ ball (0 : ℂ) θ⁻¹,
        ‖matrixPoleRoot K D c r l-c‖ < r ∧
        matrixPencilDet K D l (matrixPoleRoot K D c r l) = 0 ∧
        deriv (matrixPencilDet K D l) (matrixPoleRoot K D c r l) ≠ 0 ∧
        ∀ z ∈ ball c r, matrixPencilDet K D l z = 0 → z = matrixPoleRoot K D c r l := by
  have hF : ∀ l ∈ ball (0 : ℂ) θ⁻¹,
      AnalyticOnNhd ℂ (matrixPencilDet K D l) (closedBall c r) :=
    fun l _ => matrix_pencil_det_analyticOnNhd hK hD l
  have hboundary : ∀ l ∈ ball (0 : ℂ) θ⁻¹, ∀ z ∈ sphere c r,
      matrixPencilDet K D l z ≠ 0 :=
    fun _ hl => matrix_pencil_parameter_boundary_nonzero hθ hb hmargin hl
  have hcount := matrix_pencil_diskZeroCount_eq_one hr hθ hK hD hb hzero hsimp honly hmargin
  obtain ⟨hc, hd⟩ := matrix_pencil_complex_joint_continuousOn
    (T := ball (0 : ℂ) θ⁻¹)
    (fun i j => (hK i j).mono sphere_subset_closedBall)
    (fun i j => (hD i j).mono sphere_subset_closedBall)
  have hp : ∀ z ∈ sphere c r,
      DifferentiableOn ℂ (fun l => matrixPencilDet K D l z) (ball 0 θ⁻¹) := by
    intro z hz
    exact (matrix_pencil_parameter_analyticOnNhd hK hD
      (sphere_subset_closedBall hz)).1.differentiableOn.mono (subset_univ _)
  have hpd : ∀ z ∈ sphere c r,
      DifferentiableOn ℂ (fun l => deriv (matrixPencilDet K D l) z) (ball 0 θ⁻¹) := by
    intro z hz
    exact (matrix_pencil_parameter_analyticOnNhd hK hD
      (sphere_subset_closedBall hz)).2.differentiableOn.mono (subset_univ _)
  obtain ⟨hA, hroots⟩ := disk_unique_root_holomorphic_family isOpen_ball hr
    hF hboundary hcount hc hd hp hpd
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) θ⁻¹ := mem_ball_self (inv_pos.mpr hθ)
  have hinit := diskRootFamily_initial hr (hF 0 h0) (hboundary 0 h0) (hcount 0 h0)
    (by simpa [matrixPencilDet] using hzero)
  refine ⟨hA, hinit, fun l hl => ?_⟩
  obtain ⟨hin, hz, hs, hu⟩ := hroots l hl
  exact ⟨hin, hz, hs, hu⟩

set_option maxHeartbeats 800000 in
/-- Full named Taylor-remainder certificate. Its coefficients are actual
iterated derivatives of the contour-constructed pole shift. The constant
coefficient is zero, so the finite sum is the source's sum from one to N. -/
theorem oqed_pole_taylor_remainder {K D : ℂ → Matrix n n ℂ}
    {c : ℂ} {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) (closedBall c r))
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) (closedBall c r))
    (hb : ∀ z ∈ sphere c r, (K z).det ≠ 0)
    (hzero : (K c).det = 0) (hsimp : deriv (fun z => (K z).det) c ≠ 0)
    (honly : ∀ z ∈ ball c r, (K z).det = 0 → z = c)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (K z) * D z‖ ≤ θ) :
    let z := matrixPoleRoot K D c r
    let f := fun l => z l-c
    AnalyticOnNhd ℂ z (ball 0 θ⁻¹) ∧ z 0 = c ∧
      (∀ l ∈ ball (0 : ℂ) θ⁻¹,
        ‖z l-c‖ < r ∧ matrixPencilDet K D l (z l) = 0 ∧
        deriv (matrixPencilDet K D l) (z l) ≠ 0 ∧
        ∀ w ∈ ball c r, matrixPencilDet K D l w = 0 → w = z l) ∧
      poleTaylorCoeff f 0 = 0 ∧ poleTaylorCoeff f 1 = deriv z 0 ∧
      (∀ k, ‖poleTaylorCoeff f k‖ ≤ r * θ^k) ∧
      HasSum (poleTaylorCoeff f) (z 1-c) ∧
      (∀ N : ℕ, ‖z 1-c-∑ k ∈ Finset.range (N+1), poleTaylorCoeff f k‖ ≤
        r*θ^(N+1)/(1-θ)) ∧
      |poleShiftRate (z 1-c)-poleShiftRate (deriv z 0)| ≤
        2*r*θ^2/(1-θ) := by
  obtain ⟨ha, hi, hp⟩ := matrix_pole_holomorphic_family hr hθ hK hD hb hzero hsimp honly hmargin
  let z := matrixPoleRoot K D c r
  have hi' : z 0 = c := hi
  have hd : DifferentiableOn ℂ z (ball 0 θ⁻¹) := ha.differentiableOn
  have hbound : ∀ l ∈ ball (0 : ℂ) θ⁻¹, ‖z l-c‖ ≤ r := fun l hl => (hp l hl).1.le
  have hc := pole_shift_taylor_coefficients z
  rw [hi'] at hc
  refine ⟨ha, hi, hp, hc.1, hc.2, ?_, ?_, ?_, ?_⟩
  · exact pole_taylor_coefficient_bound (f := fun l => z l-c) (R := r) hθ (hd.sub_const c) hbound
  · exact pole_taylor_hasSum (f := fun l => z l-c) hθ hθ1 (hd.sub_const c)
  · exact pole_taylor_remainder (f := fun l => z l-c) (R := r) hθ hθ1 (hd.sub_const c) hbound
  · have hrate := pole_branch_rate_remainder hθ hθ1 hd
      (fun l hl => by simpa only [hi'] using hbound l hl)
    simpa only [hi'] using hrate

end UV

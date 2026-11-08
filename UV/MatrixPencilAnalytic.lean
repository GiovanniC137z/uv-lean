import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! Scalar-entry analyticity of finite matrix pencils. The determinant and
its actual z-derivative are jointly holomorphic in the complex homotopy
parameter and z. No norm on the matrix space is used. -/

noncomputable section
open Set Metric
open scoped Topology

namespace UV

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixPencilDet (K D : ℂ → Matrix n n ℂ) (lam z : ℂ) : ℂ :=
  (K z + lam • D z).det

theorem joint_snd_deriv_eq_fderiv {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : DifferentiableAt ℂ F p) :
    deriv (fun z : ℂ => F (p.1, z)) p.2 = fderiv ℂ F p (0, 1) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact h.deriv

theorem analyticAt_joint_snd_deriv {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : AnalyticAt ℂ F p) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => deriv (fun z : ℂ => F (q.1, z)) q.2) p := by
  have heval : AnalyticAt ℂ (fun q : ℂ × ℂ => fderiv ℂ F q (0, 1)) p :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hF.fderiv
  apply heval.congr
  filter_upwards [hF.eventually_analyticAt] with q hq
  exact (joint_snd_deriv_eq_fderiv hq.differentiableAt).symm

theorem matrix_pencil_det_joint_analyticOnNhd
    {K D : ℂ → Matrix n n ℂ} {S : Set ℂ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => matrixPencilDet K D p.1 p.2) (univ ×ˢ S) := by
  intro p hp
  have he (i j : n) : AnalyticAt ℂ (fun q : ℂ × ℂ => K q.2 i j + q.1 * D q.2 i j) p :=
    ((hK i j p.2 hp.2).comp analyticAt_snd).add
      (analyticAt_fst.mul ((hD i j p.2 hp.2).comp analyticAt_snd))
  simp only [matrixPencilDet, Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => he (σ i) i))

theorem matrix_pencil_det_analyticOnNhd
    {K D : ℂ → Matrix n n ℂ} {S : Set ℂ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) (lam : ℂ) :
    AnalyticOnNhd ℂ (matrixPencilDet K D lam) S := by
  intro z hz
  exact (matrix_pencil_det_joint_analyticOnNhd hK hD (lam, z) ⟨mem_univ _, hz⟩).comp
    (analyticAt_const.prod analyticAt_id)

theorem matrix_pencil_deriv_joint_analyticOnNhd
    {K D : ℂ → Matrix n n ℂ} {S : Set ℂ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => deriv (matrixPencilDet K D p.1) p.2) (univ ×ˢ S) := by
  intro p hp
  exact analyticAt_joint_snd_deriv (matrix_pencil_det_joint_analyticOnNhd hK hD p hp)

theorem matrix_pencil_complex_joint_continuousOn
    {K D : ℂ → Matrix n n ℂ} {S T : Set ℂ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) :
    ContinuousOn (fun p : ℂ × ℂ => matrixPencilDet K D p.1 p.2) (T ×ˢ S) ∧
    ContinuousOn (fun p : ℂ × ℂ => deriv (matrixPencilDet K D p.1) p.2) (T ×ˢ S) := by
  exact ⟨(matrix_pencil_det_joint_analyticOnNhd hK hD).continuousOn.mono
      (prod_mono (subset_univ _) Subset.rfl),
    (matrix_pencil_deriv_joint_analyticOnNhd hK hD).continuousOn.mono
      (prod_mono (subset_univ _) Subset.rfl)⟩

theorem complex_family_real_parameter_continuousOn
    (F : ℂ × ℂ → ℂ) {S : Set ℂ} {T : Set ℝ}
    (hF : ContinuousOn F (univ ×ˢ S)) :
    ContinuousOn (fun p : ℝ × ℂ => F ((p.1 : ℂ), p.2)) (T ×ˢ S) := by
  have he : Continuous (fun p : ℝ × ℂ => ((p.1 : ℂ), p.2)) := by fun_prop
  have hm : MapsTo (fun p : ℝ × ℂ => ((p.1 : ℂ), p.2)) (T ×ˢ S) (univ ×ˢ S) :=
    fun p hp => ⟨mem_univ _, hp.2⟩
  exact hF.comp he.continuousOn hm

theorem matrix_pencil_real_joint_continuousOn
    {K D : ℂ → Matrix n n ℂ} {S : Set ℂ} {T : Set ℝ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) :
    ContinuousOn (fun p : ℝ × ℂ => matrixPencilDet K D (p.1 : ℂ) p.2) (T ×ˢ S) ∧
    ContinuousOn (fun p : ℝ × ℂ => deriv (matrixPencilDet K D (p.1 : ℂ)) p.2) (T ×ˢ S) := by
  refine ⟨complex_family_real_parameter_continuousOn
      (fun p : ℂ × ℂ => matrixPencilDet K D p.1 p.2)
      (matrix_pencil_det_joint_analyticOnNhd hK hD).continuousOn, ?_⟩
  exact complex_family_real_parameter_continuousOn
    (fun p : ℂ × ℂ => deriv (matrixPencilDet K D p.1) p.2)
    (matrix_pencil_deriv_joint_analyticOnNhd hK hD).continuousOn

theorem matrix_pencil_parameter_analyticOnNhd
    {K D : ℂ → Matrix n n ℂ} {S : Set ℂ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) S)
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) S) {z : ℂ} (hz : z ∈ S) :
    AnalyticOnNhd ℂ (fun lam => matrixPencilDet K D lam z) univ ∧
    AnalyticOnNhd ℂ (fun lam => deriv (matrixPencilDet K D lam) z) univ := by
  constructor
  · intro lam _
    have hmap : AnalyticAt ℂ (fun w : ℂ => (w, z)) lam := analyticAt_id.prod analyticAt_const
    have hjoint := matrix_pencil_det_joint_analyticOnNhd hK hD (lam, z) ⟨mem_univ _, hz⟩
    exact AnalyticAt.comp (f := fun w : ℂ => (w, z)) (x := lam) hjoint hmap
  · intro lam _
    have hmap : AnalyticAt ℂ (fun w : ℂ => (w, z)) lam := analyticAt_id.prod analyticAt_const
    have hjoint := matrix_pencil_deriv_joint_analyticOnNhd hK hD (lam, z) ⟨mem_univ _, hz⟩
    exact AnalyticAt.comp (f := fun w : ℂ => (w, z)) (x := lam) hjoint hmap

/-- Exact real homotopy boundary data required by the disk root-count
argument, obtained solely from entry analyticity near the closed disk. -/
theorem matrix_pencil_closedDisk_boundary_data
    {K D : ℂ → Matrix n n ℂ} {c : ℂ} {r : ℝ}
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) (closedBall c r))
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) (closedBall c r)) :
    (∀ t : ℝ, AnalyticOnNhd ℂ (fun z => (K z + (t : ℂ) • D z).det) (closedBall c r)) ∧
    ContinuousOn (fun p : ℝ × ℂ => (K p.2 + (p.1 : ℂ) • D p.2).det)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r) ∧
    ContinuousOn (fun p : ℝ × ℂ => deriv (fun z => (K z + (p.1 : ℂ) • D z).det) p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r) := by
  refine ⟨fun t => matrix_pencil_det_analyticOnNhd hK hD (t : ℂ), ?_⟩
  exact matrix_pencil_real_joint_continuousOn
    (fun i j => (hK i j).mono sphere_subset_closedBall)
    (fun i j => (hD i j).mono sphere_subset_closedBall)

end UV

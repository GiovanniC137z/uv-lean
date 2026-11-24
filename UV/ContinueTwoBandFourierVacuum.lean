import UV.ContinueTwoBandProjectors
import UV.ContinueTwoBandRelativeWord
import UV.ContinueRepairResultSlab
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Occupied-band mixing on a fixed rectangular spatial torus. Finite
Slater overlap determinants have a strictly positive limit as the mode
cutoff is removed. -/

noncomputable section
open Matrix Set Filter
open scoped Matrix Topology

namespace UV.SectorPlane

def twoBandMixingAngle (m v : ℝ) : ℝ :=
  Real.arctan (v / (twoBandGap m v + m))

private def vacuumSlot (θ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(-(Real.sin θ : ℝ) : ℂ), (Real.cos θ : ℂ)]

private theorem vacuum_slot_norm (θ : ℝ) : ‖vacuumSlot θ‖ = 1 := by
  have h : ‖vacuumSlot θ‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    change ‖-(Real.sin θ : ℂ)‖^2 + ‖(Real.cos θ : ℂ)‖^2 = 1
    rw [norm_neg,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs,Real.sin_sq_add_cos_sq]
  nlinarith [norm_nonneg (vacuumSlot θ)]

/-- The occupied unit spinor has its phase fixed by a positive second
component, the occupied onsite basis direction. -/
def twoBandOccupiedUnit (m v : ℝ) : UnitVector (EuclideanSpace ℂ (Fin 2)) :=
  ⟨vacuumSlot (twoBandMixingAngle m v),vacuum_slot_norm _⟩

theorem twoBand_occupied_eigenvector {m : ℝ} (hm : 0 < m) (v : ℝ) :
    twoBandSymbol m v 0 *ᵥ (twoBandOccupiedUnit m v).val =
      (-(twoBandGap m v : ℂ)) • ((twoBandOccupiedUnit m v).val : Fin 2 → ℂ) := by
  let E := twoBandGap m v
  let r := v/(E+m)
  let s := Real.sqrt (1+r^2)
  have hE : 0 < E+m := add_pos (twoBand_gap_pos hm v) hm
  have hr : r*(E+m) = v := div_mul_cancel₀ _ hE.ne'
  have hS : 0 < s := by unfold s; positivity
  have hIdentity : v*r = E-m := by
    apply (mul_left_inj' hE.ne').mp
    change v*r*(E+m) = (E-m)*(E+m)
    rw [mul_assoc,hr]
    nlinarith [twoBand_gap_sq m v]
  have h₀ : m * -(r/s) + v*(1/s) = -E * -(r/s) := by
    field_simp
    linarith only [hr]
  have h₁ : v * -(r/s) + (-m)*(1/s) = -E * (1/s) := by
    field_simp
    linarith only [hIdentity]
  ext i
  fin_cases i
  · simpa [twoBandSymbol,twoBandOccupiedUnit,vacuumSlot,twoBandMixingAngle,
      Matrix.mulVec, dotProduct,Fin.sum_univ_two,Real.sin_arctan,Real.cos_arctan,E,r,s] using
      congrArg Complex.ofReal h₀
  · simpa [twoBandSymbol,twoBandOccupiedUnit,vacuumSlot,twoBandMixingAngle,
      Matrix.mulVec, dotProduct,Fin.sum_univ_two,Real.sin_arctan,Real.cos_arctan,E,r,s] using
      congrArg Complex.ofReal h₁

theorem twoBand_onsite_overlap (m v : ℝ) :
    inner ℂ (EuclideanSpace.single 1 (1:ℂ)) (twoBandOccupiedUnit m v).val =
      (Real.cos (twoBandMixingAngle m v) : ℂ) := by
  simp [EuclideanSpace.inner_single_left,twoBandOccupiedUnit,vacuumSlot]

theorem twoBand_onsite_overlap_pos (m v : ℝ) : 0 < Real.cos (twoBandMixingAngle m v) :=
  Real.cos_arctan_pos _

private theorem abs_arctan_bound (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have hd (t : ℝ) : ‖deriv Real.arctan t‖ ≤ 1 := by
    rw [(Real.hasDerivAt_arctan t).deriv,Real.norm_of_nonneg (by positivity),div_le_one (by positivity)]
    linarith [sq_nonneg t]
  simpa [Real.norm_eq_abs] using (convex_univ.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (s := (univ : Set ℝ)) (fun t _ => (Real.hasDerivAt_arctan t).differentiableAt)
    (fun t _ => hd t) (mem_univ (0:ℝ)) (mem_univ x))

theorem twoBand_mixing_angle_bound {m : ℝ} (hm : 0 < m) (v : ℝ) :
    |twoBandMixingAngle m v| ≤ |v| / (2*m) := by
  refine (abs_arctan_bound _).trans ?_
  have h := twoBand_mass_le_gap hm v
  rw [abs_div,abs_of_pos (add_pos (twoBand_gap_pos hm v) hm)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith)

def twoBandTorusHop (g σ δ₁ δ₂ δ₃ : ℝ) (n : ℤ × ℤ × ℤ) : ℝ :=
  twoBandSpatialHop g σ (repairTorusMomentum δ₁ δ₂ δ₃ n)

theorem twoBand_torus_mixing_angles_summable {m σ δ₁ δ₂ δ₃ : ℝ} (hm : 0 < m)
    (hσ : 0 < σ) (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) (g : ℝ) :
    Summable (fun n => (twoBandMixingAngle m (twoBandTorusHop g σ δ₁ δ₂ δ₃ n))^2) := by
  have hsum := (repair_gaussian_torus_summable (τ := 2*σ^2) (by positivity) h₁ h₂ h₃).mul_left
    ((g/(2*m))^2)
  apply hsum.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
  let k := repairTorusMomentum δ₁ δ₂ δ₃ n
  let v := twoBandTorusHop g σ δ₁ δ₂ δ₃ n
  calc
    _ = |twoBandMixingAngle m v|^2 := (sq_abs _).symm
    _ ≤ (|v|/(2*m))^2 := pow_le_pow_left₀ (abs_nonneg _) (twoBand_mixing_angle_bound hm v) _
    _ = _ := by
      unfold v twoBandTorusHop twoBandSpatialHop FurtherOptical.attenuation
      rw [div_pow,sq_abs,mul_pow,← Real.exp_nat_mul]
      push_cast
      rw [show 2*(-(σ^2 * ‖k‖^2)) = -(2*σ^2)*‖k‖^2 by ring]
      ring

/-- Finite mixed Gram matrix of the onsite and occupied orbitals.
The two bases use identical orthogonal momentum labels. -/
def twoBandCutoffGram {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℝ) (v : ι → ℝ) :
    Matrix ι ι ℂ := fun i j =>
  inner ℂ (EuclideanSpace.single (i,(1:Fin 2)) (1:ℂ))
    (WithLp.toLp 2 (fun a : ι × Fin 2 =>
      if a.1 = j then (twoBandOccupiedUnit m (v j)).val a.2 else 0))

theorem twoBand_cutoff_gram_det {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℝ) (v : ι → ℝ) :
    (twoBandCutoffGram m v).det = ∏ i, (Real.cos (twoBandMixingAngle m (v i)) : ℂ) := by
  have h : twoBandCutoffGram m v = Matrix.diagonal (fun i => (Real.cos (twoBandMixingAngle m (v i)) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [twoBandCutoffGram,EuclideanSpace.inner_single_left,twoBandOccupiedUnit,vacuumSlot]
    · simp [twoBandCutoffGram,EuclideanSpace.inner_single_left,hij]
  rw [h,Matrix.det_diagonal]

/-- The net of finite Slater overlap products converges to a strictly
positive real amplitude over all reciprocal lattice modes of the fixed
torus, including the zero mode. -/
theorem twoBand_torus_onsite_vacuum_overlap {m σ δ₁ δ₂ δ₃ : ℝ} (hm : 0 < m)
    (hσ : 0 < σ) (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) (g : ℝ) :
    let θ := fun n => twoBandMixingAngle m (twoBandTorusHop g σ δ₁ δ₂ δ₃ n)
    ∃ A : ℝ, 0 < A ∧ HasProd (fun n => Real.cos (θ n)) A := by
  let θ := fun n => twoBandMixingAngle m (twoBandTorusHop g σ δ₁ δ₂ δ₃ n)
  have hSum : Summable (fun n => (θ n)^2) := twoBand_torus_mixing_angles_summable hm hσ h₁ h₂ h₃ g
  have hDev : Summable (fun n => Real.cos (θ n)-1) := by
    apply (hSum.mul_left (1/2:ℝ)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [Real.cos_le_one (θ n)])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ n)]
  have hLog : Summable (fun n => Real.log (Real.cos (θ n))) :=
    (Real.summable_log_one_add_of_summable hDev).congr (fun n => by congr 1; ring)
  exact ⟨_,Real.exp_pos _,Real.hasProd_of_hasSum_log (fun n => twoBand_onsite_overlap_pos _ _) hLog.hasSum⟩

/-- Limit of the actual finite mixed Gram determinants, over arbitrary
increasing finite reciprocal-mode cutoffs. -/
theorem twoBand_torus_cutoff_gram_limit {m σ δ₁ δ₂ δ₃ : ℝ} (hm : 0 < m)
    (hσ : 0 < σ) (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) (g : ℝ) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun S : Finset (ℤ × ℤ × ℤ) =>
      (twoBandCutoffGram m (fun j : S => twoBandTorusHop g σ δ₁ δ₂ δ₃ j.val)).det)
        atTop (𝓝 (A:ℂ)) := by
  obtain ⟨A,hA,h⟩ := twoBand_torus_onsite_vacuum_overlap hm hσ h₁ h₂ h₃ g
  let c := fun n => Real.cos (twoBandMixingAngle m (twoBandTorusHop g σ δ₁ δ₂ δ₃ n))
  change Tendsto (fun S : Finset (ℤ × ℤ × ℤ) => ∏ i ∈ S, c i) atTop (𝓝 A) at h
  refine ⟨A,hA,(Complex.continuous_ofReal.continuousAt.tendsto.comp h).congr' ?_⟩
  apply Eventually.of_forall
  intro S
  simp only [Function.comp_apply,twoBand_cutoff_gram_det,Complex.ofReal_prod]
  exact (Finset.prod_coe_sort S (fun i => (c i : ℂ))).symm

end UV.SectorPlane

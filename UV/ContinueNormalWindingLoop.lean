import UV.ContinueNormalPacketGraph
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Absolute bounds on closed massive normal-circle Dirac loops at
nonzero winding. One long increment supplies decay in the independent
four-momentum, even when the other normal increments vanish. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {n : ℕ}

def normalLoopPhase (L θ : ℝ) (w : ℤ) : ℂ := (L:ℂ)*Complex.exp (Complex.I*((w:ℝ)*θ:ℝ))

theorem normal_loop_phase_norm {L : ℝ} (hL : 0 < L) (θ : ℝ) (w : ℤ) :
    ‖normalLoopPhase L θ w‖ = L := by simp [normalLoopPhase,Complex.norm_exp,Complex.mul_re,abs_of_pos hL]

/-- The product includes a unit-polarized Dirac insertion after every
propagator and the normal circle centre and holonomy outside the trace. -/
def normalWindingTrace (m L θ : ℝ) (w : ℤ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (x : Fin n → ℝ) : ℂ :=
  normalLoopPhase L θ w * (List.ofFn (fun j => normalDiracCover normalCoverGamma5 m (p j)
    (normalOpenIncrements ((w:ℝ)*L) x j) * diracSlash (u j).val)).prod.trace

theorem normal_winding_long_increment (D : ℝ) (x : Fin n → ℝ) :
    ∃ i : Fin (n+1), |D|/((n:ℝ)+1) ≤ |normalOpenIncrements D x i| := by
  let d := normalOpenIncrements D x
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j => |d j|) Finset.univ_nonempty
  have hs : |D| ≤ ∑ j, |d j| := by
    calc |D| = |∑ j, d j| := congrArg abs (normal_open_increments_sum D x).symm
         _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
  refine ⟨i,(div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr ?_⟩
  have h := hs.trans (Finset.sum_le_sum (fun j hj => hi j hj))
  simpa [mul_comm] using h

theorem normal_winding_decay {m L : ℝ} (hm : 0 < m) (hL : 0 < L) {w : ℤ} (hw : w ≠ 0)
    (p : Fin (n+1) → OSFourSpace) (x : Fin n → ℝ) :
    let D := (w:ℝ)*L
    let d := normalOpenIncrements D x
    let a := L/(2*((n:ℝ)+1))
    Real.exp (-(∑ j, normalCoverEnergy m (p j)*|d j|)) ≤
      (Real.exp (-(m/4)*|D|) * ∏ j, Real.exp (-(m/4)*|x j|)) *
        ∑ i, Real.exp (-a*‖p i‖) := by
  dsimp only
  let D := (w:ℝ)*L
  let d := normalOpenIncrements D x
  let E := fun j => normalCoverEnergy m (p j)
  let S := ∑ j, E j*|d j|
  let a := L/(2*((n:ℝ)+1))
  have hD : L ≤ |D| := by
    have hi : (1:ℤ) ≤ |w| := (Int.add_one_le_iff.mpr (abs_pos.mpr hw))
    have hw' : (1:ℝ) ≤ |(w:ℝ)| := by exact_mod_cast hi
    simpa [D,abs_mul,abs_of_pos hL] using mul_le_mul_of_nonneg_right hw' hL.le
  have hdisp : |D| ≤ ∑ j, |d j| := by
    calc |D| = |∑ j,d j| := congrArg abs (normal_open_increments_sum D x).symm
         _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
  have hx : ∑ j, |x j| ≤ ∑ j, |d j| := by rw [Fin.sum_univ_succ]; exact le_add_of_nonneg_left (abs_nonneg _)
  have hsum : m*(∑ j, |d j|) ≤ S := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (normal_cover_energy_bounds hm (p j)).1 (abs_nonneg _))
  obtain ⟨i,hi⟩ := normal_winding_long_increment D x
  have hj : L/((n:ℝ)+1) ≤ |d i| := (div_le_div_of_nonneg_right hD (by positivity)).trans hi
  have hpart : (L/((n:ℝ)+1))*‖p i‖ ≤ S := by
    have hh := mul_le_mul hj (normal_cover_energy_bounds hm (p i)).2 (norm_nonneg _) (abs_nonneg _)
    rw [mul_comm |d i|] at hh
    exact hh.trans (Finset.single_le_sum (fun j _ => mul_nonneg (hm.le.trans (normal_cover_energy_bounds hm (p j)).1) (abs_nonneg _)) (Finset.mem_univ i))
  have ha : a = (L/((n:ℝ)+1))/2 := by dsimp [a]; rw [div_div,mul_comm (2:ℝ)]
  have he : Real.exp (-S) ≤ (Real.exp (-(m/4)*|D|) * ∏ j, Real.exp (-(m/4)*|x j|)) * Real.exp (-a*‖p i‖) := by
    rw [←Real.exp_sum,←Finset.mul_sum,←Real.exp_add,←Real.exp_add,Real.exp_le_exp,ha]
    nlinarith [mul_le_mul_of_nonneg_left hdisp hm.le,mul_le_mul_of_nonneg_left hx hm.le]
  exact he.trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => (Real.exp_pos (-a*‖p j‖)).le) (Finset.mem_univ i)) (by positivity))

theorem normal_winding_trace_majorant {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) {w : ℤ} (hw : w ≠ 0)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) (x : Fin n → ℝ) :
    ‖normalWindingTrace m L θ w u p x‖ ≤ (L*(4*2^(n+1))) *
      ((Real.exp (-(m/4)*|(w:ℝ)*L|) * ∏ j, Real.exp (-(m/4)*|x j|)) * ∑ i, Real.exp (-(L/(2*((n:ℝ)+1)))*‖p i‖)) := by
  let d := normalOpenIncrements ((w:ℝ)*L) x
  let A := fun j => normalDiracCover normalCoverGamma5 m (p j) (d j)*diracSlash (u j).val
  have hA j : ‖A j‖ ≤ 2*Real.exp (-normalCoverEnergy m (p j)*|d j|) := by
    apply (norm_mul_le _ _).trans
    rw [wilson_slash_opnorm,(u j).property,mul_one]
    exact normal_dirac_cover_bound _ normal_cover_gamma_norm hm _ _
  have hp : ‖(List.ofFn A).prod‖ ≤ 2^(n+1)*Real.exp (-(∑ j, normalCoverEnergy m (p j)*|d j|)) := by
    apply (List.norm_prod_le _).trans
    rw [List.map_ofFn,List.prod_ofFn]
    apply (Finset.prod_le_prod (fun j _ => norm_nonneg (A j)) (fun j _ => hA j)).trans_eq
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_sum,
      neg_mul,Finset.sum_neg_distrib]
  rw [normalWindingTrace,norm_mul,normal_loop_phase_norm hL]
  have ht := (wilson_trace_le_opnorm (List.ofFn A).prod).trans (mul_le_mul_of_nonneg_left hp (by norm_num))
  calc _ ≤ L * (4*(2^(n+1)*Real.exp (-(∑ j, normalCoverEnergy m (p j)*|d j|)))) := mul_le_mul_of_nonneg_left ht hL.le
       _ = (L*(4*2^(n+1)))*Real.exp (-(∑ j, normalCoverEnergy m (p j)*|d j|)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (normal_winding_decay hm hL hw p x) (by positivity)

local instance normalWindingMatrixSpace : MeasurableSpace DiracMatrix := borel _
local instance normalWindingMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_winding_trace_measurable {Z : Type*} [MeasurableSpace Z] (m L θ : ℝ) (w : ℤ)
    (u : Fin (n+1) → UnitVector OSFourSpace) {p : Z → Fin (n+1) → OSFourSpace} (hp : ∀ j, Measurable (p · j))
    {x : Z → Fin n → ℝ} (hx : ∀ j, Measurable (x · j)) : Measurable (fun z => normalWindingTrace m L θ w u (p z) (x z)) := by
  let A := fun j z => normalDiracCover normalCoverGamma5 m (p z j) (normalOpenIncrements ((w:ℝ)*L) (x z) j)*diracSlash (u j).val
  have hd (j : Fin (n+1)) : Measurable (fun z => normalOpenIncrements ((w:ℝ)*L) (x z) j) := by
    refine Fin.cases ?_ (fun i => hx i) j
    exact measurable_const.sub (Finset.measurable_sum _ (fun i _ => hx i))
  have hA (j) : Measurable (A j) := (normal_cover_args_measurable _ _ (hp j) (hd j)).mul_const _
  have hl (l : List (Fin (n+1))) : Measurable (fun z => (l.map (fun j => A j z)).prod) := by
    induction l with
    | nil => exact measurable_const
    | cons j l ih => exact (hA j).mul ih
  have hP := hl (List.ofFn (fun i : Fin (n+1) => i))
  simp only [List.map_ofFn,Function.comp_def] at hP
  exact measurable_const.mul ((Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp hP)

theorem normal_carrier_exponential {a : ℝ} (ha : 0 < a) :
    Integrable (fun k : OSFourSpace => Real.exp (-a*‖k‖)) := by
  apply (integrable_fun_norm_addHaar (E := OSFourSpace) volume (f := fun y => Real.exp (-a*y))).mpr
  simpa only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul,Real.rpow_one,Real.rpow_natCast]
    using integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := (3:ℕ)) (by norm_num) le_rfl ha

end UV

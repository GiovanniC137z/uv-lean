import UV.ContinueHeatMaxwellChordMarks
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! A common integrable four-momentum majorant for shifted Gaussian
Wilson marks, uniform in the external momentum near its soft limit. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

local instance : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

def heatLoopMajorant (k : EuclideanPlaneMomentum) : ℝ := Real.exp (-‖k‖^2/4)

theorem heat_loop_majorant_integrable : Integrable heatLoopMajorant := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=EuclideanPlaneMomentum)
    (b:=((4:ℂ)⁻¹)) (by norm_num) 0 0).norm
  change Integrable (fun k : EuclideanPlaneMomentum => Real.exp (-‖k‖^2/4))
  convert h using 1
  ext x
  simp [Complex.norm_exp,Complex.mul_re,←Complex.ofReal_pow]
  ring

private theorem heat_exp_absorb (r : ℝ) (hr : 0≤r) (n : ℕ) :
    (1+r)^n*Real.exp (-r^2/2) ≤ Real.exp ((n:ℝ)^2)*Real.exp (-r^2/4) := by
  have hx : 1+r≤Real.exp r := by linarith [Real.add_one_le_exp r]
  calc _ ≤ (Real.exp r)^n*Real.exp (-r^2/2) := by gcongr
       _ = Real.exp ((n:ℝ)*r-r^2/2) := by rw [←Real.exp_nat_mul,←Real.exp_add];congr 1;ring
       _ ≤ _ := by rw [←Real.exp_add,Real.exp_le_exp];nlinarith [sq_nonneg (r/2-n)]

def heatShiftGaussian (k : EuclideanPlaneMomentum) (s : ℝ) : ℝ :=
  Real.exp (-‖k‖^2)*heatShiftFactor ⟪k,softLongitudinal.val⟫ s

theorem heat_shift_gaussian_bound (k : EuclideanPlaneMomentum) {s : ℝ} (hs : |s|≤1) :
    heatShiftGaussian k s ≤ Real.exp 2 * Real.exp (-‖k‖^2/2) := by
  have h := (abs_real_inner_le_norm k softLongitudinal.val)
  rw [softLongitudinal.property,mul_one] at h
  have hp : |⟪k,softLongitudinal.val⟫*s| ≤ ‖k‖ :=
    (abs_mul _ _).le.trans ((mul_le_mul h hs (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  simp only [heatShiftGaussian,heatShiftFactor,←Real.exp_add,Real.exp_le_exp]
  nlinarith [(abs_le.mp hp).1,sq_nonneg (‖k‖-2),sq_nonneg s]

/-- The zeroth and first two longitudinal derivatives of the same affine
vector polynomial times the shifted Gaussian. -/
def heatAffineMark (k y w : EuclideanPlaneMomentum) (s : ℝ) : EuclideanPlaneMomentum :=
  heatShiftGaussian k s • (y+s • w)

def heatAffineFirst (k y w : EuclideanPlaneMomentum) (s : ℝ) : EuclideanPlaneMomentum :=
  let L := -2*⟪k,softLongitudinal.val⟫-2*s
  heatShiftGaussian k s • (L • (y+s • w)+w)

def heatAffineSecond (k y w : EuclideanPlaneMomentum) (s : ℝ) : EuclideanPlaneMomentum :=
  let L := -2*⟪k,softLongitudinal.val⟫-2*s
  heatShiftGaussian k s • ((L^2-2) • (y+s • w)+(2*L) • w)

theorem heat_affine_derivatives (k y w : EuclideanPlaneMomentum) (s : ℝ) :
    HasDerivAt (heatAffineMark k y w) (heatAffineFirst k y w s) s ∧
    HasDerivAt (heatAffineFirst k y w) (heatAffineSecond k y w s) s := by
  let j := ⟪k,softLongitudinal.val⟫
  let L := fun s : ℝ => -2*j-2*s
  have ha : HasDerivAt (heatShiftGaussian k) (L s*heatShiftGaussian k s) s := by
    convert (heatShiftFactor_hasDerivAt j s).const_mul (Real.exp (-‖k‖^2)) using 1
    dsimp [heatShiftGaussian,L,j];ring
  have hb : HasDerivAt (fun s : ℝ => y+s • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add y
  have hL : HasDerivAt L (-2) s := by simpa [L] using (((hasDerivAt_id s).const_mul 2).const_sub (-2*j))
  constructor
  · convert ha.smul hb using 1
    dsimp [heatAffineFirst,L,j];module
  · convert ha.smul (((hL.smul hb).add_const w)) using 1
    dsimp [heatAffineSecond,L,j];module

theorem heat_affine_uniform (k y w : EuclideanPlaneMomentum) {C : ℝ} (hC : 0≤C)
    (hy : ‖y‖ ≤ C*(1+‖k‖)^3) (hw : ‖w‖ ≤ C*(1+‖k‖)^3) {s : ℝ} (hs : |s|≤1) :
    let B := 24*C*Real.exp 2*Real.exp 25*heatLoopMajorant k
    ‖heatAffineMark k y w s‖≤B ∧ ‖heatAffineFirst k y w s‖≤B ∧ ‖heatAffineSecond k y w s‖≤B := by
  let R := 1+‖k‖
  let L := -2*⟪k,softLongitudinal.val⟫-2*s
  let g := heatShiftGaussian k s
  have hR : 1≤R := by dsimp only [R];linarith [norm_nonneg k]
  have hab : 0≤g := by dsimp [g,heatShiftGaussian,heatShiftFactor];positivity
  have hj := abs_real_inner_le_norm k softLongitudinal.val
  rw [softLongitudinal.property,mul_one] at hj
  have hL : |L|≤2*R := by
    dsimp only [L,R]
    rw [sub_eq_add_neg]
    calc _ ≤ |(-2)*⟪k,softLongitudinal.val⟫| + |-(2*s)| := abs_add_le _ _
         _ ≤ _ := by rw [abs_neg,abs_mul,abs_mul,abs_of_nonpos (by norm_num : (-2:ℝ)≤0),abs_of_nonneg (by norm_num : (0:ℝ)≤2),neg_neg];linarith
  have hL2 : |L^2-2| ≤ 6*R^2 := abs_le.mpr ⟨by nlinarith [sq_nonneg L,sq_nonneg (R-1)],
    by nlinarith [sq_le_sq.mpr (hL.trans_eq (abs_of_nonneg (by positivity : 0≤2*R)).symm),sq_nonneg (R-1)]⟩
  have hY : ‖y+s • w‖ ≤ 2*C*R^3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs]
    dsimp only [R] at *
    nlinarith [mul_le_of_le_one_left (norm_nonneg w) hs]
  have hR1 : 0≤C*R^3 := by positivity
  have hp : C*R^3 ≤ C*R^5 := by gcongr <;> first | exact hR | norm_num
  have hp' : C*R^4 ≤ C*R^5 := by gcongr <;> first | exact hR | norm_num
  have hL1 : ‖L • (y+s • w)+w‖ ≤ 24*C*R^5 := by
    refine (norm_add_le _ _).trans ?_;rw [norm_smul,Real.norm_eq_abs]
    have hs' := mul_le_mul hL hY (norm_nonneg _) (by positivity)
    change ‖w‖≤C*R^3 at hw
    nlinarith
  have hL' : ‖(L^2-2) • (y+s • w)+(2*L) • w‖ ≤ 24*C*R^5 := by
    refine (norm_add_le _ _).trans ?_;rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have hs' := mul_le_mul hL2 hY (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)) hw (norm_nonneg _) (by positivity)
    change ‖w‖≤C*R^3 at hw
    dsimp only [R] at h2 ⊢ hp hp'
    nlinarith
  have transfer (v : EuclideanPlaneMomentum) (hv : ‖v‖≤24*C*R^5) :
      ‖g • v‖≤24*C*Real.exp 2*Real.exp 25*heatLoopMajorant k := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hab]
    have h := mul_le_mul (heat_shift_gaussian_bound k hs) hv (norm_nonneg _) (by positivity)
    have h' := mul_le_mul_of_nonneg_left (heat_exp_absorb ‖k‖ (norm_nonneg _) 5)
      (show 0≤24*C*Real.exp 2 by positivity)
    norm_num only [Nat.cast_ofNat,show (5:ℝ)^2=25 by norm_num] at h'
    dsimp [g,R,heatLoopMajorant] at *
    nlinarith
  exact ⟨transfer _ (by nlinarith),transfer _ hL1,transfer _ hL'⟩

end UV.HeatMaxwell

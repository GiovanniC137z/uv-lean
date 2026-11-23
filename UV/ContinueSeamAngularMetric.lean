import UV.ContinueCurvatureModes
import UV.ContinueTemporalPolarization
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Two oriented seam angles on a fixed carrier. The integral character
uses the lattice covector (q,−q). Unit principal axes carry the metric
projectors, and the fixed diagonal circle is averaged with Haar probability. -/

noncomputable section

namespace UV.SeamAngular

open Real MeasureTheory Matrix Set
open scoped Matrix BigOperators ComplexConjugate

abbrev SeamCircle := AddCircle ((2:ℝ)*π)
abbrev AngularMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev AngularCoordinates := Fin 2 → ℝ

private instance : Fact (0 < (2 : ℝ)*π) := ⟨by positivity⟩

def seamCharacter (m n : ℤ) (θ₁ θ₂ : SeamCircle) : ℂ := fourier m θ₁ * fourier n θ₂

private theorem angular_character_translate (m : ℤ) (x z : SeamCircle) :
    fourier m (x+z) = fourier m x * fourier m z := by
  simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]

theorem seam_diagonal_gauss_projection (m n : ℤ) (θ₁ θ₂ : SeamCircle) :
    (∫ ζ : SeamCircle, seamCharacter m n (θ₁+ζ) (θ₂+ζ) ∂AddCircle.haarAddCircle) =
      if n = -m then seamCharacter m n θ₁ θ₂ else 0 := by
  have he (ζ : SeamCircle) : seamCharacter m n (θ₁+ζ) (θ₂+ζ) =
      seamCharacter m n θ₁ θ₂ * fourier (m+n) ζ := by
    simp only [seamCharacter,angular_character_translate,fourier_add]
    ring
  simp_rw [he]
  rw [integral_const_mul,UV.ContinueCurvatureModes.circle_character_integral]
  by_cases h : n = -m
  · simp [h]
  · rw [if_neg h,if_neg (show m+n ≠ 0 by omega),mul_zero]

def seamOrbit : AngularCoordinates := ![1,1]
def seamDifference : AngularCoordinates := ![1,-1]

/-- The normalized axes on the two-angle fibre. The actual integral
orbit and charge covectors above have length √2. -/
def seamUnitAxis (relative : Bool) : SectorPlane.UnitVector (EuclideanSpace ℝ (Fin 2)) :=
  ⟨WithLp.toLp 2 (fun i => (if relative then seamDifference i else seamOrbit i)/√2),by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    cases relative <;> simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,seamOrbit,seamDifference,
      Real.norm_eq_abs,div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> norm_num⟩

def seamMetric (d a : ℝ) : AngularMatrix :=
  !![(d+a)/2,(d-a)/2; (d-a)/2,(d+a)/2]

def seamForm (M : AngularMatrix) (v : AngularCoordinates) : ℝ := dotProduct v (M *ᵥ v)

theorem seam_metric_unit_projectors (d a : ℝ) (i j : Fin 2) :
    seamMetric d a i j =
      d*(seamUnitAxis false).val i*(seamUnitAxis false).val j +
      a*(seamUnitAxis true).val i*(seamUnitAxis true).val j := by
  have h := sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : √(2:ℝ) ≠ 0 := by positivity
  fin_cases i <;> fin_cases j <;> simp [seamMetric,seamUnitAxis,seamOrbit,seamDifference] <;>
    field_simp <;> nlinarith [h,show 0 = d*((√(2:ℝ))^2-2) by rw [h]; ring,
      show 0 = a*((√(2:ℝ))^2-2) by rw [h]; ring]

theorem seam_metric_quadratic (d a : ℝ) (v : AngularCoordinates) :
    seamForm (seamMetric d a) v = (d*(v 0+v 1)^2+a*(v 0-v 1)^2)/2 := by
  simp [seamForm,seamMetric,dotProduct,mulVec,Fin.sum_univ_two]
  ring

theorem seam_metric_posDef {d a : ℝ} (hd : 0 < d) (ha : 0 < a) : (seamMetric d a).PosDef := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro v hv
    change 0 < seamForm (seamMetric d a) v
    rw [seam_metric_quadratic]
    have hn : v 0+v 1 ≠ 0 ∨ v 0-v 1 ≠ 0 := by
      by_contra! h
      apply hv
      funext i
      fin_cases i
      · change v 0 = 0
        linarith only [h.1,h.2]
      · change v 1 = 0
        linarith only [h.1,h.2]
    apply div_pos _ two_pos
    rcases hn with hp | hm
    · exact add_pos_of_pos_of_nonneg (mul_pos hd (sq_pos_of_ne_zero hp)) (mul_nonneg ha.le (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hd.le (sq_nonneg _)) (mul_pos ha (sq_pos_of_ne_zero hm))

theorem seam_metric_det (d a : ℝ) : (seamMetric d a).det = d*a := by
  rw [seamMetric,Matrix.det_fin_two_of]
  ring

/-- The actual inverse has the reciprocal principal metric on each axis. -/
theorem seam_metric_inverse {d a : ℝ} (hd : d ≠ 0) (ha : a ≠ 0) :
    (seamMetric d a)⁻¹ = seamMetric d⁻¹ a⁻¹ := by
  rw [Matrix.inv_def,seam_metric_det,Ring.inverse_eq_inv,Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [seamMetric] <;> field_simp <;> ring

/-- The character's relative charge covector observes the squared
diagonal orbit length divided by the determinant of the entire metric. -/
theorem seam_selection_identity (M : AngularMatrix) (q : ℤ) :
    seamForm M⁻¹ ((q:ℝ) • seamDifference) = (q:ℝ)^2*seamForm M seamOrbit/M.det := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.adjugate_fin_two]
  simp [seamForm,seamDifference,seamOrbit,dotProduct,mulVec,Fin.sum_univ_two,div_eq_mul_inv]
  ring

theorem seam_distinct_pair_energies {r : ℝ} (hr : 0 < r) (q : ℤ) :
    let M₁ := seamMetric 1 (r^8)
    let M₂ := seamMetric (r^8) 1
    M₁.PosDef ∧ M₂.PosDef ∧ √M₁.det = r^4 ∧ √M₂.det = r^4 ∧
    (∀ i : Fin 2, seamForm M₁⁻¹ (Pi.single i 1) = (1+(r^8)⁻¹)/2 ∧
      seamForm M₂⁻¹ (Pi.single i 1) = (1+(r^8)⁻¹)/2) ∧
    seamForm M₁⁻¹ ((q:ℝ) • seamDifference) = 2*(q:ℝ)^2/(r^8) ∧
    seamForm M₂⁻¹ ((q:ℝ) • seamDifference) = 2*(q:ℝ)^2 := by
  intro M₁ M₂
  have h8 : 0 < r^8 := pow_pos hr _
  have hvol : √(r^8) = r^4 := by rw [show r^8 = (r^4)^2 by ring,sqrt_sq (by positivity)]
  have h1 := seam_metric_inverse one_ne_zero h8.ne'
  have h2 := seam_metric_inverse h8.ne' one_ne_zero
  refine ⟨seam_metric_posDef zero_lt_one h8,seam_metric_posDef h8 zero_lt_one,
    by simp [M₁,seam_metric_det,hvol],by simp [M₂,seam_metric_det,hvol],?_,?_,?_⟩
  · intro i
    dsimp only [M₁,M₂]
    rw [h1,h2,seam_metric_quadratic,seam_metric_quadratic]
    fin_cases i <;> norm_num [Pi.single_apply] <;> ring
  · rw [show M₁⁻¹ = _ from h1,seam_metric_quadratic]
    simp [seamDifference,div_eq_mul_inv]
    ring
  · rw [show M₂⁻¹ = _ from h2,seam_metric_quadratic]
    simp [seamDifference]
    ring

end UV.SeamAngular

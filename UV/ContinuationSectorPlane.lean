import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! Geometry of one locked sector plane, from equations
`eq:uvfinal-offset-labels`, `eq:locking`, `eq:pullback-metric`,
`eq:fw-physical-endpoints`, and `eq:fw-cut-routing` of the expanded source.
Sector, evolution branch, carrier unit, and affine offset are distinct data. -/

noncomputable section

namespace UV.SectorPlane

open scoped RealInnerProductSpace

/-- The two support sectors. These labels do not specify an evolution order. -/
inductive Sector where
  | N
  | A
  deriving DecidableEq

/-- Ascending or descending order in the centred carrier coordinate. -/
inductive Evolution where
  | ascending
  | descending
  deriving DecidableEq

def sectorSign : Sector → ℝ
  | .N => 1
  | .A => -1

def evolutionSign : Evolution → ℝ
  | .ascending => 1
  | .descending => -1

@[simp] theorem sectorSign_sq (s : Sector) : sectorSign s ^ 2 = 1 := by
  cases s <;> norm_num [sectorSign]

@[simp] theorem evolutionSign_sq (ε : Evolution) : evolutionSign ε ^ 2 = 1 := by
  cases ε <;> norm_num [evolutionSign]

@[simp] theorem sectorSign_abs (s : Sector) : |sectorSign s| = 1 := by
  cases s <;> norm_num [sectorSign]

@[simp] theorem evolutionSign_abs (ε : Evolution) : |evolutionSign ε| = 1 := by
  cases ε <;> norm_num [evolutionSign]

abbrev UnitVector (E : Type*) [Norm E] := {u : E // ‖u‖ = 1}

/-- The diamond data `(s,b_s)` and its assigned unit carrier on a fixed copy.
The ambient axis is positive-norm GT geometry. -/
structure Plane (E : Type*) [Norm E] where
  s : Sector
  b_s : ℝ
  Ghat : UnitVector E

abbrev Spatial := EuclideanSpace ℝ (Fin 3)

variable {E : Type*} [NormedAddCommGroup E]

def Plane.poleUnit (diamond : Plane E) : UnitVector E := diamond.Ghat

def Plane.eta (diamond : Plane E) (ε : Evolution) : ℝ :=
  sectorSign diamond.s * evolutionSign ε

@[simp] theorem Plane.eta_sq (diamond : Plane E) (ε : Evolution) :
    diamond.eta ε ^ 2 = 1 := by
  rw [Plane.eta, mul_pow, sectorSign_sq, evolutionSign_sq, mul_one]

/-- Paired N/A copies use the same fixed pole unit. Their sector signs
change the signed boundary side outside the geometric direction. -/
theorem paired_sector_pole (Ghat : UnitVector E) (bN bA : ℝ) (ε : Evolution) :
    (Plane.mk .N bN Ghat).poleUnit = (Plane.mk .A bA Ghat).poleUnit ∧
      (Plane.mk .N bN Ghat).eta ε = -(Plane.mk .A bA Ghat).eta ε := by
  constructor
  · rfl
  · simp [Plane.eta, sectorSign]

section Geometry

variable [InnerProductSpace ℝ E]

def Plane.embedGTL (diamond : Plane E) (X₀ : ℝ) (x : Spatial) : E × Spatial :=
  ((X₀ + diamond.b_s) • (diamond.Ghat : E), x)

def Plane.centeredGT (diamond : Plane E) (X_GT : E) : ℝ :=
  ⟪(diamond.Ghat : E), X_GT⟫ - diamond.b_s

def Plane.transverse (diamond : Plane E) (X_GT : E) : E :=
  X_GT - ⟪(diamond.Ghat : E), X_GT⟫ • (diamond.Ghat : E)

theorem Plane.inner_carrier_self (diamond : Plane E) :
    ⟪(diamond.Ghat : E), (diamond.Ghat : E)⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, diamond.Ghat.property]
  norm_num

theorem Plane.centered_embed (diamond : Plane E) (X₀ : ℝ) (x : Spatial) :
    diamond.centeredGT (diamond.embedGTL X₀ x).1 = X₀ := by
  simp [Plane.centeredGT, Plane.embedGTL, real_inner_smul_right, diamond.inner_carrier_self]

theorem Plane.transverse_embed (diamond : Plane E) (X₀ : ℝ) (x : Spatial) :
    diamond.transverse (diamond.embedGTL X₀ x).1 = 0 := by
  simp [Plane.transverse, Plane.embedGTL, real_inner_smul_right, diamond.inner_carrier_self]

/-- The independent momentum binder selects the carrier ray; it leaves the
real signed coefficient free. The same projector can test a position. -/
theorem Plane.alignment_iff (diamond : Plane E) (q : E) :
    diamond.transverse q = 0 ↔ ∃ t : ℝ, q = t • (diamond.Ghat : E) := by
  constructor
  · intro h
    exact ⟨_, sub_eq_zero.mp h⟩
  · rintro ⟨t, rfl⟩
    simp [Plane.transverse, real_inner_smul_right, diamond.inner_carrier_self]

theorem Plane.affine_fourier_pairing (diamond : Plane E)
    (X₀ : ℝ) (x : Spatial) (p_GT : E) :
    ⟪p_GT, (diamond.embedGTL X₀ x).1⟫ =
      ⟪(diamond.Ghat : E), p_GT⟫ * (X₀ + diamond.b_s) := by
  rw [Plane.embedGTL, real_inner_smul_right, real_inner_comm p_GT, mul_comm]

theorem Plane.embed_centered_of_locked (diamond : Plane E) (X_GT : E) (x : Spatial)
    (h : diamond.transverse X_GT = 0) :
    diamond.embedGTL (diamond.centeredGT X_GT) x = (X_GT, x) := by
  change ((⟪(diamond.Ghat : E), X_GT⟫ - diamond.b_s + diamond.b_s) •
    (diamond.Ghat : E), x) = (X_GT, x)
  rw [sub_add_cancel]
  exact Prod.ext (sub_eq_zero.mp h).symm rfl

theorem Plane.locked_GT_difference (diamond : Plane E) (X₀ Y₀ : ℝ) (x y : Spatial) :
    (diamond.embedGTL X₀ x).1 - (diamond.embedGTL Y₀ y).1 =
      (X₀ - Y₀) • (diamond.Ghat : E) := by
  simp only [Plane.embedGTL, ← sub_smul, add_sub_add_right_eq_sub]

/-- Exact metric pullback on finite displacements of the affine embedding. -/
theorem Plane.pullback_quadratic_form (diamond : Plane E) (X₀ Y₀ : ℝ) (x y : Spatial) :
    ‖(diamond.embedGTL X₀ x).1 - (diamond.embedGTL Y₀ y).1‖ ^ 2 -
      ‖(diamond.embedGTL X₀ x).2 - (diamond.embedGTL Y₀ y).2‖ ^ 2 =
      (X₀ - Y₀) ^ 2 - ‖x - y‖ ^ 2 := by
  rw [diamond.locked_GT_difference, norm_smul, diamond.Ghat.property,
    mul_one, Real.norm_eq_abs, sq_abs]
  rfl

end Geometry

def Plane.orientedGT (diamond : Plane E) (X₀ : ℝ) : ℝ := sectorSign diamond.s * X₀

def Plane.calibratedGT (diamond : Plane E) (cGT t : ℝ) : ℝ :=
  sectorSign diamond.s * cGT * t

def Plane.drift [SMul ℝ E] (diamond : Plane E) (cGT : ℝ) : E :=
  (sectorSign diamond.s * cGT) • (diamond.Ghat : E)

theorem Plane.drift_norm [NormedSpace ℝ E] (diamond : Plane E) {cGT : ℝ} (hc : 0 < cGT) :
    ‖diamond.drift cGT‖ = cGT := by
  simp [Plane.drift, norm_smul, Real.norm_eq_abs, diamond.Ghat.property, abs_of_pos hc]

theorem Plane.orientedGT_calibrated (diamond : Plane E) (cGT t : ℝ) :
    diamond.orientedGT (diamond.calibratedGT cGT t) = cGT * t := by
  unfold Plane.orientedGT Plane.calibratedGT
  calc
    _ = sectorSign diamond.s ^ 2 * cGT * t := by ring
    _ = cGT * t := by simp

/-- The positive intrinsic GT measure in clock coordinates has density
`cGT` on both sectors. The spatial variable is unaffected. -/
theorem Plane.clock_measure_pullback (diamond : Plane E) {cGT : ℝ} (hc : 0 < cGT)
    (f : ℝ → ℝ) :
    (∫ X₀, f X₀) = cGT * ∫ t, f (diamond.calibratedGT cGT t) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (sectorSign diamond.s * cGT)
  rw [abs_inv, abs_mul, sectorSign_abs, abs_of_pos hc, one_mul,
    smul_eq_mul] at h
  change (∫ X₀, f X₀) = cGT * ∫ t, f ((sectorSign diamond.s * cGT) * t)
  rw [h, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

theorem Plane.transport_phase_and_shell (diamond : Plane E) (X₀ kParallel : ℝ)
    (p : Spatial) :
    diamond.orientedGT X₀ * (sectorSign diamond.s * kParallel) = X₀ * kParallel ∧
      (sectorSign diamond.s * kParallel) ^ 2 - ‖p‖ ^ 2 = kParallel ^ 2 - ‖p‖ ^ 2 := by
  constructor
  · calc
      _ = sectorSign diamond.s ^ 2 * (X₀ * kParallel) := by unfold Plane.orientedGT; ring
      _ = _ := by simp
  · rw [mul_pow, sectorSign_sq, one_mul]

def Plane.physicalIn (diamond : Plane E) (R : ℝ) : ℝ := -sectorSign diamond.s * R

def Plane.physicalOut (diamond : Plane E) (R : ℝ) : ℝ := sectorSign diamond.s * R

def carrierBra (ε : Evolution) (R : ℝ) : ℝ := evolutionSign ε * R

def carrierKet (ε : Evolution) (R : ℝ) : ℝ := -evolutionSign ε * R

theorem Plane.bra_is_physical_out_iff (diamond : Plane E) (ε : Evolution)
    {R : ℝ} (hR : 0 < R) :
    carrierBra ε R = diamond.physicalOut R ↔ diamond.eta ε = 1 := by
  have hNR : -R ≠ R := by linarith
  have hRN : R ≠ -R := hNR.symm
  rcases diamond with ⟨s, b_s, Ghat⟩
  cases s <;> cases ε <;> norm_num [carrierBra, Plane.physicalOut, Plane.eta,
    sectorSign, evolutionSign, hNR, hRN]

theorem Plane.ket_is_physical_out_iff (diamond : Plane E) (ε : Evolution)
    {R : ℝ} (hR : 0 < R) :
    carrierKet ε R = diamond.physicalOut R ↔ diamond.eta ε = -1 := by
  have hNR : -R ≠ R := by linarith
  have hRN : R ≠ -R := hNR.symm
  rcases diamond with ⟨s, b_s, Ghat⟩
  cases s <;> cases ε <;> norm_num [carrierKet, Plane.physicalOut, Plane.eta,
    sectorSign, evolutionSign, hNR, hRN]

/-- The cut reverses the complete intrinsic covector, including spatial momentum. -/
def cutArrow (ε : Evolution) (p : ℝ × Spatial) : ℝ × Spatial :=
  (evolutionSign ε * p.1, evolutionSign ε • p.2)

theorem Plane.cut_routing (diamond : Plane E) (ε : Evolution) (κ : ℝ) (p : Spatial) :
    diamond.eta ε * (cutArrow ε (sectorSign diamond.s * κ, p)).1 = κ := by
  change (sectorSign diamond.s * evolutionSign ε) *
    (evolutionSign ε * (sectorSign diamond.s * κ)) = κ
  calc
    _ = sectorSign diamond.s ^ 2 * evolutionSign ε ^ 2 * κ := by ring
    _ = _ := by simp

theorem cut_arrow_jacobian_abs (ε : Evolution) :
    |(Matrix.diagonal (fun _ : Fin 4 => evolutionSign ε)).det| = 1 := by
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_pow,
    evolutionSign_abs, one_pow]

theorem Plane.cut_positive_weight_independent (diamond : Plane E) (ε : Evolution)
    {κ : ℝ} (hκ : 0 < κ) (p : Spatial) :
    0 < diamond.eta ε * (cutArrow ε (sectorSign diamond.s * κ, p)).1 ∧
      0 < (2 * κ)⁻¹ := by
  rw [diamond.cut_routing]
  exact ⟨hκ, inv_pos.mpr (by positivity)⟩

end UV.SectorPlane

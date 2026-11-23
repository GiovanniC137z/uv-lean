import UV.ContinuePoleResidueSchur
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! What the source's scalar expression measures for a normalized vector
in a degenerate pole kernel. -/

noncomputable section
open Filter Set ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def poleLift (T : S →L[ℂ] H) (R : H →L[ℂ] H) (v : S) : WithLp 2 (S × H) :=
  WithLp.toLp 2 (v, R (T v))

private theorem poleLift_inner (T : S →L[ℂ] H) (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x y : S) : ⟪poleLift T R x, poleLift T R y⟫_ℂ = ⟪x, closingTemporalMark T 1 R R y⟫_ℂ := by
  change ⟪x, y⟫_ℂ + ⟪R (T x), R (T y)⟫_ℂ = _
  simp only [closingTemporalMark, Complex.ofReal_one, one_smul, add_apply, one_apply,
    closing_sandwich_apply, mul_apply, inner_add_right, adjoint_inner_right]
  rw [← hR.adjoint_eq, adjoint_inner_left, hR.adjoint_eq]

/-- A supported inverse of the compressed positive derivative bounds the
diagonal residue in every unit direction fixed by the self-adjoint projection.
Equality in the lower estimate characterizes eigenvectors of that inverse. -/
theorem closing_compressed_residue_direction (T : S →L[ℂ] H) (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (P Z : S →L[ℂ] S) (hP : IsSelfAdjoint P)
    (hs : P * Z = Z) (hi : (P * closingTemporalMark T 1 R R * P) * Z = P)
    (v : S) (hv : ‖v‖ = 1) (hp : P v = v) :
    let r := closingSlotResidue T R v
    (⟪v, Z v⟫_ℂ).im = 0 ∧ r ≤ (⟪v, Z v⟫_ℂ).re ∧ (⟪v, Z v⟫_ℂ).re ≤ 1 ∧
      ((⟪v, Z v⟫_ℂ).re = r ↔ Z v = (r : ℂ) • v) := by
  let J := closingTemporalMark T 1 R R
  let a := 1 + ‖R (T v)‖ ^ 2
  let r := a⁻¹
  let g := poleLift T R
  have ha : 0 < a := by dsimp [a]; positivity
  have hPz : P (Z v) = Z v := DFunLike.congr_fun hs v
  have hPJ : P (J (Z v)) = v := by
    have h := DFunLike.congr_fun hi v
    change P (J (P (Z v))) = P v at h
    simpa only [hPz, hp] using h
  have hprod (x : S) (hx : P x = x) : ⟪g x, g (Z v)⟫_ℂ = ⟪x, v⟫_ℂ := by
    calc
      ⟪g x, g (Z v)⟫_ℂ = ⟪x, J (Z v)⟫_ℂ := poleLift_inner T R hR _ _
      _ = ⟪P x, J (Z v)⟫_ℂ := congrArg (fun w : S => ⟪w, J (Z v)⟫_ℂ) hx.symm
      _ = ⟪x, P (J (Z v))⟫_ℂ := hP.isSymmetric _ _
      _ = ⟪x, v⟫_ℂ := congrArg (fun w : S => ⟪x, w⟫_ℂ) hPJ
  have hcross : ⟪g (Z v), g v⟫_ℂ = 1 := by
    rw [← inner_conj_symm, hprod v hp, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have hself : ‖g (Z v)‖^2 = (⟪v, Z v⟫_ℂ).re := by
    rw [@norm_sq_eq_re_inner ℂ, hprod _ hPz, inner_re_symm]
    rfl
  have hv2 : ‖g v‖^2 = a := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖v‖^2 + ‖R (T v)‖^2 = a
    simp [hv,a]
  have hrpos : 0 < r := inv_pos.mpr ha
  have hd : ‖g (Z v) - (r : ℂ) • g v‖^2 = (⟪v, Z v⟫_ℂ).re - r := by
    have hrre : RCLike.re (r : ℂ) = r := rfl
    rw [@norm_sub_sq ℂ, inner_smul_right, hcross, mul_one, hrre,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, mul_pow, hself, hv2]
    change _ - 2*a⁻¹ + (a⁻¹)^2*a = _ - a⁻¹
    field_simp
    ring
  have hzIm : (⟪v, Z v⟫_ℂ).im = 0 := by
    rw [← inner_conj_symm, ← hprod (Z v) hPz, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hZnorm : ‖Z v‖^2 ≤ (⟪v, Z v⟫_ℂ).re := by
    rw [← hself, WithLp.prod_norm_sq_eq_of_L2]
    change ‖Z v‖^2 ≤ ‖Z v‖^2 + ‖R (T (Z v))‖^2
    linarith [sq_nonneg ‖R (T (Z v))‖]
  have hZinner : (⟪v, Z v⟫_ℂ).re ≤ ‖Z v‖ := by
    simpa only [hv, one_mul] using (re_inner_le_norm (𝕜 := ℂ) v (Z v))
  have hUpper : ‖Z v‖ ≤ 1 := by nlinarith [sq_nonneg (‖Z v‖ - 1)]
  change (⟪v, Z v⟫_ℂ).im = 0 ∧ r ≤ (⟪v, Z v⟫_ℂ).re ∧ (⟪v, Z v⟫_ℂ).re ≤ 1 ∧
    ((⟪v, Z v⟫_ℂ).re = r ↔ Z v = (r : ℂ) • v)
  refine ⟨hzIm, by linarith [sq_nonneg ‖g (Z v) - (r : ℂ) • g v‖],
    hZinner.trans hUpper, ?_⟩
  constructor
  · intro he
    rw [he,sub_self,sq_eq_zero_iff,norm_eq_zero,sub_eq_zero] at hd
    exact congrArg (fun x : WithLp 2 (S × H) => (WithLp.ofLp x).1) hd
  · intro he
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp

/-- If the pole kernel has any dimension, the reciprocal diagonal
derivative is a lower bound for the actual real diagonal residue, which
is at most one. Equality with the lower bound
holds exactly when the unit vector is a residue eigenvector with that
weight. The proof computes the squared distance between the two lifts. -/
theorem closing_schur_residue_lower_bound {A : S →L[ℂ] S} {B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (E₀ : ℝ) (Z : S →L[ℂ] S) (v : S) (hv : ‖v‖ = 1)
    (hk : closingPolePencil A B T ((-E₀ : ℝ) : ℂ) v = 0)
    (hb : IsUnit (closingShift B (-E₀ : ℝ)))
    (hu : ∀ᶠ z in 𝓝[≠] ((-E₀ : ℝ) : ℂ), IsUnit (closingPolePencil A B T z))
    (hZ : Tendsto (fun z : ℂ => (z - ((-E₀ : ℝ) : ℂ)) • Ring.inverse (closingPolePencil A B T z))
      (𝓝[≠] ((-E₀ : ℝ) : ℂ)) (𝓝 Z)) :
    let R := closingResolvent B ((-E₀ : ℝ) : ℂ)
    let r := closingSlotResidue T R v
    (⟪v, Z v⟫_ℂ).im = 0 ∧ r ≤ (⟪v, Z v⟫_ℂ).re ∧ (⟪v, Z v⟫_ℂ).re ≤ 1 ∧
      ((⟪v, Z v⟫_ℂ).re = r ↔ Z v = (r : ℂ) • v) := by
  obtain ⟨hs, _, _, hi⟩ := closing_schur_measured_charge hA hB T 1 E₀ Z hb hu hZ
  exact closing_compressed_residue_direction T _ (closing_real_resolvent_selfAdjoint B hB (-E₀))
    _ Z (inverse_pole_projection_selfAdjoint _) hs (by simpa only [Complex.ofReal_one, one_smul] using hi)
    v hv (inverse_pole_projection_fixes hk)

end UV.SectorPlane

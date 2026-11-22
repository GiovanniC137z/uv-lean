import UV.FurtherTemporalAnalytic

/-! The limiting eigenspaces and full pencils are expressed in one fixed
orthonormal chart, including their contact and charge matrices. -/

noncomputable section
open Complex Filter Matrix Set
open scoped Topology Matrix Matrix.Norms.Elementwise

namespace UV

variable {d : ℕ}

abbrev TemporalUnitary (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def temporalBasis (U : TemporalUnitary d) (A : TemporalMatrix d) : TemporalMatrix d :=
  (U : TemporalMatrix d)ᴴ * A * U

theorem continuous_temporalBasis (U : TemporalUnitary d) : Continuous (temporalBasis U) :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem temporalBasis_mul (U : TemporalUnitary d) (A B : TemporalMatrix d) :
    temporalBasis U (A * B) = temporalBasis U A * temporalBasis U B := by
  have hU : (U : TemporalMatrix d) * (U : TemporalMatrix d)ᴴ = 1 := unitary.coe_mul_star_self U
  unfold temporalBasis
  simp only [mul_assoc]
  rw [← mul_assoc (U : TemporalMatrix d) _, hU, one_mul]

theorem temporalBasis_one (U : TemporalUnitary d) : temporalBasis U 1 = 1 := by
  unfold temporalBasis
  rw [mul_one]
  exact unitary.coe_star_mul_self U

theorem temporalBasis_add (U : TemporalUnitary d) (A B : TemporalMatrix d) :
    temporalBasis U (A + B) = temporalBasis U A + temporalBasis U B := by
  simp only [temporalBasis, mul_add, add_mul]

theorem temporalBasis_smul (U : TemporalUnitary d) (a : ℂ) (A : TemporalMatrix d) :
    temporalBasis U (a • A) = a • temporalBasis U A := by
  simp only [temporalBasis, Matrix.mul_smul, Matrix.smul_mul]

theorem temporalBasis_conjTranspose (U : TemporalUnitary d) (A : TemporalMatrix d) :
    temporalBasis U Aᴴ = (temporalBasis U A)ᴴ := by
  simp only [temporalBasis, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]

theorem temporalBasis_hermitian (U : TemporalUnitary d) {A : TemporalMatrix d} (hA : A.IsHermitian) :
    (temporalBasis U A).IsHermitian := by
  rw [Matrix.IsHermitian, ← temporalBasis_conjTranspose, hA.eq]

theorem temporalBasis_trace (U : TemporalUnitary d) (A : TemporalMatrix d) :
    (temporalBasis U A).trace = A.trace := by
  have hU : (U : TemporalMatrix d) * (U : TemporalMatrix d)ᴴ = 1 := unitary.coe_mul_star_self U
  rw [temporalBasis, Matrix.trace_mul_comm, ← mul_assoc, hU, one_mul]

theorem temporalBasis_injective (U : TemporalUnitary d) : Function.Injective (temporalBasis U) := by
  intro A B he
  have hU : (U : TemporalMatrix d) * (U : TemporalMatrix d)ᴴ = 1 := unitary.coe_mul_star_self U
  have h := congrArg (fun X => (U : TemporalMatrix d) * X * (U : TemporalMatrix d)ᴴ) he
  simpa only [temporalBasis, ← mul_assoc, hU, one_mul, mul_assoc A, mul_assoc B, mul_one] using h

theorem temporalBasis_isUnit_inverse (U : TemporalUnitary d) {A : TemporalMatrix d}
    (hA : IsUnit A) : temporalBasis U A⁻¹ = (temporalBasis U A)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← temporalBasis_mul, Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    temporalBasis_one]

theorem temporalBasis_pencil (U : TemporalUnitary d) (A : TemporalMatrix d) (z : ℂ) :
    temporalBasis U (furtherTemporalPencil A z) = furtherTemporalPencil (temporalBasis U A) z := by
  simp only [furtherTemporalPencil, temporalBasis_add, temporalBasis_smul, temporalBasis_one]

theorem temporalBasis_resolvent (U : TemporalUnitary d) {A : TemporalMatrix d} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    temporalBasis U (furtherTemporalResolvent A z) =
      furtherTemporalResolvent (temporalBasis U A) z := by
  unfold furtherTemporalResolvent
  rw [temporalBasis_isUnit_inverse U (furtherTemporalPencil_isUnit_of_im_ne_zero hA hz),
    temporalBasis_pencil]

theorem temporalBasis_coefficient (U : TemporalUnitary d) {A B : TemporalMatrix d}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C Q : TemporalMatrix d) {z : ℂ} (hz : z.im ≠ 0) :
    furtherTemporalCoefficient A B C Q z = furtherTemporalCoefficient
      (temporalBasis U A) (temporalBasis U B) (temporalBasis U C) (temporalBasis U Q) z := by
  unfold furtherTemporalCoefficient
  rw [← temporalBasis_resolvent U hA hz, ← temporalBasis_resolvent U hB hz,
    ← temporalBasis_conjTranspose]
  simp only [← temporalBasis_mul, temporalBasis_trace]

/-- The spectral projection on the energy in the original orthonormal slots.
Degenerate eigenvalues use the entire equal-energy eigenspace. -/
def furtherTemporalEnergyProjection {H : TemporalMatrix d} (hH : H.IsHermitian) (E : ℝ) :
    TemporalMatrix d :=
  let U : TemporalMatrix d := hH.eigenvectorUnitary
  U * temporalEnergyProjection hH.eigenvalues E * Uᴴ

theorem temporalBasis_energyProjection {H : TemporalMatrix d} (hH : H.IsHermitian) (E : ℝ) :
    temporalBasis hH.eigenvectorUnitary (furtherTemporalEnergyProjection hH E) =
      temporalEnergyProjection hH.eigenvalues E := by
  let U : TemporalUnitary d := hH.eigenvectorUnitary
  have hU : (U : TemporalMatrix d)ᴴ * (U : TemporalMatrix d) = 1 := unitary.coe_star_mul_self U
  change (U : TemporalMatrix d)ᴴ * ((U : TemporalMatrix d) *
    temporalEnergyProjection hH.eigenvalues E * (U : TemporalMatrix d)ᴴ) * (U : TemporalMatrix d) = _
  rw [← mul_assoc _ _ _, ← mul_assoc _ _ _, hU, one_mul, mul_assoc, hU, mul_one]

theorem temporalBasis_nonzero_energy_block {H : TemporalMatrix d} (hH : H.IsHermitian)
    (E : ℝ) (Q : TemporalMatrix d)
    (hq : furtherTemporalEnergyProjection hH E * Q * furtherTemporalEnergyProjection hH E ≠ 0) :
    temporalEnergyProjection hH.eigenvalues E * temporalBasis hH.eigenvectorUnitary Q *
      temporalEnergyProjection hH.eigenvalues E ≠ 0 := by
  intro hz
  apply hq
  apply temporalBasis_injective hH.eigenvectorUnitary
  rw [temporalBasis_mul, temporalBasis_mul, temporalBasis_energyProjection, hz]
  simp [temporalBasis]

theorem temporalBasis_bounded {C : ℝ → TemporalMatrix d} (U : TemporalUnitary d)
    (hC : ∃ K : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖C t‖ ≤ K) :
    ∃ K : ℝ, ∀ᶠ t in (atTop : Filter ℝ), ‖temporalBasis U (C t)‖ ≤ K := by
  obtain ⟨K, hK⟩ := hC
  obtain ⟨K', hK'⟩ := ((isCompact_closedBall (0 : TemporalMatrix d) K).image
    (continuous_temporalBasis U)).isBounded.exists_norm_le
  exact ⟨K', hK.mono fun t ht => hK' _ ⟨C t, by simpa using ht, rfl⟩⟩

end UV

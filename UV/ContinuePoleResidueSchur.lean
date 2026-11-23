import UV.ContinuePoleResidueCompression

/-! The positive boundary pencil, evaluated at the scalar carrier frequency
in the chosen sector plane. -/

noncomputable section
open Filter Set ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The slot Schur pencil using the eliminated channel's actual resolvent. -/
def closingPolePencil (A : S →L[ℂ] S) (B : H →L[ℂ] H) (T : S →L[ℂ] H)
    (z : ℂ) : S →L[ℂ] S :=
  closingInverseSlot A T (closingResolvent B z) z

theorem closing_pencil_selfAdjoint {A : S →L[ℂ] S} {B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H) (p : ℝ) :
    IsSelfAdjoint (closingPolePencil A B T (p : ℂ)) := by
  have h₁ : IsSelfAdjoint ((p : ℂ) • (1 : S →L[ℂ] S)) := by
    simp [IsSelfAdjoint, star_smul]
  exact (h₁.add hA).sub ((closing_real_resolvent_selfAdjoint B hB p).adjoint_conj T)

omit [CompleteSpace S] in
private theorem closing_pole_inverses {D : ℂ → S →L[ℂ] S} {p : ℂ}
    (hu : ∀ᶠ z in 𝓝[≠] p, IsUnit (D z)) :
    ∀ᶠ z in 𝓝[≠] p, D z * Ring.inverse (D z) = 1 ∧ Ring.inverse (D z) * D z = 1 := by
  filter_upwards [hu] with z hz
  exact ⟨Ring.mul_inverse_cancel _ hz, Ring.inverse_mul_cancel _ hz⟩

/-- The compressed current times the measured inverse residue equals the
charge times the pole projection in both orders, allowing degeneracy. Here
the norm limit is taken on the literal inverse of the Schur pencil. -/
theorem closing_schur_measured_charge {A : S →L[ℂ] S} {B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (q E₀ : ℝ) (Z : S →L[ℂ] S)
    (hb : IsUnit (closingShift B (-E₀ : ℝ)))
    (hu : ∀ᶠ z in 𝓝[≠] ((-E₀ : ℝ) : ℂ), IsUnit (closingPolePencil A B T z))
    (hZ : Tendsto (fun z : ℂ => (z - ((-E₀ : ℝ) : ℂ)) • Ring.inverse (closingPolePencil A B T z))
      (𝓝[≠] ((-E₀ : ℝ) : ℂ)) (𝓝 Z)) :
    let p : ℂ := (-E₀ : ℝ)
    let P := inversePoleKernelProjection (closingPolePencil A B T p)
    let R := closingResolvent B p
    let Γ := closingTemporalMark T q R R
    P * Z = Z ∧ Z * P = Z ∧ Z * (P * Γ * P) = (q : ℂ) • P ∧
      (P * Γ * P) * Z = (q : ℂ) • P := by
  let p : ℂ := (-E₀ : ℝ)
  let R := closingResolvent B p
  let P := inversePoleKernelProjection (closingPolePencil A B T p)
  have hD := closing_inverse_slot_hasDerivAt A T hb
  obtain ⟨h₁, h₂, h₃, h₄⟩ := inverse_pole_kernel_compression (D := closingPolePencil A B T) hD
    (closing_pencil_selfAdjoint hA hB T (-E₀)) (closing_pole_inverses hu) hZ
  have hΓ : closingTemporalMark T q R R = (q : ℂ) • closingTemporalMark T 1 R R := by
    simp [closingTemporalMark]
  refine ⟨h₁, h₂, ?_, ?_⟩
  · change Z * (P * closingTemporalMark T q R R * P) = (q : ℂ) • P
    rw [hΓ, mul_smul_comm, smul_mul_assoc, mul_smul_comm, h₃]
  · change P * closingTemporalMark T q R R * P * Z = (q : ℂ) • P
    rw [hΓ, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, h₄]

/-- With a one-dimensional nullspace the measured diagonal residue really
is the source's scalar norm expression, and its product with the temporal
charge insertion equals q. -/
theorem closing_schur_rank_one_residue {A : S →L[ℂ] S} {B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (q E₀ : ℝ) (Z : S →L[ℂ] S) (v : S) (hv : ‖v‖ = 1)
    (hk : LinearMap.ker (closingPolePencil A B T ((-E₀ : ℝ) : ℂ)).toLinearMap = ℂ ∙ v)
    (hb : IsUnit (closingShift B (-E₀ : ℝ)))
    (hu : ∀ᶠ z in 𝓝[≠] ((-E₀ : ℝ) : ℂ), IsUnit (closingPolePencil A B T z))
    (hZ : Tendsto (fun z : ℂ => (z - ((-E₀ : ℝ) : ℂ)) • Ring.inverse (closingPolePencil A B T z))
      (𝓝[≠] ((-E₀ : ℝ) : ℂ)) (𝓝 Z)) :
    let R := closingResolvent B ((-E₀ : ℝ) : ℂ)
    ⟪v, Z v⟫_ℂ = (closingSlotResidue T R v : ℂ) ∧
      ⟪v, Z v⟫_ℂ * ⟪v, closingTemporalMark T q R R v⟫_ℂ = (q : ℂ) := by
  let R := closingResolvent B ((-E₀ : ℝ) : ℂ)
  have hR := closing_real_resolvent_selfAdjoint B hB (-E₀)
  obtain ⟨_, he⟩ := inverse_pole_rank_one v hv hk (closing_inverse_slot_hasDerivAt A T hb)
    (closing_pencil_selfAdjoint hA hB T (-E₀)) (closing_pole_inverses hu) hZ
  change ⟪v, Z v⟫_ℂ = (⟪v, closingTemporalMark T 1 R R v⟫_ℂ)⁻¹ at he
  rw [closing_temporal_mark_quadratic T 1 R hR v hv, one_mul] at he
  have hz : ⟪v, Z v⟫_ℂ = (closingSlotResidue T R v : ℂ) := by
    simpa only [closingSlotResidue, Complex.ofReal_inv] using he
  exact ⟨hz, hz ▸ closing_residue_times_temporal_charge T q R hR v hv⟩

end UV.SectorPlane

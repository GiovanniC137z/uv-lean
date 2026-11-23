import UV.ContinueRealPoleChart
import UV.ContinuePoleResidueSchur

/-! Residues of the slot pencil with a possibly unbounded self-adjoint
boundary generator. A bounded two-sided resolvent at the real center
gives the local chart. Its values are the genuine boundary resolvents
throughout a neighborhood of the center. -/

noncomputable section
open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : H →ₗ.[ℂ] H} {p : ℝ}

def closingRealPolePencil (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (z : ℂ) : S →L[ℂ] S :=
  closingInverseSlot A T (closingRealPoleChart R₀ z) z

/-- The full complex neighborhood uses the true inverse on the domain of B,
including the nearby real frequencies. -/
theorem closing_real_pole_pencil_local_resolvent (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    ∀ᶠ z in 𝓝 (p:ℂ), ∃ R : ClosingUnboundedResolvent B z,
      closingRealPolePencil A T R₀ z = closingInverseSlot A T R.map z := by
  filter_upwards [closing_real_pole_factor_unit R₀] with z hu
  exact ⟨closingRealChartResolvent R₀ z hu,rfl⟩

theorem closing_real_pole_pencil_nonreal (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (hB : IsSelfAdjoint B) (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    ∀ᶠ z in 𝓝 (p:ℂ), ∀ hz : z.im≠0, closingRealPolePencil A T R₀ z =
      closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z := by
  filter_upwards [closing_real_pole_chart_nonreal hB R₀] with z hz
  intro h
  exact congrArg (fun R => closingInverseSlot A T R z) (hz h)

private theorem real_pencil_selfAdjoint {A : S →L[ℂ] S} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (T : S →L[ℂ] H) (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    IsSelfAdjoint (closingRealPolePencil A T R₀ (p:ℂ)) := by
  rw [closingRealPolePencil,closing_real_pole_chart_at]
  have h₁ : IsSelfAdjoint ((p:ℂ) • (1:S →L[ℂ] S)) := by simp [IsSelfAdjoint,star_smul]
  exact (h₁.add hA).sub ((closing_real_pole_map_selfAdjoint hB R₀).adjoint_conj T)

omit [CompleteSpace S] in
private theorem real_pencil_inverses {D : ℂ → S →L[ℂ] S}
    (hu : ∀ᶠ z in 𝓝[≠] (p:ℂ), IsUnit (D z)) :
    ∀ᶠ z in 𝓝[≠] (p:ℂ), D z * Ring.inverse (D z) = 1 ∧ Ring.inverse (D z) * D z = 1 := by
  filter_upwards [hu] with z h
  exact ⟨Ring.mul_inverse_cancel _ h,Ring.inverse_mul_cancel _ h⟩

/-- For a measured first-order pole at p=-E₀, the full residue is supported
on ker D(p). There it inverts the compressed derivative, so that the
compressed temporal current times the residue equals qP in both orders. -/
theorem closing_unbounded_pole_measured_charge {A : S →L[ℂ] S}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (q : ℝ) (Z : S →L[ℂ] S)
    (hu : ∀ᶠ z in 𝓝[≠] (p:ℂ), IsUnit (closingRealPolePencil A T R₀ z))
    (hZ : Tendsto (fun z : ℂ => (z-(p:ℂ)) • Ring.inverse (closingRealPolePencil A T R₀ z))
      (𝓝[≠] (p:ℂ)) (𝓝 Z)) :
    let P := inversePoleKernelProjection (closingRealPolePencil A T R₀ (p:ℂ))
    let Γ := closingTemporalMark T q R₀.map R₀.map
    P*Z=Z ∧ Z*P=Z ∧ Z*(P*Γ*P)=(q:ℂ) • P ∧ (P*Γ*P)*Z=(q:ℂ) • P := by
  let P := inversePoleKernelProjection (closingRealPolePencil A T R₀ (p:ℂ))
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inverse_pole_kernel_compression (D:=closingRealPolePencil A T R₀)
    (closing_real_pole_schur_hasDerivAt A T R₀) (real_pencil_selfAdjoint hA hB T R₀)
    (real_pencil_inverses hu) hZ
  have hΓ : closingTemporalMark T q R₀.map R₀.map = (q:ℂ) • closingTemporalMark T 1 R₀.map R₀.map := by
    simp [closingTemporalMark]
  refine ⟨h₁,h₂,?_,?_⟩
  · change Z*(P*closingTemporalMark T q R₀.map R₀.map*P)=(q:ℂ) • P
    rw [hΓ,mul_smul_comm,smul_mul_assoc,mul_smul_comm,h₃]
  · change P*closingTemporalMark T q R₀.map R₀.map*P*Z=(q:ℂ) • P
    rw [hΓ,mul_smul_comm,smul_mul_assoc,smul_mul_assoc,h₄]

/-- If a unit vector spans the pole kernel the measured diagonal is
(1+‖(B-E₀)⁻¹Tv‖²)⁻¹, including for unbounded B. -/
theorem closing_unbounded_pole_rank_one_residue {A : S →L[ℂ] S}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (q : ℝ) (Z : S →L[ℂ] S)
    (v : S) (hv : ‖v‖=1)
    (hk : LinearMap.ker (closingRealPolePencil A T R₀ (p:ℂ)).toLinearMap = ℂ ∙ v)
    (hu : ∀ᶠ z in 𝓝[≠] (p:ℂ), IsUnit (closingRealPolePencil A T R₀ z))
    (hZ : Tendsto (fun z : ℂ => (z-(p:ℂ)) • Ring.inverse (closingRealPolePencil A T R₀ z))
      (𝓝[≠] (p:ℂ)) (𝓝 Z)) :
    let r := closingSlotResidue T R₀.map v
    Z v = (r:ℂ) • v ∧ ⟪v,Z v⟫_ℂ = (r:ℂ) ∧
      ⟪v,Z v⟫_ℂ * ⟪v,closingTemporalMark T q R₀.map R₀.map v⟫_ℂ = (q:ℂ) := by
  obtain ⟨hm,he⟩ := inverse_pole_rank_one (D:=closingRealPolePencil A T R₀) v hv hk
    (closing_real_pole_schur_hasDerivAt A T R₀) (real_pencil_selfAdjoint hA hB T R₀)
    (real_pencil_inverses hu) hZ
  have hR := closing_real_pole_map_selfAdjoint hB R₀
  have hr : (⟪v,closingTemporalMark T 1 R₀.map R₀.map v⟫_ℂ)⁻¹ = (closingSlotResidue T R₀.map v:ℂ) := by
    rw [closing_temporal_mark_quadratic T 1 R₀.map hR v hv,one_mul]
    simp only [closingSlotResidue, Complex.ofReal_inv]
  rw [hr] at hm he
  exact ⟨hm,he,he ▸ closing_residue_times_temporal_charge T q R₀.map hR v hv⟩

end UV.SectorPlane

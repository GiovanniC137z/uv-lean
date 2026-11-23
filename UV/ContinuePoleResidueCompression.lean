import UV.ContinueClosingPositiveVertex
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The residue of a first-order inverse pole on a fixed carrier-frequency
chart. The kernel may have arbitrary dimension. -/

noncomputable section
open Filter Set
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- A two-sided local inverse with a first-order pole coefficient in norm.
Multiplying the inverse by the coordinate difference only requires a limit.
No differentiability of its regular part or simplicity of the determinant
zero is needed. -/
theorem inverse_pole_kernel_identities {D G : ℂ → A} {p : ℂ} {S R : A}
    (hD : HasDerivAt D S p)
    (hG : ∀ᶠ z in 𝓝[≠] p, D z * G z = 1 ∧ G z * D z = 1)
    (hR : Tendsto (fun z => (z-p) • G z) (𝓝[≠] p) (𝓝 R)) :
    D p * R = 0 ∧ R * D p = 0 ∧
    (∀ B : A, D p * B = 0 → R * S * B = B) ∧
    (∀ B : A, B * D p = 0 → B * S * R = B) := by
  have hK := hD.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {p}ᶜ))
  have hZ : Tendsto (fun z : ℂ => z-p) (𝓝[≠] p) (𝓝 0) := by
    simpa using ((tendsto_id (x := 𝓝 p)).sub_const p).mono_left
      (nhdsWithin_le_nhds (a := p) (s := {p}ᶜ))
  have h0 : Tendsto (fun z : ℂ => (z-p) • (1 : A)) (𝓝[≠] p) (𝓝 0) := by
    simpa using hZ.smul_const (1 : A)
  have hS := hasDerivAt_iff_tendsto_slope.mp hD
  refine ⟨tendsto_nhds_unique_of_eventuallyEq (hK.mul hR) h0 ?_,
    tendsto_nhds_unique_of_eventuallyEq (hR.mul hK) h0 ?_, ?_, ?_⟩
  · filter_upwards [hG] with z hz
    simp [hz.1]
  · filter_upwards [hG] with z hz
    simp [hz.2]
  · intro B hB
    apply tendsto_nhds_unique_of_eventuallyEq ((hR.mul hS).mul_const B) tendsto_const_nhds
    filter_upwards [hG, self_mem_nhdsWithin (s := {p}ᶜ)] with z hInv hz
    have hn : z-p ≠ 0 := sub_ne_zero.mpr hz
    simp only [slope, vsub_eq_sub]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [mul_assoc, sub_mul, hB, sub_zero, ←mul_assoc, hInv.2, one_mul]
  · intro B hB
    apply tendsto_nhds_unique_of_eventuallyEq
      (Filter.Tendsto.mul (hS.const_mul B) hR) tendsto_const_nhds
    filter_upwards [hG, self_mem_nhdsWithin (s := {p}ᶜ)] with z hInv hz
    have hn : z-p ≠ 0 := sub_ne_zero.mpr hz
    simp only [slope, vsub_eq_sub]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [mul_sub, hB, sub_zero, mul_assoc, hInv.1, mul_one]

end Algebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private instance poleKernelComplete (L : H →L[ℂ] H) : CompleteSpace (LinearMap.ker L.toLinearMap) :=
  (ContinuousLinearMap.isComplete_ker L).completeSpace_coe

/-- The orthogonal projection onto the kernel of the slot pencil at the pole. -/
def inversePoleKernelProjection (L : H →L[ℂ] H) : H →L[ℂ] H :=
  (LinearMap.ker L.toLinearMap).starProjection

theorem inverse_pole_projection_selfAdjoint (L : H →L[ℂ] H) :
    IsSelfAdjoint (inversePoleKernelProjection L) := isSelfAdjoint_starProjection _

theorem inverse_pole_projection_fixes {L : H →L[ℂ] H} {x : H} (hx : L x = 0) :
    inversePoleKernelProjection L x = x :=
  (LinearMap.ker L.toLinearMap).starProjection_eq_self_iff.mpr hx

/-- On a self-adjoint zero-frequency slot, the norm residue is supported
on the full orthogonal kernel projection. On that kernel it is the two-sided
inverse of the compressed derivative. -/
theorem inverse_pole_kernel_compression {D G : ℂ → H →L[ℂ] H} {p : ℂ}
    {S R : H →L[ℂ] H}
    (hD : HasDerivAt D S p) (ha : IsSelfAdjoint (D p))
    (hG : ∀ᶠ z in 𝓝[≠] p, D z * G z = 1 ∧ G z * D z = 1)
    (hR : Tendsto (fun z => (z-p) • G z) (𝓝[≠] p) (𝓝 R)) :
    let P := inversePoleKernelProjection (D p)
    P * R = R ∧ R * P = R ∧ R * (P * S * P) = P ∧ (P * S * P) * R = P := by
  obtain ⟨hDR,hRD,hRight,hLeft⟩ := inverse_pole_kernel_identities hD hG hR
  let K := LinearMap.ker (D p).toLinearMap
  letI : CompleteSpace K := poleKernelComplete _
  let P := K.starProjection
  have hPa : star P = P := (isSelfAdjoint_starProjection K).star_eq
  have hDP : D p * P = 0 := by
    ext1 x
    exact (K.orthogonalProjection x).property
  have hPD : P * D p = 0 := by
    simpa only [star_mul, hPa, ha.star_eq, star_zero] using congrArg star hDP
  have hsupport (C : H →L[ℂ] H) (h : D p * C = 0) : P * C = C := by
    ext1 x
    apply (K.starProjection_eq_self_iff).mpr
    exact DFunLike.congr_fun h x
  have hPR := hsupport R hDR
  have hRstar : D p * star R = 0 := by
    simpa only [star_mul, ha.star_eq, star_zero] using congrArg star hRD
  have hRP : R * P = R := by
    simpa only [star_mul, hPa, star_star] using congrArg star (hsupport (star R) hRstar)
  change P * R = R ∧ R * P = R ∧ R * (P * S * P) = P ∧ (P * S * P) * R = P
  refine ⟨hPR,hRP,?_,?_⟩
  · rw [←mul_assoc, ←mul_assoc, hRP, hRight _ hDP]
  · rw [mul_assoc (P*S), hPR, hLeft _ hPD]

/-- A unit vector spanning the pole kernel is an eigenvector of the measured
residue with eigenvalue reciprocal to its diagonal derivative. -/
theorem inverse_pole_rank_one {D G : ℂ → H →L[ℂ] H} {p : ℂ}
    {S R : H →L[ℂ] H} (v : H) (hv : ‖v‖ = 1)
    (hk : LinearMap.ker (D p).toLinearMap = ℂ ∙ v)
    (hD : HasDerivAt D S p) (ha : IsSelfAdjoint (D p))
    (hG : ∀ᶠ z in 𝓝[≠] p, D z * G z = 1 ∧ G z * D z = 1)
    (hR : Tendsto (fun z => (z-p) • G z) (𝓝[≠] p) (𝓝 R)) :
    R v = (⟪v, S v⟫_ℂ)⁻¹ • v ∧ ⟪v, R v⟫_ℂ = (⟪v, S v⟫_ℂ)⁻¹ := by
  obtain ⟨_, _, hInverse, _⟩ := inverse_pole_kernel_compression hD ha hG hR
  let P := (LinearMap.ker (D p).toLinearMap).starProjection
  have hproj (x : H) : P x = ⟪v, x⟫_ℂ • v := by
    simp [P, hk, Submodule.starProjection_singleton, hv]
  have hn : ⟪v, v⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hv]
  have hvP : P v = v := by rw [hproj, hn, one_smul]
  have hx := DFunLike.congr_fun hInverse v
  change R (P (S (P v))) = P v at hx
  rw [hvP, hproj, map_smul] at hx
  have hnon : ⟪v, S v⟫_ℂ ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hx
    simp [← hx] at hv
  have he : R v = (⟪v, S v⟫_ℂ)⁻¹ • v := by
    simpa only [smul_smul, inv_mul_cancel₀ hnon, one_smul] using
      congrArg (fun x : H => (⟪v, S v⟫_ℂ)⁻¹ • x) hx
  exact ⟨he, by rw [he, inner_smul_right, hn, mul_one]⟩

end UV.SectorPlane

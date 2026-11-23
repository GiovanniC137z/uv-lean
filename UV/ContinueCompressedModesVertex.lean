import UV.ContinueNormalLegTransfer

/-! The longitudinally conjugated three-compression vertex on one fixed
normal mode. Its exact Ward contraction coexists with two different
soft limits in unit-normalized transfer directions. -/

noncomputable section

open Filter Set UV.SectorPlane
open scoped RealInnerProductSpace Matrix.Norms.L2Operator Topology

namespace UV

variable {ι : Type*} [Fintype ι]

def compressedTransferUnit (Q : OSFourSpace) (hQ : Q ≠ 0) : UnitVector OSFourSpace :=
  ⟨‖Q‖⁻¹ • Q,by simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hQ]⟩

def compressedLongitudinal (Q x : OSFourSpace) := (⟪Q,x⟫/‖Q‖^2) • Q

theorem compressed_longitudinal_unit (Q : OSFourSpace) (hQ : Q ≠ 0) (x : OSFourSpace) :
    compressedLongitudinal Q x = ⟪(compressedTransferUnit Q hQ).val,x⟫ • (compressedTransferUnit Q hQ).val := by
  simp only [compressedTransferUnit,compressedLongitudinal,real_inner_smul_left,smul_smul]
  congr 1
  rw [div_eq_mul_inv,←inv_pow]; ring

theorem compressed_longitudinal_ray (v : UnitVector OSFourSpace) (x : OSFourSpace) {r : ℝ} (hr : r ≠ 0) :
    compressedLongitudinal (r • v.val) x = ⟪v.val,x⟫ • v.val := by
  simp only [compressedLongitudinal,real_inner_smul_left,norm_smul,Real.norm_eq_abs,v.property,mul_one,sq_abs,smul_smul]
  congr 1
  field_simp

def compressedVertexFactor (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p Q : OSFourSpace) : ℝ :=
  normalLegForm L T ξ (p+Q)*normalLegForm L T ξ p*normalLegForm L T 0 Q

/-- Evaluation of the displayed one-photon tensor on a polarization x.
Only its transverse component receives the charged and photon profiles. -/
def compressedPhotonVertex (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p Q x : OSFourSpace) : DiracMatrix :=
  Complex.I • diracSlash (compressedVertexFactor L T ξ p Q • (x-compressedLongitudinal Q x) + compressedLongitudinal Q x)

theorem compressed_vertex_ward (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p Q : OSFourSpace) (hQ : Q ≠ 0) :
    compressedPhotonVertex L T ξ p Q Q = Complex.I • diracSlash Q ∧
      compressedPhotonVertex L T ξ p Q Q = normalDiracSymbol m (p+Q) ξ-normalDiracSymbol m p ξ := by
  have he : compressedLongitudinal Q Q = Q := by
    simp [compressedLongitudinal,real_inner_self_eq_norm_sq,hQ]
  rw [compressedPhotonVertex,he,sub_self,smul_zero,zero_add]
  refine ⟨rfl,?_⟩
  simp only [normalDiracSymbol,normalFiveSlash,diracSlash_add,smul_add]
  abel

theorem compressed_vertex_factor_limit (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : OSFourSpace) :
    Tendsto (compressedVertexFactor L T ξ p) (𝓝 0) (𝓝 (normalLegForm L T ξ p^2)) := by
  have hc : Continuous (compressedVertexFactor L T ξ p) :=
    (((normal_leg_form_continuous L T ξ).comp (continuous_const.add continuous_id)).mul continuous_const).mul (normal_leg_form_continuous L T 0)
  simpa only [compressedVertexFactor,add_zero,normal_leg_form_origin,mul_one,pow_two] using hc.tendsto 0

theorem compressed_vertex_parallel (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (v : UnitVector OSFourSpace) {r : ℝ} (hr : r ≠ 0) :
    compressedPhotonVertex L T ξ p (r • v.val) v.val = Complex.I • diracSlash v.val := by
  simp [compressedPhotonVertex,compressed_longitudinal_ray v v.val hr,real_inner_self_eq_norm_sq,v.property]

theorem compressed_vertex_orthogonal (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (v u : UnitVector OSFourSpace) (hvu : ⟪v.val,u.val⟫ = 0) {r : ℝ} (hr : r ≠ 0) :
    compressedPhotonVertex L T ξ p (r • v.val) u.val =
      (compressedVertexFactor L T ξ p (r • v.val) : ℂ) • (Complex.I • diracSlash u.val) := by
  simp only [compressedPhotonVertex,compressed_longitudinal_ray v u.val hr,hvu,zero_smul,sub_zero,add_zero,diracSlash_real_smul]
  rw [smul_comm]

theorem compressed_vertex_directional_limits (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (u v : UnitVector OSFourSpace) (hvu : ⟪v.val,u.val⟫ = 0) :
    Tendsto (fun r : ℝ => compressedPhotonVertex L T ξ p (r • u.val) u.val) (𝓝[≠] 0) (𝓝 (Complex.I • diracSlash u.val)) ∧
    Tendsto (fun r : ℝ => compressedPhotonVertex L T ξ p (r • v.val) u.val) (𝓝[≠] 0)
      (𝓝 (((normalLegForm L T ξ p)^2:ℝ) • (Complex.I • diracSlash u.val))) := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (compressed_vertex_parallel L T ξ p u hr).symm
  · have hv : Tendsto (fun r : ℝ => r • v.val) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [id_eq,zero_smul] using ((continuous_id.smul continuous_const : Continuous (fun r : ℝ => r • v.val)).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := ({0}:Set ℝ)ᶜ))
    have hh := ((compressed_vertex_factor_limit L T ξ p).comp hv).smul_const (Complex.I • diracSlash u.val)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [compressed_vertex_orthogonal L T ξ p v u hvu hr]
    ext a b
    exact Complex.real_smul

theorem compressed_vertex_unequal_limits (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (u : UnitVector OSFourSpace) (hf : normalLegForm L T ξ p^2 ≠ 1) :
    ((normalLegForm L T ξ p)^2:ℝ) • (Complex.I • diracSlash u.val) ≠ Complex.I • diracSlash u.val := by
  intro he
  have nh := congrArg norm he
  simp only [norm_smul,Complex.norm_I,wilson_slash_opnorm,u.property,mul_one,Real.norm_of_nonneg (sq_nonneg _)] at nh
  exact hf nh

theorem compressed_unit_ray_punctured (u : UnitVector OSFourSpace) :
    Tendsto (fun r : ℝ => r • u.val) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [id_eq,zero_smul] using
      ((continuous_id.smul continuous_const : Continuous (fun r : ℝ => r • u.val)).tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := ({0}:Set ℝ)ᶜ))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply smul_ne_zero hr
    intro he
    have h := u.property
    simp [he] at h

theorem compressed_vertex_no_soft_limit (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : OSFourSpace) (u v : UnitVector OSFourSpace) (hvu : ⟪v.val,u.val⟫ = 0)
    (hf : normalLegForm L T ξ p^2 ≠ 1) :
    ¬ ∃ G, Tendsto (fun Q => compressedPhotonVertex L T ξ p Q u.val) (𝓝[≠] 0) (𝓝 G) := by
  rintro ⟨G,hG⟩
  obtain ⟨hp,ht⟩ := compressed_vertex_directional_limits L T ξ p u v hvu
  apply compressed_vertex_unequal_limits L T ξ p u hf
  exact (tendsto_nhds_unique ht (hG.comp (compressed_unit_ray_punctured v))).trans
    (tendsto_nhds_unique (hG.comp (compressed_unit_ray_punctured u)) hp)

theorem compressed_vertex_soft_obstruction_at_large_carriers {L : ℝ} (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ξ : ℝ) (p : OSFourSpace), R ≤ ‖p‖ →
      ¬ ∃ G, Tendsto (fun Q => compressedPhotonVertex L T ξ p Q (osAxis 0).val) (𝓝[≠] 0) (𝓝 G) := by
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  obtain ⟨B,hB,hh⟩ := normal_shell_characteristic_decay ι (by omega)
  refine ⟨(B+1)/L,by positivity,fun ξ p hp => ?_⟩
  apply compressed_vertex_no_soft_limit L T ξ p (osAxis 0) (osAxis 1)
  · simp [osAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]
  · let P := normalBallJoin ξ p
    have hle : ‖p‖ ≤ ‖P‖ := by
      dsimp [P]
      nlinarith [normal_ball_join_norm ξ p,norm_nonneg p,norm_nonneg (normalBallJoin ξ p),sq_nonneg ξ]
    have hv : B+1 ≤ L*‖P‖ := by simpa only [mul_comm] using (div_le_iff₀ hL).mp (hp.trans hle)
    have hc := hh (L • T P)
    rw [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le] at hc
    have hl : |normalLegForm L T ξ p| < 1 := (Complex.abs_re_le_norm _).trans_lt
      (hc.trans_lt ((div_lt_one (by positivity)).mpr (by nlinarith [sq_nonneg (L*‖P‖)])))
    have hs := mul_self_lt_mul_self (abs_nonneg _) hl
    rw [←sq, sq_abs] at hs
    linarith

end UV

import UV.ContinueWilsonAmplitudeRotation

/-! Direction-independent transverse scalar of the summed closed Wilson
two-point graph. The transverse unit polarization can vary with the
nonzero momentum, even discontinuously. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

variable {m : ℕ} {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]

/-- The same transverse scalar is obtained in all directions on the
four-dimensional Euclidean plane. Its numerator vanishes at the origin
in the sense of the full punctured four-vector limit. The reference pair
gives a definite expression for the common coefficient. -/
theorem wilson_incidence_transverse_limit (src dst : E → Option (Fin m))
    (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row) {L lam : ℝ}
    (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (Gdel : B.tree → SimpleGraph (Option (Fin m))) (hc : ∀ j, (Gdel j).Connected)
    (hcover : ∀ j : B.tree, NetworkOrientationCovers (Gdel j) (fun e : {e : E // e ≠ j.val} => src e) (fun e => dst e))
    (s t : Option (Fin m)) (u v : UnitVector OSFourSpace) (huv : ⟪u.val,v.val⟫ = 0)
    (e : OSFourSpace → UnitVector OSFourSpace) (he : ∀ k ≠ 0, ⟪k,(e k).val⟫ = 0) :
    let G := wilsonGraphOfIncidence src dst B s t
    let b := fun x j => B.offset (fun i => wilsonExternalPair s t x (some i)) j
    let F := fun k => G.summedAmplitude L lam T b B.coefficient k (e k) (e k)
    Tendsto (fun k : OSFourSpace => F k/(‖k‖^2 : ℝ)) (𝓝[≠] 0)
      (𝓝 (G.summedCoefficient L lam T b B.coefficient u v v)) ∧ Tendsto F (𝓝[≠] 0) (𝓝 0) := by
  dsimp only
  let G := wilsonGraphOfIncidence src dst B s t
  let b := fun x j => B.offset (fun i => wilsonExternalPair s t x (some i)) j
  let F := G.summedAmplitude L lam T b B.coefficient
  have hdir := wilson_incidence_summed_quotient src dst B hL hlam hl T Gdel hc hcover s t u v v
  have hrot (k : OSFourSpace) (hk : k ≠ 0) : F (‖k‖ • u.val) v v = F k (e k) (e k) := by
    let p : UnitVector OSFourSpace := ⟨‖k‖⁻¹ • k,by simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hk]⟩
    have hp : ⟪p.val,(e k).val⟫ = 0 := by
      change ⟪‖k‖⁻¹ • k,(e k).val⟫ = 0
      rw [real_inner_smul_left,he k hk,mul_zero]
    obtain ⟨R,h₁,h₂⟩ := wilson_orthogonal_unit_pair u v p (e k) huv hp
    have hk' : R (‖k‖ • u.val) = k := by
      rw [map_smul,show R u.val=p.val from congrArg Subtype.val h₁]
      change ‖k‖ • ‖k‖⁻¹ • k = k
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hk),one_smul]
    have hr := G.summedAmplitude_rotate hL lam T R b (B.offset_pair_rotate src dst s t R) B.coefficient (‖k‖ • u.val) v v
    simpa only [hk',h₂] using hr.symm
  have hn : Tendsto (fun k : OSFourSpace => ‖k‖) (𝓝[≠] 0) (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using (continuous_norm.continuousAt (x := (0:OSFourSpace))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with k hk
      exact norm_ne_zero_iff.mpr hk
  constructor
  · apply (hdir.1.comp hn).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    change F (‖k‖ • u.val) v v / _ = F k (e k) (e k) / _
    rw [hrot k hk,norm_smul,u.property,mul_one,Real.norm_of_nonneg (norm_nonneg _)]
  · apply (hdir.2.comp hn).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact hrot k hk

end UV

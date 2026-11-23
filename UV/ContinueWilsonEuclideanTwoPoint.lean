import UV.ContinueWilsonSummedTwoPoint

/-! The undisivided two-current amplitude and its squared-momentum
quotient on an actual contracted incidence graph. Both external
directions and polarizations are unit vectors. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Topology BigOperators

namespace UV

variable {V C D ι : Type*} [Fintype V] [Fintype C] [Fintype D] [Fintype ι]

def WilsonClosedPolygon.externalMark (P : WilsonClosedPolygon) (χ : OSFourSpace → ℂ)
    (k : OSFourSpace) (v : UnitVector OSFourSpace) : ℂ := χ k * P.polarized v k

theorem WilsonClosedPolygon.external_radial (P : WilsonClosedPolygon) (χ : OSFourSpace → ℂ)
    (u v : UnitVector OSFourSpace) {r : ℝ} (hr : r ≠ 0) :
    P.externalMark χ (r • u.val) v = (r : ℂ) * P.softMark χ u v r := by
  unfold externalMark softMark
  field_simp [Complex.ofReal_ne_zero.mpr hr]

def WilsonCurrentGraph.amplitude (G : WilsonCurrentGraph V C D) (χ : OSFourSpace → ℂ) (P : V → WilsonClosedPolygon)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (k : OSFourSpace) (v w : UnitVector OSFourSpace) : ℂ :=
  ∫ q, (P G.first).externalMark χ k v * (P G.second).externalMark χ (-k) w * G.kernel χ P b a k q
    ∂Measure.pi (fun _ : C => volume)

omit [Fintype V] in
theorem WilsonCurrentGraph.amplitude_factor (G : WilsonCurrentGraph V C D) (χ : OSFourSpace → ℂ) (P : V → WilsonClosedPolygon)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) {r : ℝ} (hr : r ≠ 0) :
    G.amplitude χ P b a (r • u.val) v w = (r:ℂ)^2 * G.twoPoint χ P b a u v w r := by
  have he : -(r • u.val) = r • (wilsonOppositeDirection u).val := (smul_neg r u.val).symm
  rw [amplitude,twoPoint,←integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  dsimp only
  rw [he,(P G.first).external_radial χ u v hr,(P G.second).external_radial χ (wilsonOppositeDirection u) w hr]
  ring

def WilsonCurrentGraph.summedAmplitude (G : WilsonCurrentGraph V C D) (L lam : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (k : OSFourSpace) (v w : UnitVector OSFourSpace) : ℂ :=
  ∑' n : V → ℕ, (wilsonDetWeight lam n : ℂ) *
    ∫ d, wilsonGraphReturnWeight L T d * G.amplitude (wilsonShellPhotonForm L T) (fun j => wilsonReturnPolygon (d j)) b a k v w
      ∂wilsonGraphReturnMeasure L T n

theorem WilsonCurrentGraph.summedAmplitude_factor (G : WilsonCurrentGraph V C D) (L lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ)
    (u v w : UnitVector OSFourSpace) {r : ℝ} (hr : r ≠ 0) :
    G.summedAmplitude L lam T b a (r • u.val) v w = (r:ℂ)^2 * G.summedRadial L lam T b a u v w r := by
  unfold summedAmplitude summedRadial
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [G.amplitude_factor _ _ b a u v w hr,mul_left_comm (wilsonGraphReturnWeight L T _)
    ((r:ℂ)^2),integral_const_mul]
  ring

def wilsonGraphOfIncidence {E : Type*} {n : ℕ} (src dst : E → Option (Fin n))
    (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row) (s t : Option (Fin n)) :
    WilsonCurrentGraph (Option (Fin n)) B.Chord B.tree :=
  ⟨s,t,fun c => (src c,dst c),fun j => (src j,dst j)⟩

/-- Every tree deletion leaves a connected graph witnessed by the
surviving labelled edges. Under that cycle condition the true amplitude,
integrated over the closed Wilson polygons and summed with their cyclic
determinant weights, admits the stated limit in each unit direction. -/
theorem wilson_incidence_summed_quotient {m : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (src dst : E → Option (Fin m)) (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)
    {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (Gdel : B.tree → SimpleGraph (Option (Fin m))) (hc : ∀ j, (Gdel j).Connected)
    (hcover : ∀ j : B.tree, NetworkOrientationCovers (Gdel j) (fun e : {e : E // e ≠ j.val} => src e) (fun e => dst e))
    (s t : Option (Fin m)) (u v w : UnitVector OSFourSpace) :
    let G := wilsonGraphOfIncidence src dst B s t
    let b := fun x j => B.offset (fun i => wilsonExternalPair s t x (some i)) j
    let F := fun k => G.summedAmplitude L lam T b B.coefficient k v w
    Tendsto (fun r : ℝ => F (r • u.val)/(‖r • u.val‖^2 : ℝ)) (𝓝[≠] 0)
      (𝓝 (G.summedCoefficient L lam T b B.coefficient u v w)) ∧
      Tendsto (fun r : ℝ => F (r • u.val)) (𝓝[≠] 0) (𝓝 0) := by
  dsimp only
  let G := wilsonGraphOfIncidence src dst B s t
  let b := fun x j => B.offset (fun i => wilsonExternalPair s t x (some i)) j
  have H := G.summed_twoPoint_limit hL hlam hl T b (fun j => (B.offset_pair_continuous src dst s t j).continuousAt)
    B.coefficient (fun j => B.active_of_deletion j (wilson_incidence_nonbridge src dst j (Gdel j) (hc j) (hcover j))) u v w
  have he : ∀ᶠ (r : ℝ) in 𝓝[≠] (0:ℝ), G.summedAmplitude L lam T b B.coefficient (r • u.val) v w =
      (r:ℂ)^2 * G.summedRadial L lam T b B.coefficient u v w r :=
    by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact G.summedAmplitude_factor _ _ _ _ _ _ _ _ hr
  constructor
  · apply H.congr'
    filter_upwards [he,self_mem_nhdsWithin] with r hr h0
    change _ = G.summedAmplitude L lam T b B.coefficient (r • u.val) v w / _
    rw [hr,norm_smul,u.property,mul_one,Real.norm_eq_abs,sq_abs,Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr (show r ≠ 0 from h0)]
  · have hz : Tendsto (fun r : ℝ => (r:ℂ)^2) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((Complex.continuous_ofReal.pow 2).continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using (hz.mul H).congr' (Filter.EventuallyEq.symm he)

end UV

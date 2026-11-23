import UV.ContinueWilsonIncidenceRouting
import UV.ContinueWilsonRoutedSoftLimit

/-! Two external marks inject opposite four-momenta. The rooted incidence
solution balances these injections at every vertex, including the root.
Connectivity after deleting an internal tree edge supplies precisely
the nonzero chord coefficient needed for the fixed-polygon soft limit. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane
open scoped Topology

namespace UV

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def wilsonVertexSign (s t v : Option (Fin n)) : ℝ :=
  (if t = v then 1 else 0) - (if s = v then 1 else 0)

theorem wilson_vertex_sign_sum (s t : Option (Fin n)) : ∑ v, wilsonVertexSign s t v = 0 := by
  classical
  simp [wilsonVertexSign,Finset.sum_sub_distrib]

def wilsonExternalPair (s t : Option (Fin n)) (x : OSFourSpace) (v : Option (Fin n)) : OSFourSpace :=
  wilsonVertexSign s t v • x

theorem wilson_external_pair_sum (s t : Option (Fin n)) (x : OSFourSpace) : ∑ v, wilsonExternalPair s t x v = 0 := by
  simp only [wilsonExternalPair,←Finset.sum_smul,wilson_vertex_sign_sum,zero_smul]

variable (src dst : E → Option (Fin n)) (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)

/-- The solved flow satisfies all vertex equations as four-vector equations. -/
theorem WilsonIncidenceBasis.full_balance (s t : Option (Fin n)) (x : OSFourSpace) (q : B.Chord → OSFourSpace)
    (v : Option (Fin n)) :
    ∑ e, wilsonVertexSign (src e) (dst e) v • B.flow (fun i => wilsonExternalPair s t x (some i)) q e =
      wilsonExternalPair s t x v := by
  classical
  let F := B.flow (fun i => wilsonExternalPair s t x (some i)) q
  let S := fun v => ∑ e, wilsonVertexSign (src e) (dst e) v • F e
  have hs (i : Fin n) : S (some i) = wilsonExternalPair s t x (some i) := by
    ext k
    have hb := congrFun (B.balance (fun i => wilsonExternalPair s t x (some i)) q k) i
    change (EuclideanSpace.proj k : OSFourSpace →L[ℝ] ℝ) (∑ e, wilsonVertexSign (src e) (dst e) (some i) • F e) = _
    rw [map_sum]
    simpa only [map_smul,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
      Matrix.row,groundedNetworkIncidence,wilsonVertexSign,F,mul_comm] using hb
  cases v with
  | some i => exact hs i
  | none =>
    have he : ∑ v, S v = 0 := by
      dsimp only [S]
      rw [Finset.sum_comm]
      simp only [←Finset.sum_smul,wilson_vertex_sign_sum,zero_smul,Finset.sum_const_zero]
    have hex := wilson_external_pair_sum s t x
    rw [Fintype.sum_option] at he hex
    simp_rw [hs] at he
    exact add_right_cancel (he.trans hex.symm)

omit [Fintype E] [DecidableEq E] in
theorem WilsonIncidenceBasis.offset_pair_continuous (s t : Option (Fin n)) (j : B.tree) :
    Continuous (fun x => B.offset (fun v => wilsonExternalPair s t x (some v)) j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
  apply continuous_pi fun k => ?_
  apply (B.basis.coord j).continuous_of_finiteDimensional.comp
  apply continuous_pi fun v => ?_
  exact (EuclideanSpace.proj k : OSFourSpace →L[ℝ] ℝ).continuous.comp
    (continuous_const (y := wilsonVertexSign s t (some v)) |>.smul (continuous_id (X := OSFourSpace)))

def wilsonContractedEdge (P : Option (Fin n) → WilsonClosedPolygon) (e : E) : WilsonPolygonEdge :=
  ⟨P (src e), P (dst e)⟩

/-- The routed two-point limit, with opposite external transfers and no
internal soft cutoff, for the specified closed polygons on the vertices.
The deletion condition refers to the actual surviving labelled edges. -/
theorem wilson_graph_polygon_two_point {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (Gdel : B.tree → SimpleGraph (Option (Fin n))) (hc : ∀ j, (Gdel j).Connected)
    (hcover : ∀ j : B.tree, NetworkOrientationCovers (Gdel j)
      (fun e : {e : E // e ≠ j.val} => src e) (fun e => dst e))
    (P : Option (Fin n) → WilsonClosedPolygon) (s t : Option (Fin n)) (u v w : UnitVector OSFourSpace) :
    let χ := wilsonShellPhotonForm L T
    let edge := wilsonContractedEdge src dst P
    let F := fun x q => wilsonRoutedPhotonProduct χ (fun c : B.Chord => edge c) (fun j : B.tree => edge j)
      (B.onTree (fun i => wilsonExternalPair s t x (some i))) q
    Tendsto (fun r : ℝ => ∫ q, (P s).softMark χ u v r * (P t).softMark χ (wilsonOppositeDirection u) w r *
      F (r • u.val) q ∂Measure.pi (fun _ : B.Chord => volume)) (𝓝[≠] 0)
      (𝓝 (∫ q, (P s).softCoefficient u v * (P t).softCoefficient (wilsonOppositeDirection u) w * F 0 q
        ∂Measure.pi (fun _ : B.Chord => volume))) := by
  exact wilson_fixed_polygon_two_point_limit hL T _ _
    (fun x j => B.offset (fun i => wilsonExternalPair s t x (some i)) j)
    (fun j => (B.offset_pair_continuous src dst s t j).continuousAt) B.coefficient
    (fun j => B.active_of_deletion j (wilson_incidence_nonbridge src dst j (Gdel j) (hc j) (hcover j)))
    (P s) (P t) u v w

end UV

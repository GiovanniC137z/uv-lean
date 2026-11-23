import UV.ContinueWilsonCurrentRotation

/-! Covariance of the entire summed Euclidean two-current amplitude
under a common orthogonal change of carrier variables. The actual
incidence offsets transform with the signed external pair. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V C D ι : Type*} [Fintype V] [Fintype C] [Fintype D] [Fintype ι]

omit [Fintype V] in
theorem WilsonCurrentGraph.amplitude_rotate (G : WilsonCurrentGraph V C D) {L : ℝ}
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace)
    (P : V → WilsonClosedPolygon) (b : OSFourSpace → D → OSFourSpace)
    (hb : ∀ k j, b (R k) j = R (b k j)) (a : D → C → ℝ) (k : OSFourSpace) (v w : UnitVector OSFourSpace) :
    let χ := wilsonShellPhotonForm L T
    G.amplitude χ (fun j => (P j).rotate R) b a (R k) (wilsonRotateUnit R v) (wilsonRotateUnit R w) =
      G.amplitude χ P b a k v w := by
  dsimp only
  let χ := wilsonShellPhotonForm L T
  have hχ (p) : χ (R p) = χ p := wilson_shell_radial L T (R.norm_map p)
  let ν := Measure.pi (fun _ : C => (volume : Measure OSFourSpace))
  let H : (C → OSFourSpace) ≃ᵐ (C → OSFourSpace) := MeasurableEquiv.piCongrRight (fun _ => R.toMeasurableEquiv)
  have hH : MeasurePreserving H ν ν := measurePreserving_pi _ _ (fun _ => R.measurePreserving)
  let F := fun (P' : V → WilsonClosedPolygon) (k' : OSFourSpace) (v' w' : UnitVector OSFourSpace) (q : C → OSFourSpace) =>
    (P' G.first).externalMark χ k' v' * (P' G.second).externalMark χ (-k') w' * G.kernel χ P' b a k' q
  change (∫ q, F (fun j => (P j).rotate R) (R k) _ _ q ∂ν) = _
  rw [←hH.integral_comp H.measurableEmbedding (F (fun j => (P j).rotate R) (R k) (wilsonRotateUnit R v) (wilsonRotateUnit R w))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall fun q => ?_
  have ht (e : D) : wilsonAffineTransfer (b (R k) e) (a e) (H q) = R (wilsonAffineTransfer (b k e) (a e) q) := by
    simp only [hb,wilsonAffineTransfer,wilson_route_linear_apply,map_add,_root_.map_sum,map_smul]
    rfl
  change F (fun j => (P j).rotate R) (R k) _ _ (H q) = F P k v w q
  simp only [F,WilsonClosedPolygon.externalMark,←map_neg,
    WilsonClosedPolygon.polarized_rotate,hχ,kernel,wilsonRoutedPhotonProduct,edge,ht]
  change _ * ((∏ i, (WilsonPolygonEdge.mk ((P (G.chord i).1).rotate R) ((P (G.chord i).2).rotate R)).sewing χ (R (q i))) * _) = _
  simp only [wilson_rotate_sewing _ _ R hχ]

theorem WilsonCurrentGraph.summedAmplitude_rotate (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L) (lam : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ k j, b (R k) j = R (b k j))
    (a : D → C → ℝ) (k : OSFourSpace) (v w : UnitVector OSFourSpace) :
    G.summedAmplitude L lam T b a (R k) (wilsonRotateUnit R v) (wilsonRotateUnit R w) =
      G.summedAmplitude L lam T b a k v w := by
  unfold summedAmplitude
  apply tsum_congr
  intro n
  congr 1
  let μ := wilsonDisplacementMeasure L T
  let H : (WilsonGraphDisplacements n) ≃ᵐ (WilsonGraphDisplacements n) := MeasurableEquiv.piCongrRight
    (fun _ => MeasurableEquiv.piCongrRight (fun _ => R.toMeasurableEquiv))
  have hH : MeasurePreserving H (wilsonGraphReturnMeasure L T n) (wilsonGraphReturnMeasure L T n) :=
    measurePreserving_pi _ _ (fun j => measurePreserving_pi (fun _ : Fin (n j) => μ) _ (fun _ => wilson_displacement_orthogonal L T R))
  let F := fun (k' : OSFourSpace) (v' w' : UnitVector OSFourSpace) (d : WilsonGraphDisplacements n) =>
    wilsonGraphReturnWeight L T d * G.amplitude (wilsonShellPhotonForm L T) (fun j => wilsonReturnPolygon (d j)) b a k' v' w'
  change (∫ d, F (R k) _ _ d ∂_) = _
  rw [←hH.integral_comp H.measurableEmbedding (F (R k) (wilsonRotateUnit R v) (wilsonRotateUnit R w))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall fun d => ?_
  change (∏ j, wilsonReturnWeight L T (fun i => R (d j i))) * G.amplitude (wilsonShellPhotonForm L T)
      (fun j => wilsonReturnPolygon (fun i => R (d j i))) b a (R k) _ _ = F k v w d
  simp only [wilson_return_weight_rotate hL T,wilson_return_polygon_rotate,G.amplitude_rotate T R _ b hb,F,wilsonGraphReturnWeight]

variable {m : ℕ} {E : Type*} (src dst : E → Option (Fin m))
    (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)

theorem WilsonIncidenceBasis.offset_pair_scalar (s t : Option (Fin m)) (x : OSFourSpace) (j : B.tree) :
    B.offset (fun i => wilsonExternalPair s t x (some i)) j =
      (B.basis.coord j (fun i => wilsonVertexSign s t (some i))) • x := by
  ext k
  have he : (fun i => wilsonExternalPair s t x (some i) k) = (x k) • (fun i => wilsonVertexSign s t (some i)) := by
    funext i
    simp [wilsonExternalPair,mul_comm]
  change B.basis.coord j (fun i => wilsonExternalPair s t x (some i) k) = _
  rw [he,map_smul]
  exact mul_comm _ _

theorem WilsonIncidenceBasis.offset_pair_rotate (s t : Option (Fin m)) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace)
    (x : OSFourSpace) (j : B.tree) :
    B.offset (fun i => wilsonExternalPair s t (R x) (some i)) j =
      R (B.offset (fun i => wilsonExternalPair s t x (some i)) j) := by
  simp only [B.offset_pair_scalar src dst,map_smul]

end UV

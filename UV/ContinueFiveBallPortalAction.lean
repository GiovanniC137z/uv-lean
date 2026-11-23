import UV.ContinueFiveBallPortalHeat

/-! The literal transverse Duhamel coefficient of the squared minimally
gauged Dirac symbol. Its two first variations and the direct variation
are acted on by the same Gaussian and the same external mediator. -/

noncomputable section

open MeasureTheory Set UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV

/-- Squaring a Dirac symbol with an affine connection gives the two
placements of a first variation between momentum k and momentum k'. -/
def portalLinearVertex (k k' : ScalarMomentum) (u : UnitVector ScalarMomentum) :=
  diracSlash k'*diracSlash u.val+diracSlash u.val*diracSlash k

/-- The two orders of the identical transverse insertions in the
quadratic (direct) vertex. -/
def portalDirectVertex (u : UnitVector ScalarMomentum) :=
  (2:ℂ) • (diracSlash u.val*diracSlash u.val)

theorem portal_dirac_vertices (k Q : ScalarMomentum) (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    ((portalLinearVertex (k+Q) k u * portalLinearVertex k (k+Q) u).trace).re =
      4*((2*⟪u.val,k⟫)^2+‖Q‖^2) ∧ (portalDirectVertex u).trace.re = 8 := by
  let U := diracSlash u.val
  let V := diracSlash Q
  let W := diracSlash k
  let c := ((2*⟪u.val,k⟫:ℝ):ℂ)
  have hu : U*U=1 := by simpa only [U,u.property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq u.val
  have hk : U*W+W*U = c • 1 := wilson_slash_anticommutator _ _
  have hr := wilson_slash_anticommutator u.val Q
  rw [hQ,mul_zero,Complex.ofReal_zero,zero_smul] at hr
  have hV : U*V = -(V*U) := eq_neg_of_add_eq_zero_left hr
  have hplus : portalLinearVertex k (k+Q) u = c • 1+V*U := by
    rw [portalLinearVertex,diracSlash_add,add_mul,←hk]
    dsimp only [U,V,W]
    abel
  have hminus : portalLinearVertex (k+Q) k u = c • 1-V*U := by
    rw [portalLinearVertex,diracSlash_add,mul_add,←hk,←neg_eq_iff_eq_neg.mpr hV]
    dsimp only [U,V,W]
    abel
  have hs : (V*U)*(V*U) = -((‖Q‖^2:ℝ):ℂ) • (1:DiracMatrix) := by
    calc _ = (V*(U*V))*U := by noncomm_ring
         _ = -((V*V)*(U*U)) := by rw [hV]; noncomm_ring
         _ = _ := by rw [hu,mul_one,diracSlash_sq]; simp
  have hm : portalLinearVertex (k+Q) k u * portalLinearVertex k (k+Q) u =
      (c^2+((‖Q‖^2:ℝ):ℂ)) • (1:DiracMatrix) := by
    rw [hplus,hminus,sub_mul,mul_add,mul_add,smul_mul_smul,one_mul,smul_mul_assoc,one_mul,mul_smul_comm,mul_one,hs]
    simp only [neg_smul,add_smul,pow_two]
    abel
  constructor
  · rw [hm,Matrix.trace_smul,Matrix.trace_one]
    change (((Complex.ofReal (2*⟪u.val,k⟫))^2 + Complex.ofReal (‖Q‖^2)) * Complex.ofReal 4).re = _
    rw [←Complex.ofReal_pow,←Complex.ofReal_add,←Complex.ofReal_mul,Complex.ofReal_re,mul_comm]
  · change (((2:ℂ) • (U*U)).trace).re = 8
    rw [hu,Matrix.trace_smul,Matrix.trace_one]
    norm_num

def portalActionHeat (m b t : ℝ) (Q : ScalarMomentum) (u : UnitVector ScalarMomentum) :=
  let X := ‖Q‖^2
  (t*Real.exp (-t*m^2)*(portalEuclidean b X)^2/(2*(2*Real.pi)^4*X)) *
    ∫ v in (0:ℝ)..1,
      (∫ k, (portalLinearVertex (k+Q) k u * portalLinearVertex k (k+Q) u).trace.re * portalHeatLeg t v Q k) -
      (1/t)*(∫ k:ScalarMomentum, (portalDirectVertex u).trace.re*Real.exp (-t*‖k‖^2))

theorem portal_action_proper_time (m b : ℝ) {t : ℝ} (ht : 0<t) (Q : ScalarMomentum) (hq : Q≠0)
    (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    portalActionHeat m b t Q u = portalBare m b (‖Q‖^2) t := by
  let X := ‖Q‖^2
  have hX : 0<X := sq_pos_of_pos (norm_pos_iff.mpr hq)
  let G := fun v => ∫ k, portalHeatLeg t v Q k
  let O := fun v => ∫ k, (2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k
  let D := ∫ k:ScalarMomentum, Real.exp (-t*‖k‖^2)
  have hg (v:ℝ) : Integrable (portalHeatLeg t v Q) := by
    apply two_line_gaussian_integrable
    linarith [show t*(1-v)+t*v=t by ring]
  have ho (v : ℝ) : Integrable (fun k => (2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k) := by
    by_contra h
    have hz := integral_undef h
    rw [portal_gaussian_orbital ht v Q u hQ,portal_gaussian_spin ht] at hz
    exact (ne_of_gt (by positivity)) hz
  have he (v:ℝ) : (∫ k, (portalLinearVertex (k+Q) k u * portalLinearVertex k (k+Q) u).trace.re * portalHeatLeg t v Q k) = 4*(O v+X*G v) := by
    have hn (k) : (portalLinearVertex (k+Q) k u * portalLinearVertex k (k+Q) u).trace.re * portalHeatLeg t v Q k =
       4*((2*⟪u.val,k⟫)^2*portalHeatLeg t v Q k + X*portalHeatLeg t v Q k) := by rw [(portal_dirac_vertices k Q u hQ).1]; dsimp [X];ring
    simp_rw [hn]
    rw [integral_const_mul,integral_add (ho v) ((hg v).const_mul X),integral_const_mul]
  have hD := (portal_dirac_vertices 0 Q u hQ).2
  have ha (v:ℝ) : 4*(O v+X*G v)-1/t*(8*D) = (4*X)*(G v+(O v-(2/t)*D)/X) := by field_simp; ring
  rw [←portal_resolved_proper_time m b ht Q hq u hQ]
  unfold portalActionHeat
  simp_rw [he,hD,integral_const_mul (8:ℝ)]
  change _*(∫ v in (0:ℝ)..1, 4*(O v+X*G v)-1/t*(8*D))=_
  simp_rw [ha]
  rw [intervalIntegral.integral_const_mul]
  unfold portalResolvedHeat
  change _ * ((4*X)*(∫ v in (0:ℝ)..1, G v+(O v-2/t*D)/X)) =
    _*(∫ v in (0:ℝ)..1, G v+(O v-2/t*D)/X)
  field_simp [hX.ne',Real.pi_ne_zero]
  dsimp only [X]
  ring

theorem portal_action_uv_obstruction (m : ℝ) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (Q : ScalarMomentum) (hq : Q≠0) (u : UnitVector ScalarMomentum) (hQ : ⟪u.val,Q⟫=0) :
    ¬ IntegrableOn (fun t => portalActionHeat m b t Q u) (Ioo 0 δ) := by
  intro h
  exact portal_bare_nonintegrable m hb (sq_pos_of_pos (norm_pos_iff.mpr hq)) hδ
    (h.congr_fun (fun t ht => portal_action_proper_time m b ht.1 Q hq u hQ) measurableSet_Ioo)

end UV

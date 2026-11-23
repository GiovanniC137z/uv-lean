import UV.ContinueSourceReviewSchurWard
import UV.ContinuePoleResidueSchur
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! A local holomorphic chart for a real point in the resolvent set of
the possibly unbounded self-adjoint boundary energy. The frequency is the
complex coordinate on the already selected sector; `p` denotes a real energy
in that coordinate. Both inverse equations use the original graph domain. -/

noncomputable section
namespace UV.SectorPlane
open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace ComplexConjugate

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : H →ₗ.[ℂ] H} {p : ℝ}

def closingRealPoleFactor (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (z : ℂ) : H →L[ℂ] H :=
  1+(z-(p:ℂ)) • R₀.map

def closingRealPoleChart (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (z : ℂ) : H →L[ℂ] H :=
  R₀.map*Ring.inverse (closingRealPoleFactor R₀ z)

omit [CompleteSpace H] in
theorem closing_real_pole_chart_at (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    closingRealPoleChart R₀ (p:ℂ)=R₀.map := by simp [closingRealPoleChart,closingRealPoleFactor]

theorem closing_real_pole_factor_unit (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    ∀ᶠ z in 𝓝 (p:ℂ), IsUnit (closingRealPoleFactor R₀ z) := by
  have hc : Continuous (closingRealPoleFactor R₀) := by unfold closingRealPoleFactor;fun_prop
  exact hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds (by simp [closingRealPoleFactor]))

omit [CompleteSpace H] in
/-- The chart with its two-sided graph inverse property at each admissible point. -/
def closingRealChartResolvent (R₀ : ClosingUnboundedResolvent B (p:ℂ)) (z : ℂ)
    (hu : IsUnit (closingRealPoleFactor R₀ z)) : ClosingUnboundedResolvent B z := by
  let F := closingRealPoleFactor R₀ z
  refine {map:=closingRealPoleChart R₀ z,inDomain:=fun v => R₀.inDomain (Ring.inverse F v),rightInverse:=?_,leftInverse:=?_}
  · intro v
    let y := Ring.inverse F v
    let u : B.domain := ⟨R₀.map y,R₀.inDomain y⟩
    have h := R₀.rightInverse y
    change (p:ℂ) • (u:H)+B u=y at h
    change z • (u:H)+B u=v
    calc _ = y+(z-(p:ℂ)) • (u:H) := by rw [←h];module
         _ = F y := rfl
         _ = v := by
           change (F * Ring.inverse F) v = _
           rw [Ring.mul_inverse_cancel F hu,one_apply]
  · intro u
    let y := (p:ℂ) • (u:H)+B u
    have he : F y=z • (u:H)+B u := by
      change y+(z-(p:ℂ)) • (R₀.map ((p:ℂ) • (u:H)+B u))=_
      rw [R₀.leftInverse u];dsimp only [y];module
    change R₀.map ((Ring.inverse F) (z • (u:H)+B u))=(u:H)
    rw [←he]
    change R₀.map ((Ring.inverse F * F) y)=_
    rw [Ring.inverse_mul_cancel F hu,one_apply]
    exact R₀.leftInverse u

theorem closing_real_pole_chart_graph (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    ∀ᶠ z in 𝓝 (p:ℂ), ∃ R : ClosingUnboundedResolvent B z, R.map=closingRealPoleChart R₀ z :=
  (closing_real_pole_factor_unit R₀).mono fun z hu => ⟨closingRealChartResolvent R₀ z hu,rfl⟩

theorem closing_real_pole_chart_nonreal (hB : IsSelfAdjoint B) (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    ∀ᶠ z in 𝓝 (p:ℂ), ∀ hz : z.im≠0, closingRealPoleChart R₀ z=(closingNonrealResolvent B hB z hz).map := by
  filter_upwards [closing_real_pole_factor_unit R₀] with z hu
  intro hz
  let R := closingRealChartResolvent R₀ z hu
  let N := closingNonrealResolvent B hB z hz
  apply ContinuousLinearMap.ext
  intro v
  change R.map v=N.map v
  calc R.map v = R.map (z • N.map v+B ⟨N.map v,N.inDomain v⟩) := congrArg R.map (N.rightInverse v).symm
       _ = N.map v := R.leftInverse ⟨_,N.inDomain v⟩

theorem closing_real_pole_map_selfAdjoint (hB : IsSelfAdjoint B) (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    IsSelfAdjoint R₀.map := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  let x : B.domain := ⟨R₀.map v,R₀.inDomain v⟩
  let y : B.domain := ⟨R₀.map w,R₀.inDomain w⟩
  have hs := closing_symmetric_of_selfAdjoint B hB x y
  change ⟪(x:H),w⟫_ℂ=⟪v,(y:H)⟫_ℂ
  calc _ = ⟪(x:H),(p:ℂ) • (y:H)+B y⟫_ℂ := congrArg (fun t => ⟪(x:H),t⟫_ℂ) (R₀.rightInverse w).symm
       _ = ⟪(p:ℂ) • (x:H)+B x,(y:H)⟫_ℂ := by
             simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal,hs]
       _ = _ := congrArg (fun t => ⟪t,(y:H)⟫_ℂ) (R₀.rightInverse v)

theorem closing_real_pole_chart_analytic (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    AnalyticAt ℂ (closingRealPoleChart R₀) (p:ℂ) := by
  have hf : AnalyticAt ℂ (closingRealPoleFactor R₀) (p:ℂ) := analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const)
  have hi : AnalyticAt ℂ Ring.inverse (closingRealPoleFactor R₀ (p:ℂ)) := by
    simpa only [closingRealPoleFactor,sub_self,zero_smul,add_zero,Units.val_one] using
      analyticAt_inverse (𝕜:=ℂ) (1:(H →L[ℂ] H)ˣ)
  exact analyticAt_const.mul (hi.comp hf)

theorem closing_real_pole_chart_hasDerivAt (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    HasDerivAt (closingRealPoleChart R₀) (-(R₀.map*R₀.map)) (p:ℂ) := by
  have hF : HasDerivAt (closingRealPoleFactor R₀) R₀.map (p:ℂ) := by
    simpa only [closingRealPoleFactor,one_smul] using ((((hasDerivAt_id (p:ℂ)).sub_const (p:ℂ)).smul_const R₀.map).const_add (1:H →L[ℂ] H))
  have hi : HasFDerivAt Ring.inverse _ (1:H →L[ℂ] H) := hasFDerivAt_ringInverse (𝕜:=ℂ) (1:(H →L[ℂ] H)ˣ)
  have h0 : closingRealPoleFactor R₀ (p:ℂ)=1 := by simp [closingRealPoleFactor]
  have h : HasFDerivAt Ring.inverse _ (closingRealPoleFactor R₀ (p:ℂ)) := h0.symm ▸ hi
  have hInv : HasDerivAt (fun z => Ring.inverse (closingRealPoleFactor R₀ z)) (-R₀.map) (p:ℂ) := by
    simpa using h.comp_hasDerivAt (p:ℂ) hF
  simpa only [closingRealPoleChart,mul_neg] using hInv.const_mul R₀.map

theorem closing_real_pole_schur_analytic (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    AnalyticAt ℂ (fun z => closingInverseSlot A T (closingRealPoleChart R₀ z) z) (p:ℂ) :=
  ((analyticAt_id.smul analyticAt_const).add analyticAt_const).sub
    (((closingSandwich T).analyticAt _).comp (closing_real_pole_chart_analytic R₀))

theorem closing_real_pole_schur_hasDerivAt (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p:ℂ)) :
    HasDerivAt (fun z => closingInverseSlot A T (closingRealPoleChart R₀ z) z)
      (closingTemporalMark T 1 R₀.map R₀.map) (p:ℂ) := by
  have hz := (((hasDerivAt_id (p:ℂ)).smul_const (1 : S →L[ℂ] S)).add_const A)
  have hs := (closingSandwich T).hasFDerivAt.comp_hasDerivAt (p:ℂ) (closing_real_pole_chart_hasDerivAt R₀)
  simpa only [closingInverseSlot,closingTemporalMark,Complex.ofReal_one,one_smul,map_neg,sub_neg_eq_add] using hz.sub hs

end UV.SectorPlane

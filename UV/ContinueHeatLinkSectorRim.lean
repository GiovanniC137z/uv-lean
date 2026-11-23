import UV.ContinueHeatLinkPoles
import UV.MassiveRunningPole

/-! Evaluation of the Euclidean heat-link residue on the two characters of
the prescribed sector-plane rim. The Euclidean argument is the negative
of the continued Minkowski shell square. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set UV.Carrier UV.HeatMaxwell
open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E]

def Plane.heatVectorRim (diamond : Plane E) (ε : Evolution) (h : Height)
    (s : ℝ) : ℂ × ℂ := -quotientCharacterEquiv (diamond.poleDenominator ε h s)

theorem Plane.heat_vector_rim_coordinates (diamond : Plane E) (ε : Evolution) (h : Height) (s : ℝ) :
    diamond.heatVectorRim ε h s =
      (-((s:ℂ)+Complex.I*((diamond.eta ε*(h:ℝ):ℝ):ℂ)),
       -((s:ℂ)-Complex.I*((diamond.eta ε*(h:ℝ):ℝ):ℂ))) := by
  simp [Plane.heatVectorRim,Plane.poleDenominator,directed,sub_eq_add_neg]

private theorem heat_rim_tendsto_punctured {η : ℝ} (hη : η ≠ 0) (s : ℝ) :
    Tendsto (fun h : Height => -((s:ℂ)+Complex.I*((η*(h:ℝ):ℝ):ℂ))) poleBoundaryHeights (𝓝[≠] (-(s:ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => -((s:ℂ)+Complex.I*((η*t:ℝ):ℂ))) := by fun_prop
    simpa only [mul_zero,Complex.ofReal_zero,add_zero] using
      (hc.continuousAt (x := 0)).tendsto.comp pole_height_tendsto_zero
  · apply Eventually.of_forall
    intro h
    change -((s:ℂ)+Complex.I*((η*(h:ℝ):ℝ):ℂ)) ≠ -(s:ℂ)
    simpa only [ne_eq,neg_inj,add_eq_left,mul_eq_zero,Complex.I_ne_zero,false_or,Complex.ofReal_eq_zero]
      using (mul_ne_zero hη h.property.ne')

/-- Both characters give the proposed positive real residue at the physical
sheet. The chart retains its actual shell square, evolution sign and height. -/
theorem Plane.heat_vector_rim_residues (diamond : Plane E) (ε : Evolution)
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (q : MassiveMomentum)
    (n : UnitVector Spatial) (k : ℝ) (hsp : q.2 = k • n.val)
    (hz : heatVectorDenominator m a (-((q.1^2-k^2 : ℝ):ℂ)) = 0) :
    let s := shellSquare q.1 q.2
    let L := ((Real.exp (-a^2*s)/(1+2*a^2*s) : ℝ):ℂ)
    Tendsto (fun h => let z := diamond.heatVectorRim ε h s
      ((z.1 + (s:ℂ))*heatFreeVector m a z.1,(z.2 + (s:ℂ))*heatFreeVector m a z.2))
      poleBoundaryHeights (𝓝 (L,L)) := by
  let s := shellSquare q.1 q.2
  have hs : s = q.1^2-k^2 := by
    simp [s,shellSquare,hsp,norm_smul,Real.norm_eq_abs,n.property]
  have h := heatFreeVector_residue_limit hm ha (hs.symm ▸ hz :
    heatVectorDenominator m a (-(s:ℂ)) = 0)
  have hη : diamond.eta ε ≠ 0 := by
    intro he
    simpa [he] using diamond.eta_sq ε
  have h₁ := h.comp (heat_rim_tendsto_punctured hη s)
  have h₂ := h.comp (heat_rim_tendsto_punctured (neg_ne_zero.mpr hη) s)
  have hL : Complex.exp ((a:ℂ)^2 * -(s:ℂ))/(1-2*(a:ℂ)^2 * -(s:ℂ)) =
      ((Real.exp (-a^2*s)/(1+2*a^2*s) : ℝ):ℂ) := by push_cast; simp [neg_mul]
  rw [hL] at h₁ h₂
  simpa only [Plane.heat_vector_rim_coordinates,Function.comp_apply,
    neg_mul,Complex.ofReal_neg,mul_neg,sub_eq_add_neg,neg_neg] using h₁.prodMk_nhds h₂

end UV.SectorPlane

import UV.ContinueNaimarkSchur
import UV.MassiveRunningPole

/-! The Abelian atom limit of the finite-slot Cauchy transform on the two
characters of the prescribed vectorial pole. Arbitrary Borel spectral
mass may accumulate at the measured energy. -/

noncomputable section
open Filter Set MeasureTheory UV.Carrier
open scoped Topology ComplexConjugate
namespace UV.SectorPlane

private def atomDisplacement (b : ℝ) (h : Height) : ℂ := Complex.I*((b*(h:ℝ):ℝ):ℂ)

private def atomRatio (a : ℂ) (e x : ℝ) : ℂ := a*((-(e:ℂ)+a+(x:ℂ))⁻¹)

private theorem atom_ratio_bound (b : ℝ) (h : Height) (e x : ℝ) :
    ‖atomRatio (atomDisplacement b h) e x‖ ≤ 1 := by
  let a := atomDisplacement b h
  let d := -(e:ℂ)+a+(x:ℂ)
  have hd : d.im=b*(h:ℝ) := by simp [d,a,atomDisplacement]
  have hle : ‖a‖ ≤ ‖d‖ := by
    simpa [hd,a,atomDisplacement] using Complex.abs_im_le_norm d
  change ‖a*d⁻¹‖ ≤ 1
  rw [←div_eq_mul_inv,norm_div]
  exact div_le_one_of_le₀ hle (norm_nonneg _)

private theorem atom_ratio_limit {b : ℝ} (hb : b≠0) (e x : ℝ) :
    Tendsto (fun h => atomRatio (atomDisplacement b h) e x) poleBoundaryHeights
      (𝓝 (if x=e then 1 else 0)) := by
  by_cases he : x=e
  · subst x
    have h (t : Height) : atomRatio (atomDisplacement b t) e e=1 := by
      have hn : atomDisplacement b t ≠ 0 := by simp [atomDisplacement,hb,t.property.ne']
      simpa [atomRatio,add_comm,add_left_comm,add_assoc] using mul_inv_cancel₀ hn
    simpa only [h,if_pos rfl] using (tendsto_const_nhds (x:=(1:ℂ)) (f:=poleBoundaryHeights))
  · have hzero : -(e:ℂ)+(x:ℂ) ≠ 0 := by
      rw [neg_add_eq_sub]
      exact sub_ne_zero.mpr (Complex.ofReal_injective.ne he)
    have ha : Tendsto (fun t => atomDisplacement b t) poleBoundaryHeights (𝓝 0) := by
      let A (u : ℝ) := Complex.I*((b*u:ℝ):ℂ)
      have hc : Continuous A := by dsimp [A]; fun_prop
      simpa [A,atomDisplacement,Function.comp_def] using hc.continuousAt.tendsto.comp pole_height_tendsto_zero
    have hd := (tendsto_const_nhds (x:=-(e:ℂ))).add ha |>.add (tendsto_const_nhds (x:=(x:ℂ)))
    simpa only [atomRatio,if_neg he,zero_mul] using ha.mul (hd.inv₀ (by simpa using hzero))

/-- An integrable complex density gives the actual singleton entry, along
either signed vertical approach, by dominated convergence. -/
theorem closing_vertical_density_atom (μ : Measure ℝ) {d : ℝ → ℂ} (hd : Integrable d μ)
    (e b : ℝ) (hb : b ≠ 0) :
    Tendsto (fun h : Height => let z := -(e:ℂ)+Complex.I*((b*(h:ℝ):ℝ):ℂ)
      (z+(e:ℂ)) * ∫ x, (z+(x:ℂ))⁻¹ * d x ∂μ)
      poleBoundaryHeights (𝓝 (∫ x in {e}, d x ∂μ)) := by
  let F (h : Height) (x : ℝ) := atomRatio (atomDisplacement b h) e x * d x
  have hF (h : Height) : AEStronglyMeasurable (F h) μ := by
    apply AEStronglyMeasurable.mul _ hd.aestronglyMeasurable
    apply Measurable.aestronglyMeasurable
    change Measurable (fun x : ℝ => atomDisplacement b h*((-(e:ℂ)+atomDisplacement b h+(x:ℂ))⁻¹))
    fun_prop
  have hlim : Tendsto (fun h => ∫ x, F h x ∂μ) poleBoundaryHeights
      (𝓝 (∫ x, ({e}:Set ℝ).indicator d x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖d x‖)
      (Eventually.of_forall hF) _ hd.norm
    · exact Eventually.of_forall fun x => by
        have h := (atom_ratio_limit hb e x).mul (tendsto_const_nhds (x:=d x))
        by_cases hx : x=e <;> simpa [F,hx,Set.indicator,Set.mem_singleton_iff] using h
    · exact Eventually.of_forall fun h => Eventually.of_forall fun x => by
        simpa only [F,norm_mul,one_mul] using
          mul_le_mul_of_nonneg_right (atom_ratio_bound b h e x) (norm_nonneg (d x))
  rw [integral_indicator (measurableSet_singleton e)] at hlim
  apply hlim.congr
  intro h
  dsimp only [F,atomRatio]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [atomDisplacement]
  ring

/-- Every entry of a finite matrix-valued measure obeys the two-character
atom formula at every real energy, including embedded atoms. -/
theorem Plane.closing_measured_pole_atom {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    (diamond : Plane E) (ε : Evolution) (M : Matrix ι ι (ComplexMeasure ℝ)) (e : ℝ) (i j : ι) :
    let F (z : ℂ) := (z+(e:ℂ))*closingMeasureEntryIntegral M (fun x => (z+(x:ℂ))⁻¹) i j
    Tendsto (fun h : Height => let z := quotientCharacterEquiv (diamond.poleDenominator ε h (-e))
      (F z.1,F z.2)) poleBoundaryHeights (𝓝 (M i j {e},M i j {e})) := by
  have hn : diamond.eta ε ≠ 0 := fun he => by simpa [he] using diamond.eta_sq ε
  have ha := closing_vertical_density_atom _ (closing_density_entry_integrable M i j) e (diamond.eta ε) hn
  have hb := closing_vertical_density_atom _ (closing_density_entry_integrable M i j) e (-(diamond.eta ε)) (neg_ne_zero.mpr hn)
  rw [closing_density_entry_integral M i j (measurableSet_singleton e)] at ha hb
  simpa [Plane.poleDenominator,directed,closingMeasureEntryIntegral,sub_eq_add_neg] using ha.prodMk_nhds hb

open Matrix
open scoped Matrix ComplexOrder InnerProductSpace

/-- On a unit slot both vertical limits give the same real atom weight
between zero and one for a normalized positive matrix spectral measure. -/
theorem Plane.closing_unit_slot_pole_atom {E ι : Type*} [NormedAddCommGroup E] [Fintype ι] [DecidableEq ι]
    (diamond : Plane E) (ε : Evolution) (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (hn : ClosingNormalizedMatrixMeasure M)
    (e : ℝ) (v : UnitVector (EuclideanSpace ℂ ι)) :
    let read (A : Matrix ι ι ℂ) := dotProduct (star (WithLp.ofLp v.val)) (A.mulVec (WithLp.ofLp v.val))
    let W := read (fun i j => M i j {e})
    let F (z : ℂ) := read (fun i j => (z+(e:ℂ))*closingMeasureEntryIntegral M (fun x => (z+(x:ℂ))⁻¹) i j)
    W = (W.re:ℂ) ∧ W.re ∈ Icc (0:ℝ) 1 ∧
      Tendsto (fun h : Height => let z := quotientCharacterEquiv (diamond.poleDenominator ε h (-e))
        (F z.1,F z.2)) poleBoundaryHeights (𝓝 (W,W)) := by
  let u := WithLp.ofLp v.val
  let Q (A : Matrix ι ι ℂ) := dotProduct (star u) (A.mulVec u)
  let A (s : Set ℝ) : Matrix ι ι ℂ := fun i j => M i j s
  let s : Set ℝ := {e}
  have hs : MeasurableSet s := measurableSet_singleton _
  have hQ : Continuous Q := continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  have hsplit : A s + A sᶜ = 1 := by
    rw [←show A univ=1 from hn]
    ext i j
    change M i j s+M i j sᶜ=M i j univ
    rw [←(M i j).of_union disjoint_compl_right hs hs.compl,union_compl_self]
  have hone : Q 1=1 := by
    change dotProduct (star u) ((1:Matrix ι ι ℂ).mulVec u)=1
    rw [one_mulVec,dotProduct_comm]
    change ⟪v.val,v.val⟫_ℂ=1
    simp [inner_self_eq_norm_sq_to_K,v.property]
  have hpos := RCLike.nonneg_iff.mp ((hM s hs).2 u)
  have hcompl := (hM sᶜ hs.compl).re_dotProduct_nonneg u
  have hadd : Q (A s)+Q (A sᶜ)=1 := by
    rw [←hone,←hsplit]
    exact (show Q (A s+A sᶜ)=Q (A s)+Q (A sᶜ) by simp [Q,add_mulVec,dotProduct_add]).symm
  change Q (A s)=((Q (A s)).re:ℂ) ∧ (Q (A s)).re ∈ Icc (0:ℝ) 1 ∧ _
  refine ⟨Complex.ext rfl (by exact hpos.2),⟨hpos.1,?_⟩,?_⟩
  · have h := congrArg Complex.re hadd
    rw [Complex.add_re,Complex.one_re] at h
    change 0 ≤ (Q (A sᶜ)).re at hcompl
    linarith
  · let z (h : Height) := quotientCharacterEquiv (diamond.poleDenominator ε h (-e))
    let B (p : ℂ) : Matrix ι ι ℂ := fun i j => (p+(e:ℂ))*closingMeasureEntryIntegral M (fun x => (p+(x:ℂ))⁻¹) i j
    have hlim (i j) := diamond.closing_measured_pole_atom ε M e i j
    have h₁ : Tendsto (fun h => B (z h).1) poleBoundaryHeights (𝓝 (A s)) :=
      tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => continuous_fst.continuousAt.tendsto.comp (hlim i j)
    have h₂ : Tendsto (fun h => B (z h).2) poleBoundaryHeights (𝓝 (A s)) :=
      tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => continuous_snd.continuousAt.tendsto.comp (hlim i j)
    exact (hQ.continuousAt.tendsto.comp h₁).prodMk_nhds (hQ.continuousAt.tendsto.comp h₂)

end UV.SectorPlane

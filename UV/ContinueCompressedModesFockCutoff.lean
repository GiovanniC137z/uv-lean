import UV.ContinueCompressedModesFockPhysicalTerm

/-! Actual Fock contractions on the independent continuous momenta of
their extracted cycles. The cutoff restricts all original charged slots
simultaneously, including momenta shifted by the external packet. -/

noncomputable section
open MeasureTheory Filter Set UV.SectorPlane
open scoped Topology ENNReal SchwartzMap Matrix.Norms.L2Operator

namespace UV.FermionWick
variable {ν ι V T : Type*} [NormedAddCommGroup V] [MeasurableSpace T]

def arcMomentum (σ : Equiv.Perm ν) {d : ℕ} (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) (q : EuclideanSpace ℝ (Fin d)) (k : Cycle σ→Spatial) (i : ν) :=
  k (cycleClass σ i)+(offset i+L i q)

private theorem arc_measurable (σ : Equiv.Perm ν) {d : ℕ} (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) (i : ν) :
    Measurable (fun z : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)) => arcMomentum σ offset L z.2.1 z.2.2 i) := by
  unfold arcMomentum
  exact ((measurable_pi_apply (cycleClass σ i)).comp (measurable_snd.comp measurable_snd)).add
    (measurable_const.add ((L i).continuous.measurable.comp (measurable_fst.comp measurable_snd)))

def timeFactor (es : List (Edge (Slot ν ι))) (tm : ν→ℝ) (m : ℝ) (p : ν→Spatial) : ℂ :=
  (es.map fun e => (e.sign:ℂ)*(Real.exp (-FurtherOptical.energy m (p (select true e).vertex)*
    |tm e.first.vertex-tm e.second.vertex|):ℂ)).prod

private theorem timeFactor_bound (es : List (Edge (Slot ν ι))) (h : ∀e∈es, e.sign=1 ∨ e.sign= -1)
    (tm : ν→ℝ) {m : ℝ} (hm : 0<m) (p : ν→Spatial) : ‖timeFactor es tm m p‖≤1 := by
  induction es with
  | nil => simp [timeFactor]
  | cons e es ih =>
    have h₀ : ‖(e.sign:ℂ)‖=1 := by rcases h e (List.mem_cons_self ..) with H|H <;> simp [H]
    have h₁ := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (FurtherOptical.energy_pos hm (p (select true e).vertex)).le) (abs_nonneg (tm e.first.vertex-tm e.second.vertex)))
    change ‖(_*_)*timeFactor es tm m p‖ ≤ 1
    rw [norm_mul,norm_mul,h₀,one_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul h₁ (ih (fun e he => h e (List.mem_cons_of_mem _ he))) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem measurable_timeFactor {Z : Type*} [MeasurableSpace Z] (es : List (Edge (Slot ν ι)))
    (t : Z→ν→ℝ) (ht : ∀i, Measurable (fun z=>t z i)) (m : ℝ)
    (p : Z→ν→Spatial) (hp : ∀i, Measurable (fun z=>p z i)) :
    Measurable (fun z => timeFactor es (t z) m (p z)) := by
  induction es with
  | nil => exact measurable_const
  | cons e es ih =>
    change Measurable (fun z => ((e.sign:ℂ)* (Real.exp (-(FurtherOptical.energy m (p z (select true e).vertex))*|t z e.first.vertex-t z e.second.vertex|):ℂ))*_)
    refine Measurable.mul ?_ ih
    unfold FurtherOptical.energy
    fun_prop

private theorem measurable_physical_entry {Z : Type*} [MeasurableSpace Z] {m : ℝ} (hm : 0<m)
    (bands : ν→Bool) (isDensity : ν→Bool) (u : ν→UnitVector Spatial) (p : Z→ν→Spatial)
    (hp : ∀i,Measurable (fun z=>p z i)) (row : ν→Fin 4) (i j : ν) :
    Measurable (fun z => physicalSpin m isDensity u bands (p z) row i i j) := by
  letI : MeasurableSpace DiracMatrix := borel _
  letI : BorelSpace DiracMatrix := ⟨rfl⟩
  have hc := (FurtherOptical.coefficients_continuous (τ:=0) hm).measurable
  have hD : Measurable diracSlash := by unfold diracSlash; fun_prop
  have hB (i : ν) : Measurable (fun z => seaEnergyBand (bands i) m (p z i)) := by
    unfold seaEnergyBand FurtherOptical.projector
    split_ifs <;> fun_prop (disch := exact hD.comp (hc.comp (hp i)))
  exact ((Matrix.entryLinearMap ℂ ℂ (row i) (row j)).toContinuousLinearMap.continuous.measurable).comp
    (((hB i).mul_const (chargeMatrix (isDensity i) (u i))).mul (hB j))

variable [Fintype ν]

def spinTime (σ : Equiv.Perm ν) (es : List (Edge (Slot ν ι))) (tm : ν→ℝ) (m : ℝ)
    (p : ν→Spatial) (isDensity : ν→Bool) (u : ν→UnitVector Spatial) (bands : ν→Bool) (row : ν→Fin 4) : ℂ :=
  timeFactor es tm m p * ∏ i : ν, physicalSpin m isDensity u bands p row i i (σ.symm i)

private theorem measurable_spinTime {Z : Type*} [MeasurableSpace Z] (σ : Equiv.Perm ν)
    (es : List (Edge (Slot ν ι))) (t : Z→ν→ℝ) (ht : ∀i,Measurable (fun z => t z i))
    {m : ℝ} (hm : 0<m) (p : Z→ν→Spatial) (hp : ∀i,Measurable (fun z => p z i))
    (isDensity : ν→Bool) (u : ν→UnitVector Spatial) (bands : ν→Bool) (row : ν→Fin 4) :
    Measurable (fun z => spinTime σ es (t z) m (p z) isDensity u bands row) := by
  unfold spinTime
  apply (measurable_timeFactor es t ht m p hp).mul
  exact Finset.measurable_prod _ (fun i _ => measurable_physical_entry hm bands isDensity u p hp row i (σ.symm i))

def bareGraph (diamond : Plane V) (σ : Equiv.Perm ν) (es : List (Edge (Slot ν ι)))
    (tm : T→ν→ℝ) {d : ℕ} (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ)) (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (bands : ν→Bool) (row : ν→Fin 4) (m ℓ : ℝ) (N : ℕ)
    (z : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial))) :=
  spinTime σ es (tm z.1) m (arcMomentum σ offset L z.2.1 z.2.2) isDensity u bands row * χ z.2.1 *
    ∏ c : Cycle σ, rimOnCycle diamond σ bands c (fun i => offset i+L i z.2.1) m ℓ N (z.2.2 c)

theorem bareGraph_integrable (diamond : Plane V) (σ : Equiv.Perm ν) (es : List (Edge (Slot ν ι)))
    (hsign : ∀e∈es,e.sign=1 ∨ e.sign= -1) (tm : T→ν→ℝ) (ht : ∀i, Measurable (fun t => tm t i))
    (μ : Measure T) [IsFiniteMeasure μ] {d : ℕ} (χ : 𝓢(EuclideanSpace ℝ (Fin d),ℂ)) (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (bands : ν→Bool) (row : ν→Fin 4) (t₀ : ν→ℝ)
    (ho : ∀i, if bands i then t₀ i<t₀ (σ i) else t₀ (σ i)<t₀ i)
    {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) {N : ℕ} (hN : 2≤N) :
    Integrable (bareGraph diamond σ es tm χ offset L isDensity u bands row m ℓ N) (μ.prod (volume.prod volume)) := by
  apply contribution_integrable diamond σ bands μ χ t₀ ho offset L hm hℓ hN
  · apply Measurable.aestronglyMeasurable
    let Z := T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial))
    let p := fun (z:Z) => arcMomentum σ offset L z.2.1 z.2.2
    let t := fun (z:Z) => tm z.1
    exact measurable_spinTime σ es t (fun i => (ht i).comp measurable_fst) hm p (arc_measurable σ offset L) isDensity u bands row
  · intro z
    rw [spinTime,norm_mul,norm_prod]
    apply (mul_le_mul (timeFactor_bound es hsign _ hm _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ =>
      physicalSpin_bound hm isDensity u bands _ row i i (σ.symm i))) (by positivity) zero_le_one).trans_eq (one_mul _)

def sectionBound {d : ℕ} (σ : Equiv.Perm ν) (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial) (R : ℕ) :
    Set (T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial))) :=
  {z | ∀i:ν, ‖arcMomentum σ offset L z.2.1 z.2.2 i‖≤R}

theorem remove_sections (σ : Equiv.Perm ν) {d : ℕ} (offset : ν→Spatial)
    (L : ν→EuclideanSpace ℝ (Fin d)→L[ℝ] Spatial)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {μ : Measure (T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial)))} {F : T × (EuclideanSpace ℝ (Fin d) × (Cycle σ→Spatial))→Z}
    (hF : Integrable F μ) :
    Tendsto (fun R:ℕ => ∫ z in sectionBound σ offset L R,F z ∂μ) atTop (𝓝 (∫z,F z ∂μ)) := by
  have hM (R:ℕ) : MeasurableSet (sectionBound (T:=T) σ offset L R) := by
    simp only [sectionBound,setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (arc_measurable σ offset L i).norm measurable_const)
  have hM' : Monotone (sectionBound (T:=T) σ offset L) := fun _ _ h _ hz i => (hz i).trans (by exact_mod_cast h)
  have hcov : (⋃R:ℕ,sectionBound (T:=T) σ offset L R)=univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨R,hR⟩ := exists_nat_ge (∑i:ν,‖arcMomentum σ offset L z.2.1 z.2.2 i‖)
    exact mem_iUnion.mpr ⟨R,fun i => (Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)).trans hR⟩
  have ht := tendsto_setIntegral_of_monotone hM hM' hF.integrableOn
  simpa only [hcov,setIntegral_univ] using ht

end UV.FermionWick

import UV.ContinueOrderedHopWindingCost
import Mathlib.MeasureTheory.Function.Floor

/-! Exact unfolding of a based spatial torus word. First partition each
independent displacement into a physical half-open cube and its integer
lift. Then reindex the lifts on all N hops by their total winding and the
N−1 independent lifts. All equalities hold for the absolute integrals,
also before proving finiteness. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace UV.SectorPlane

variable {n : ℕ}

def orderedHopSpatialCell (L : ℝ) (n : ℕ) : Set (Fin n → Spatial) :=
  {z | ∀ i j, z i j ∈ Ico 0 L}

private def physicalCellIndex (L : ℝ) (z : Fin n → Spatial) (i : Fin n) (j : Fin 3) : ℤ :=
  ⌊z i j / L⌋

private def physicalCell (L : ℝ) (h : Fin n → OrderedHopWinding) : Set (Fin n → Spatial) :=
  (physicalCellIndex L) ⁻¹' {h}

private theorem physical_cell_measurable (L : ℝ) (h : Fin n → OrderedHopWinding) : MeasurableSet (physicalCell L h) := by
  apply MeasurableSet.preimage (measurableSet_singleton h)
  apply measurable_pi_lambda; intro i
  apply measurable_pi_lambda; intro j
  apply Int.measurable_floor.comp
  exact (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp (continuous_apply i)).div_const L).measurable

private theorem physical_cell_translate {L : ℝ} (hL : 0 < L) (h : Fin n → OrderedHopWinding) :
    (fun x : Fin n → Spatial => x + fun i => orderedHopLattice L (h i)) ⁻¹' physicalCell L h = orderedHopSpatialCell L n := by
  ext z
  change (fun i j => ⌊(z i j + L*(h i j:ℝ))/L⌋) = h ↔ ∀ i j, z i j ∈ Ico 0 L
  have he (i j) : (z i j + L*(h i j:ℝ))/L = z i j/L + (h i j:ℝ) := by field_simp
  simp only [he,funext_iff,Int.floor_add_intCast,add_eq_right,Int.floor_eq_zero_iff,mem_Ico,
    show ∀ x : ℝ, 0 ≤ x / L ↔ 0 ≤ x from fun x => by simpa using (le_div_iff₀ hL : (0:ℝ) ≤ x/L ↔ _),
    div_lt_one hL]

/-- The half-open cubes exactly partition all independent physical
displacements, without counting any lattice face twice. -/
theorem orderedHop_cell_unfold {L : ℝ} (hL : 0 < L) (F : (Fin n → Spatial) → ℝ≥0∞) :
    (∑' h : Fin n → OrderedHopWinding, ∫⁻ x in orderedHopSpatialCell L n, F (fun i => x i + orderedHopLattice L (h i))) =
      ∫⁻ z, F z := by
  have hU : ⋃ h : Fin n → OrderedHopWinding, physicalCell L h = univ :=
    eq_univ_of_forall fun z => mem_iUnion.mpr ⟨physicalCellIndex L z,rfl⟩
  have hD : Pairwise (fun h k : Fin n → OrderedHopWinding => Disjoint (physicalCell L h) (physicalCell L k)) :=
    fun h k hne => Set.disjoint_left.mpr fun _ hh hk => hne (hh.symm.trans hk)
  have hl := lintegral_iUnion (μ := volume) (physical_cell_measurable L) hD F
  rw [hU,Measure.restrict_univ] at hl
  apply Eq.trans _ hl.symm
  apply tsum_congr
  intro h
  let A := fun i => orderedHopLattice L (h i)
  have he := (measurePreserving_add_right volume A).setLIntegral_comp_preimage_emb
    (Homeomorph.addRight A).measurableEmbedding F (physicalCell L h)
  rw [physical_cell_translate hL h] at he
  exact he

def orderedHopWindingAllocation (n : ℕ) : (OrderedHopWinding × (Fin n → OrderedHopWinding)) ≃
    (Fin (n+1) → OrderedHopWinding) where
  toFun z := Fin.cons (z.1 - ∑ i, z.2 i) z.2
  invFun k := (∑ j, k j, fun i => k i.succ)
  left_inv z := by simp [Fin.sum_univ_succ]
  right_inv k := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.sum_univ_succ]

private def orderedHopLatticeHom (L : ℝ) : OrderedHopWinding →+ Spatial where
  toFun := orderedHopLattice L
  map_zero' := by ext j; simp [orderedHopLattice]
  map_add' := by intro w h; ext j; simp [orderedHopLattice,mul_add]

/-- All spatial increments of a based lifted path. The first displacement
closes the path with total lifted displacement D. -/
def orderedHopSpatialIncrements (D : Spatial) (z : Fin n → Spatial) : Fin (n+1) → Spatial :=
  Fin.cons (D - ∑ i, z i) z

private theorem spatial_increments_cont (D : Spatial) :
    Continuous (orderedHopSpatialIncrements (n := n) D) := by
  apply continuous_pi; intro j
  refine Fin.cases ?_ (fun i => continuous_apply i) j
  exact continuous_const.sub (continuous_finset_sum _ fun i _ => continuous_apply i)

theorem orderedHop_lift_allocation (L : ℝ) (w : OrderedHopWinding) (h : Fin n → OrderedHopWinding)
    (z : Fin n → Spatial) :
    (fun j => orderedHopSpatialIncrements 0 z j + orderedHopLattice L (orderedHopWindingAllocation n (w,h) j)) =
      orderedHopSpatialIncrements (orderedHopLattice L w) (fun i => z i+orderedHopLattice L (h i)) := by
  funext j
  refine Fin.cases ?_ (fun _ => rfl) j
  change (0 - ∑ i, z i) + orderedHopLatticeHom L (w-∑ i, h i) =
    orderedHopLatticeHom L w - ∑ i, (z i + orderedHopLatticeHom L (h i))
  rw [map_sub,map_sum,Finset.sum_add_distrib]
  abel

/-- In any fixed carrier configuration, the based cell integral over all
periodic spatial lifts equals the sum of the original Euclidean displacement
integrals closed at Lw, in the same cyclic order. -/
theorem orderedHop_torus_unfold {L : ℝ} (hL : 0 < L)
    {F : (Fin (n+1) → Spatial) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in orderedHopSpatialCell L n, ∑' k : Fin (n+1) → OrderedHopWinding,
        F (fun j => orderedHopSpatialIncrements 0 z j+orderedHopLattice L (k j))) =
      ∑' w : OrderedHopWinding, ∫⁻ z : Fin n → Spatial, F (orderedHopSpatialIncrements (orderedHopLattice L w) z) := by
  let A := fun (k : Fin (n+1) → OrderedHopWinding) (z : Fin n → Spatial) =>
    F (fun j => orderedHopSpatialIncrements 0 z j + orderedHopLattice L (k j))
  have hA (k) : Measurable (A k) := by
    apply hF.comp
    apply measurable_pi_lambda; intro j
    exact ((continuous_apply j).comp (spatial_increments_cont 0)).measurable.add measurable_const
  change (∫⁻ z in orderedHopSpatialCell L n, ∑' k, A k z) = _
  rw [lintegral_tsum (fun k => (hA k).aemeasurable),← (orderedHopWindingAllocation n).tsum_eq]
  change (∑' p : OrderedHopWinding × (Fin n → OrderedHopWinding), ∫⁻ z in orderedHopSpatialCell L n,
    A (orderedHopWindingAllocation n (p.1,p.2)) z) = _
  rw [ENNReal.tsum_prod (f := fun w h => ∫⁻ z in orderedHopSpatialCell L n, A (orderedHopWindingAllocation n (w,h)) z)]
  apply tsum_congr
  intro w
  simp only [A,orderedHop_lift_allocation]
  exact orderedHop_cell_unfold hL (fun z => F (orderedHopSpatialIncrements (orderedHopLattice L w) z))

private theorem spatial_cell_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {L : ℝ} (hL : 0 < L) {F : (Fin n → Spatial) → E} (hF : Integrable F) :
    HasSum (fun h : Fin n → OrderedHopWinding => ∫ x in orderedHopSpatialCell L n,
      F (fun i => x i+orderedHopLattice L (h i))) (∫ z, F z) := by
  have hU : ⋃ h : Fin n → OrderedHopWinding, physicalCell L h = univ :=
    eq_univ_of_forall fun z => mem_iUnion.mpr ⟨physicalCellIndex L z,rfl⟩
  have hD : Pairwise (fun h k : Fin n → OrderedHopWinding => Disjoint (physicalCell L h) (physicalCell L k)) :=
    fun h k hne => Set.disjoint_left.mpr fun _ hh hk => hne (hh.symm.trans hk)
  have hs := hasSum_integral_iUnion (physical_cell_measurable L) hD hF.integrableOn
  rw [hU,setIntegral_univ] at hs
  apply hs.congr_fun
  intro h
  let A := fun i => orderedHopLattice L (h i)
  have he := (measurePreserving_add_right volume A).setIntegral_preimage_emb
    (Homeomorph.addRight A).measurableEmbedding F (physicalCell L h)
  rw [physical_cell_translate hL h] at he
  exact he

/-- Signed/complex unfolding for any absolutely summable family of winding
integrals. The finite-volume spatial cell and the full-space winding
integrals are in physical Lebesgue units, without a Jacobian correction. -/
theorem orderedHop_torus_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {L : ℝ} (hL : 0 < L) (F : (Fin (n+1) → Spatial) → E)
    (hi : ∀ w, Integrable (fun z => F (orderedHopSpatialIncrements (orderedHopLattice L w) z)))
    (hs : Summable (fun w => ∫ z, ‖F (orderedHopSpatialIncrements (orderedHopLattice L w) z)‖)) :
    (∫ z in orderedHopSpatialCell L n, ∑' k : Fin (n+1) → OrderedHopWinding,
      F (fun j => orderedHopSpatialIncrements 0 z j+orderedHopLattice L (k j))) =
      ∑' w : OrderedHopWinding, ∫ z : Fin n → Spatial, F (orderedHopSpatialIncrements (orderedHopLattice L w) z) := by
  let f := fun (w : OrderedHopWinding) (z : Fin n → Spatial) => F (orderedHopSpatialIncrements (orderedHopLattice L w) z)
  let A := fun (p : OrderedHopWinding × (Fin n → OrderedHopWinding)) (z : Fin n → Spatial) =>
    f p.1 (fun i => z i+orderedHopLattice L (p.2 i))
  have hA (p) : IntegrableOn (A p) (orderedHopSpatialCell L n) :=
    ((measurePreserving_add_right volume (fun i => orderedHopLattice L (p.2 i))).integrable_comp_of_integrable (hi p.1)).integrableOn
  have hN : Summable (fun p => ∫ z in orderedHopSpatialCell L n, ‖A p z‖) := by
    apply (summable_prod_of_nonneg fun _ => integral_nonneg fun _ => norm_nonneg _).mpr
    refine ⟨fun w => (spatial_cell_hasSum hL (hi w).norm).summable,?_⟩
    simpa only [A,f,fun w => (spatial_cell_hasSum hL (hi w).norm).tsum_eq] using hs
  have hV := hN.of_norm_bounded (fun p => norm_integral_le_integral_norm (A p))
  have he (z : Fin n → Spatial) :
      (∑' k : Fin (n+1) → OrderedHopWinding, F (fun j => orderedHopSpatialIncrements 0 z j+orderedHopLattice L (k j))) =
        ∑' p, A p z := by
    rw [← (orderedHopWindingAllocation n).tsum_eq]
    apply tsum_congr
    rintro ⟨w,h⟩
    rw [orderedHop_lift_allocation]
  simp_rw [he]
  refine (integral_tsum_of_summable_integral_norm hA hN).symm.trans (hV.tsum_prod.trans ?_)
  exact tsum_congr fun w => (spatial_cell_hasSum hL (hi w)).tsum_eq

end UV.SectorPlane

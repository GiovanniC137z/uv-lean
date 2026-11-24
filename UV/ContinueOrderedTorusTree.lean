import UV.ContinueOrderedTorusPhoton
import UV.ContinueOrderedEnvelopeChart
import UV.ContinuePinnedNormalForest
import Mathlib.MeasureTheory.Integral.Pi

/-! Spatial momenta stay on the reciprocal lattice after the vertex balance
is solved. The spatial incidence inverse is an integer matrix. The carrier
frequency remains a real variable with Lebesgue measure. -/

noncomputable section
open MeasureTheory Matrix Set Real
open scoped ENNReal Matrix
namespace UV.SectorPlane

abbrev OrderedTorusTransfer := OrderedHopWinding × ℝ
def orderedTorusTransferMeasure : Measure OrderedTorusTransfer :=
  (Measure.count : Measure OrderedHopWinding).prod volume

instance : SigmaFinite orderedTorusTransferMeasure := inferInstanceAs
  (SigmaFinite ((Measure.count : Measure OrderedHopWinding).prod (volume : Measure ℝ)))

def OrderedPhotonKind.torusLine (kind : OrderedPhotonKind) (δ : Fin 3 → ℝ) (r : ℝ)
    (x : OrderedTorusTransfer) : ℝ :=
  match kind with
  | .transverse => orderedTorusTransverse δ r x.1 x.2
  | .coulomb => orderedTorusCoulomb δ r x.1 x.2

theorem OrderedPhotonKind.torusLine_nonneg (kind : OrderedPhotonKind) (δ : Fin 3 → ℝ) (r : ℝ)
    (x : OrderedTorusTransfer) : 0 ≤ kind.torusLine δ r x := by
  cases kind <;> simp only [torusLine,orderedTorusTransverse,orderedTorusCoulomb]
    <;> split_ifs <;> positivity

theorem OrderedPhotonKind.torusLine_measurable (kind : OrderedPhotonKind) (δ : Fin 3 → ℝ) (r : ℝ) :
    Measurable (kind.torusLine δ r) := by
  have hS : Measurable (fun x : OrderedTorusTransfer => ‖orderedTorusMomentum δ x.1‖) :=
    (measurable_of_countable (fun k => ‖orderedTorusMomentum δ k‖)).comp measurable_fst
  have hz : MeasurableSet {x : OrderedTorusTransfer | x.1 = 0} := measurableSet_eq_fun measurable_fst measurable_const
  cases kind <;> unfold torusLine orderedTorusTransverse orderedTorusCoulomb <;>
    apply Measurable.ite hz measurable_const <;> fun_prop (disch := assumption)

theorem OrderedPhotonKind.torusLine_integrable (kind : OrderedPhotonKind) {δ : Fin 3 → ℝ}
    {d r : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i) (hr : 0 < r) :
    Integrable (kind.torusLine δ r) orderedTorusTransferMeasure := by
  refine ⟨(kind.torusLine_measurable δ r).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (kind.torusLine_nonneg δ r)),orderedTorusTransferMeasure,
    lintegral_prod _ (kind.torusLine_measurable δ r).ennreal_ofReal.aemeasurable, lintegral_count]
  obtain ⟨hT,hC⟩ := ordered_torus_spatial_chord_budgets hd hδ hr
  cases kind
  · simp only [torusLine,(ordered_torus_photon_time hd hδ r _).1,ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  · simp only [torusLine,(ordered_torus_photon_time hd hδ r _).2,ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by norm_num) (hC.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

/-- Grounded integer incidence, with rows at vertices and columns at edges. -/
def orderedIntegerIncidence {E : Type*} {n : ℕ} (src dst : E → Option (Fin n)) : Matrix (Fin n) E ℤ :=
  fun j e => (if dst e = some j then 1 else 0)-(if src e = some j then 1 else 0)

private theorem orderedIntegerIncidence_real {E : Type*} {n : ℕ} (src dst : E → Option (Fin n)) :
    (orderedIntegerIncidence src dst).map (fun z => (z:ℝ)) = (UV.groundedNetworkIncidence src dst)ᵀ := by
  ext i j; simp only [orderedIntegerIncidence,Matrix.map_apply,transpose_apply,UV.groundedNetworkIncidence]
  split_ifs <;> norm_num

/-- For the labelled tree selected in a connected routing, the square inverse
has integer entries. Fixed external lattice transfers may be arbitrary. -/
theorem ordered_torus_tree_det_unit {n : ℕ} (src dst : Fin n → Option (Fin n))
    (hTree : (UV.groundedSupportGraph src dst).IsTree) : IsUnit (orderedIntegerIncidence src dst).det := by
  let M := orderedIntegerIncidence src dst
  have hdet : (UV.groundedNetworkIncidence src dst).det ≠ 0 := by
    have hi := (UV.grounded_incidence_injective_iff_tree src dst (by simp [Nat.card_eq_fintype_card])).mpr hTree
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hi))
  have h := UV.grounded_incidence_det_sq src dst
  simp only [Matrix.det_transpose, pow_ne_zero _ hdet, false_or] at h
  have hh : ((M.det:ℝ))^2 = 1 := by rwa [Int.cast_det,orderedIntegerIncidence_real,Matrix.det_transpose]
  have hz : M.det^2 = 1 := by exact_mod_cast hh
  apply (isUnit_pow_iff (by decide : (2:ℕ) ≠ 0)).mp
  rw [hz]; exact isUnit_one

/-- The same tree solves integer spatial and real carrier balance, including
self-chords with zero incidence. Every independent momentum occurs unchanged
on its own chord. -/
def orderedTorusTreeFlow {n : ℕ} {J : Type*} [Fintype J]
    (src dst : Fin n → Option (Fin n)) (u v : J → Option (Fin n))
    (b : Fin n → OrderedTorusTransfer) (q : J → OrderedTorusTransfer) (i : Fin n) : OrderedTorusTransfer :=
  let M := orderedIntegerIncidence src dst
  let D := orderedIntegerIncidence u v
  (fun j => (M⁻¹ *ᵥ ((fun k => (b k).1 j)-D *ᵥ (fun k => (q k).1 j))) i,
    ((M.map (fun z => (z:ℝ)))⁻¹ *ᵥ ((fun k => (b k).2)-(D.map (fun z => (z:ℝ))) *ᵥ (fun k => (q k).2))) i)

theorem ordered_torus_tree_balance {n : ℕ} {J : Type*} [Fintype J]
    (src dst : Fin n → Option (Fin n)) (hTree : (UV.groundedSupportGraph src dst).IsTree)
    (u v : J → Option (Fin n)) (b : Fin n → OrderedTorusTransfer) (q : J → OrderedTorusTransfer) :
    let M := orderedIntegerIncidence src dst
    let D := orderedIntegerIncidence u v
    let F := orderedTorusTreeFlow src dst u v b q
    (∀ j, M *ᵥ (fun i => (F i).1 j) + D *ᵥ (fun k => (q k).1 j) = (fun i => (b i).1 j)) ∧
    (M.map (fun z => (z:ℝ))) *ᵥ (fun i => (F i).2) +
      (D.map (fun z => (z:ℝ))) *ᵥ (fun k => (q k).2) = (fun i => (b i).2) := by
  intro M D F
  have hM := ordered_torus_tree_det_unit src dst hTree
  have hR : IsUnit ((M.map (fun z => (z:ℝ))).det) := by
    rw [←Int.cast_det]; exact hM.map (Int.castRingHom ℝ)
  constructor
  · intro j
    change M *ᵥ (M⁻¹ *ᵥ _) + _ = _
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hM,Matrix.one_mulVec,sub_add_cancel]
  · change (M.map (fun z => (z:ℝ))) *ᵥ ((M.map (fun z => (z:ℝ)))⁻¹ *ᵥ _) + _ = _
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hR,Matrix.one_mulVec,sub_add_cancel]

/-- Absolute integrability of any contribution bounded by the product of the
actual photon lines in the solved torus routing. The tree bound also applies
to fixed nonzero bridge transfers and to the absent spatial harmonic. -/
theorem ordered_torus_tree_chord_integrable {n : ℕ} {J : Type*} [Fintype J]
    (src dst : Fin n → Option (Fin n)) (u v : J → Option (Fin n))
    (b : Fin n → OrderedTorusTransfer) (tree : Fin n → OrderedPhotonKind) (chord : J → OrderedPhotonKind)
    {δ : Fin 3 → ℝ} {d r : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i) (hr : 0 < r)
    (A : (J → OrderedTorusTransfer) → ℂ)
    (hA : AEStronglyMeasurable A (Measure.pi fun _ : J => orderedTorusTransferMeasure))
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ q ∂Measure.pi (fun _ : J => orderedTorusTransferMeasure), ‖A q‖ ≤
      K*((∏ i, (tree i).torusLine δ r (orderedTorusTreeFlow src dst u v b q i))*
        ∏ c, (chord c).torusLine δ r (q c))) :
    Integrable A (Measure.pi fun _ : J => orderedTorusTransferMeasure) := by
  apply ((Integrable.fintype_prod fun c => (chord c).torusLine_integrable hd hδ hr).const_mul
    (K*((d^2)⁻¹)^n)).mono' hA
  filter_upwards [hb] with q hq
  let f (i : Fin n) := (tree i).torusLine δ r (orderedTorusTreeFlow src dst u v b q i)
  have hf (i) : 0 ≤ f i := (tree i).torusLine_nonneg _ _ _
  have htree : (∏ i, f i) ≤ ((d^2)⁻¹)^n := by
    calc
      _ ≤ ∏ _i : Fin n, (d^2)⁻¹ := by
        apply Finset.prod_le_prod (fun i _ => hf i)
        intro i _
        obtain ⟨h₁,h₂⟩ := ordered_torus_bridge_bound hd hδ hr.le
          (orderedTorusTreeFlow src dst u v b q i).1 (orderedTorusTreeFlow src dst u v b q i).2
        dsimp [f,OrderedPhotonKind.torusLine]; split <;> assumption
      _ = _ := by simp
  rw [mul_assoc]
  exact hq.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htree
    (Finset.prod_nonneg (fun c _ => (chord c).torusLine_nonneg _ _ _))) hK)

end UV.SectorPlane

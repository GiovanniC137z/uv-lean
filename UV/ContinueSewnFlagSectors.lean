import UV.ContinueSewnFlagTime
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Instances.Matrix

/-! The positive orthant is covered, almost everywhere, by the
finitely many strict duration orderings. Row relabelling preserves
the actual covariance, inverse form, and heat density. -/

noncomputable section
open Real MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal Matrix
namespace UV.SewnFlags

def positiveDurations (N : ℕ) : Set (Fin N → ℝ) := {t | ∀ i, 0 < t i}

theorem positiveDurations_measurable (N : ℕ) : MeasurableSet (positiveDurations N) := by
  have he : positiveDurations N = ⋂ i : Fin N, {t | 0 < t i} := by
    ext t
    simp [positiveDurations]
  rw [he]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

def reindexRouting {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (e : Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin L) ℝ :=
  C.submatrix e id

@[simp] theorem reindexRouting_mulVec {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (e : Equiv.Perm (Fin N)) (v : Fin L → ℝ) (i : Fin N) :
    (reindexRouting C e *ᵥ v) i = (C *ᵥ v) (e i) := rfl

theorem reindexRouting_injective {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (e : Equiv.Perm (Fin N)) :
    Function.Injective (reindexRouting C e).mulVec := by
  intro v w h
  apply hC
  funext i
  simpa only [reindexRouting_mulVec,e.apply_symm_apply] using congrFun h (e.symm i)

theorem reindexRouting_face {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (e : Equiv.Perm (Fin N)) (S : Finset (Fin N)) :
    routingFace (reindexRouting C e) S = routingFace C (S.map e.toEmbedding) := by
  ext x
  change (∀ i ∉ S, (reindexRouting C e *ᵥ x.ofLp) i = 0) ↔
    (∀ i ∉ S.map e.toEmbedding, (C *ᵥ x.ofLp) i = 0)
  constructor
  · intro h i hi
    have h' : e.symm i ∉ S := by
      intro he
      apply hi
      exact Finset.mem_map.mpr ⟨e.symm i,he,e.apply_symm_apply _⟩
    simpa only [reindexRouting_mulVec,e.apply_symm_apply] using h _ h'
  · intro h i hi
    rw [reindexRouting_mulVec]
    apply h
    simpa only [Finset.mem_map_equiv,e.symm_apply_apply] using hi

theorem reindexRouting_prefix_cost {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (e : Equiv.Perm (Fin N)) (ν : Fin N → ℝ) (i : Fin N)
    (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    displacementCost (routingFaceExcess (reindexRouting C e) (ν ∘ e) i)
      (projectedDisplacement (reindexRouting C e) (routingShortPrefix i) d) =
    let S := (routingShortPrefix i).map e.toEmbedding
    displacementCost ((∑ j ∈ S, ν j) - 2 * Module.finrank ℝ (routingFace C S))
      (projectedDisplacement C S d) := by
  dsimp only
  have h := reindexRouting_face C e (routingShortPrefix i)
  unfold routingFaceExcess directionalOrderedPrefix
  rw [h]
  unfold projectedDisplacement
  simp only [h]
  simp only [Finset.sum_map,routingShortPrefix,Finset.sum_filter,
    Equiv.toEmbedding_apply,Function.comp_apply]

theorem reindexRouting_gram {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (e : Equiv.Perm (Fin N)) (t : Fin N → ℝ) :
    residualGram (reindexRouting C e) (t ∘ e) = residualGram C t := by
  unfold residualGram
  ext j k
  rw [Matrix.mul_apply (N := reindexRouting C e), Matrix.mul_apply (N := C)]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,
    reindexRouting,Matrix.submatrix_apply,id_eq,Function.comp_apply]
  exact Equiv.sum_comp e (fun i => C i j * t i * C i k)

theorem reindexRouting_mass_weight {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (e : Equiv.Perm (Fin N)) (ν m t : Fin N → ℝ)
    (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
    routedMassSchwingerWeight (reindexRouting C e) (ν ∘ e) (m ∘ e) (t ∘ e) d =
      routedMassSchwingerWeight C ν m t d := by
  unfold routedMassSchwingerWeight routedSchwingerWeight routedInverseWeight
  simp only [reindexRouting_gram,Function.comp_apply]
  rw [Equiv.sum_comp e (fun i => (m i)^2*t i), Equiv.prod_comp e (fun i => t i^(ν i-1))]

local instance {L : ℕ} : MeasurableSpace (Matrix (Fin L) (Fin L) ℝ) := borel _
local instance {L : ℕ} : BorelSpace (Matrix (Fin L) (Fin L) ℝ) := ⟨rfl⟩

theorem routedMassSchwingerWeight_measurable {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν m : Fin N → ℝ) :
    Measurable (fun x : (EuclideanSpace ℝ (Fin L × Fin 4)) × (Fin N → ℝ) =>
      routedMassSchwingerWeight C ν m x.2 x.1) := by
  have hGij (i j : Fin L) :
      Continuous (fun t : Fin N → ℝ => residualGram C t i j) := by
    have he (t : Fin N → ℝ) : residualGram C t i j = ∑ r, C r i*t r*C r j := by
      unfold residualGram
      rw [Matrix.mul_apply (N := C)]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
    simp_rw [he]
    exact continuous_finset_sum _ (fun r _ => (continuous_const.mul (continuous_apply r)).mul continuous_const)
  have hG : Continuous (residualGram C) :=
    continuous_pi (fun i => continuous_pi (fun j => hGij i j))
  let P := (EuclideanSpace ℝ (Fin L × Fin 4)) × (Fin N → ℝ)
  have hdet : Measurable (fun x : P => (residualGram C x.2).det) :=
    hG.matrix_det.measurable.comp measurable_snd
  have hInv : Measurable (fun t : Fin N → ℝ => (residualGram C t)⁻¹) := by
    simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
    exact hG.matrix_det.measurable.inv.smul hG.matrix_adjugate.measurable
  have hentry (i j : Fin L) : Measurable (fun x : P => ((residualGram C x.2)⁻¹) i j) := by
    have h : Continuous (fun A : Matrix (Fin L) (Fin L) ℝ => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact h.measurable.comp (hInv.comp measurable_snd)
  have ht (i : Fin N) : Measurable (fun x : P => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hd (i : Fin L) (r : Fin 4) : Measurable (fun x : P => x.1 (i,r)) := by
    have h : Continuous (fun x : EuclideanSpace ℝ (Fin L × Fin 4) => x (i,r)) :=
      PiLp.continuous_apply 2 (fun _ : Fin L × Fin 4 => ℝ) (i,r)
    exact h.measurable.comp measurable_fst
  have hQ (r : Fin 4) :
      Measurable (fun x : P => ∑ i, x.1 (i,r)*∑ j, ((residualGram C x.2)⁻¹) i j * x.1 (j,r)) :=
    Finset.measurable_sum _ (fun i _ => (hd i r).mul
      (Finset.measurable_sum _ (fun j _ => (hentry i j).mul (hd j r))))
  have hM : Measurable (fun x : P => exp (-(∑ i, (m i)^2*x.2 i))) :=
    (Finset.measurable_sum _ (fun i _ => (ht i).const_mul ((m i)^2))).neg.exp
  have hPower : Measurable (fun x : P => ∏ i, (x.2 i)^(ν i-1)) :=
    Finset.measurable_prod _ (fun i _ => (ht i).pow_const _)
  have hExp : Measurable (fun x : P => exp (-(∑ r, ∑ i, x.1 (i,r)*
      ∑ j, ((residualGram C x.2)⁻¹) i j * x.1 (j,r))/4)) :=
    ((Finset.measurable_sum _ (fun r _ => hQ r)).neg.div_const 4).exp
  change Measurable (fun x : P => _)
  unfold routedMassSchwingerWeight routedSchwingerWeight routedInverseWeight
  exact hM.mul ((hPower.mul (hdet.pow_const (2:ℕ)).inv).mul hExp)

private theorem ae_duration_pair_ne {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ t : Fin N → ℝ ∂volume, t i ≠ t j := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hij.symm
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) i
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ _
    let P := {p : ℝ × (Fin N → ℝ) | p.1 = p.2 k}
    have hm : MeasurableSet P := measurableSet_eq_fun measurable_fst ((measurable_pi_apply k).comp measurable_snd)
    have hP : (volume : Measure (ℝ × (Fin N → ℝ))) P = 0 := by
      change (volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ)) P = 0
      rw [Measure.prod_apply_symm hm]
      simp [P]
    have h : ∀ᵐ p : ℝ × (Fin N → ℝ) ∂volume, p.1 ≠ p.2 k := by
      rw [ae_iff]
      simpa only [P,ne_eq,not_not] using hP
    exact he.quasiMeasurePreserving.tendsto_ae.eventually h

private theorem ae_duration_injective (N : ℕ) :
    ∀ᵐ t : Fin N → ℝ ∂volume, Function.Injective t := by
  apply eventually_all.2
  intro i
  apply eventually_all.2
  intro j
  by_cases h : i = j
  · exact ae_of_all _ (fun _ _ => h)
  · exact (ae_duration_pair_ne i j h).mono (fun _ hn he => (hn he).elim)

/-- All time sectors for arbitrary finite independent loop rank.
The joint moment premise is imposed for every ordering of the same
physical rows. Equal proper times have zero Lebesgue measure. -/
theorem massive_all_flag_cost_finite {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν m : Fin N → ℝ)
    {η : ℝ} (hη : 0 < η) (hm : ∀ i, η ≤ (m i)^2)
    (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    (hJoint : ∀ e : Equiv.Perm (Fin N),
      (∫⁻ d, ∏ i, displacementCost (routingFaceExcess (reindexRouting C e) (ν ∘ e) i)
        (projectedDisplacement (reindexRouting C e) (routingShortPrefix i) d) ∂μ) < ⊤) :
    (∫⁻ d, (∫⁻ t in positiveDurations N, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ∂μ) < ⊤ := by
  classical
  let E := Equiv.Perm (Fin N)
  let A := fun e : E => MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e.symm
  have hA (e : E) : MeasurePreserving (A e) volume volume := volume_measurePreserving_piCongrLeft _ _
  have hAeq (e : E) (t : Fin N → ℝ) : A e t = t ∘ e := by
    funext i
    simpa only [A,e.symm_apply_apply,Function.comp_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin N => ℝ) e.symm t (e i)
  let S := fun e : E => (A e) ⁻¹' orderedPositiveDurations N
  have hCover : positiveDurations N ≤ᵐ[(volume : Measure (Fin N → ℝ))] ⋃ e, S e := by
    filter_upwards [ae_duration_injective N] with t ht hpos
    let e := Tuple.sort t
    have hinj : Function.Injective (t ∘ e) := ht.comp e.injective
    exact mem_iUnion.mpr ⟨e,by
      change A e t ∈ orderedPositiveDurations N
      rw [hAeq]
      exact ⟨(Tuple.monotone_sort t).strictMono_of_injective hinj, fun i => hpos (e i)⟩⟩
  let f := fun (e : E) (d : EuclideanSpace ℝ (Fin L × Fin 4)) =>
    ∫⁻ t in orderedPositiveDurations N,
      ENNReal.ofReal (routedMassSchwingerWeight (reindexRouting C e) (ν ∘ e) (m ∘ e) t d)
  have hfm (e : E) : Measurable (f e) :=
    (routedMassSchwingerWeight_measurable (reindexRouting C e) (ν ∘ e) (m ∘ e)).ennreal_ofReal.lintegral_prod_right'
  have hEq (e : E) (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
      (∫⁻ t in S e, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) = f e d := by
    let F := fun t => ENNReal.ofReal (routedMassSchwingerWeight (reindexRouting C e) (ν ∘ e) (m ∘ e) t d)
    have hmap := (hA e).setLIntegral_comp_preimage_emb (A e).measurableEmbedding F (orderedPositiveDurations N)
    refine Eq.trans ?_ hmap
    apply lintegral_congr
    intro t
    change _ = F (A e t)
    unfold F
    rw [hAeq,reindexRouting_mass_weight]
  have hdom (d : EuclideanSpace ℝ (Fin L × Fin 4)) :
      (∫⁻ t in positiveDurations N, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)) ≤ ∑ e, f e d := by
    calc
      _ ≤ ∑' e, ∫⁻ t in S e, ENNReal.ofReal (routedMassSchwingerWeight C ν m t d) :=
        (lintegral_mono' (Measure.restrict_mono_ae hCover) le_rfl).trans (lintegral_iUnion_le _ _)
      _ = _ := by simp_rw [hEq,tsum_fintype]
  apply (lintegral_mono hdom).trans_lt
  rw [lintegral_finset_sum _ (fun e _ => hfm e)]
  exact ENNReal.sum_lt_top.mpr (fun e _ => massive_ordered_flag_cost_finite _ (reindexRouting_injective C hC e)
    _ _ hη (fun i => hm (e i)) μ (hJoint e))

end UV.SewnFlags

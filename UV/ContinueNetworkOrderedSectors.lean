import UV.ContinueNetworkOrdered
import UV.ContinueNetworkSchwingerJoint
import Mathlib.Data.Fin.Tuple.Sort

/-! Almost every positive Schwinger vector belongs to a strictly
ordered sector. Coincident times form a null set, not an extra face. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace UV

def directionalPermutedSector {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  (fun t : Fin n → ℝ => t ∘ σ) ⁻¹' directionalOrderedSet n

theorem directionalPermutedSector_measurable {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (directionalPermutedSector σ) :=
  (directionalOrderedSet_open n).measurableSet.preimage
    (measurable_pi_iff.2 fun i => measurable_pi_apply (σ i))

private theorem directionalSchwinger_pair_ae_distinct {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∀ᵐ t : Fin n → ℝ ∂directionalSchwingerMeasure (Fin n), t i ≠ t j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
      let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
      let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => μ
      letI : NoAtoms μ := by dsimp [μ]; infer_instance
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i
      have he : MeasurePreserving e (directionalSchwingerMeasure (Fin (n + 1))) (μ.prod ν) :=
        measurePreserving_piFinSuccAbove (fun _ => μ) i
      have hsecond : Continuous (fun q : ℝ × (Fin n → ℝ) => q.2 j') :=
        (continuous_apply j').comp continuous_snd
      have hset : MeasurableSet {q : ℝ × (Fin n → ℝ) | q.1 ≠ q.2 j'} :=
        (isOpen_ne_fun continuous_fst hsecond).measurableSet
      have hae : ∀ᵐ q : ℝ × (Fin n → ℝ) ∂μ.prod ν, q.1 ≠ q.2 j' := by
        apply (Measure.ae_prod_iff_ae_ae hset).2
        filter_upwards with s
        exact (Measure.ae_eval_ne (fun _ => μ) j' s).mono fun _ hn => Ne.symm hn
      filter_upwards [he.quasiMeasurePreserving.ae hae] with t ht
      change t i ≠ t (i.succAbove j') at ht
      rwa [hj'] at ht

theorem directionalSchwingerMeasure_ae_ordered {n : ℕ} :
    ∀ᵐ t : Fin n → ℝ ∂directionalSchwingerMeasure (Fin n),
      ∃ σ : Equiv.Perm (Fin n), t ∈ directionalPermutedSector σ := by
  have hbox : ∀ᵐ t : Fin n → ℝ ∂directionalSchwingerMeasure (Fin n),
      ∀ i, t i ∈ Ioo (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.quasiMeasurePreserving_eval _ i).ae
      (ae_restrict_mem measurableSet_Ioo)
  have hae : ∀ᵐ t : Fin n → ℝ ∂directionalSchwingerMeasure (Fin n), ∀ i j, i ≠ j → t i ≠ t j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases he : i = j
    · exact Eventually.of_forall fun _ ht => (ht he).elim
    · exact (directionalSchwinger_pair_ae_distinct he).mono fun _ ht _ => ht
  filter_upwards [hbox, hae] with t ht hpair
  have hinj : Function.Injective t := by
    intro i j hh
    exact by_contra (fun hn => hpair i j hn hh)
  refine ⟨Tuple.sort t, ?_⟩
  apply (directionalOrderedSet_mem_iff (t ∘ Tuple.sort t)).2
  exact ⟨(Tuple.monotone_sort t).strictMono_of_injective (hinj.comp (Tuple.sort t).injective),
    fun i => ht _⟩

private theorem directionalSchwingerMeasure_restrict_sector {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    (directionalSchwingerMeasure (Fin n)).restrict (directionalPermutedSector σ) =
      volume.restrict (directionalPermutedSector σ) := by
  let box : Set (Fin n → ℝ) := univ.pi (fun _ => Ioo (0 : ℝ) 1)
  have hb : directionalSchwingerMeasure (Fin n) = volume.restrict box := by
    unfold directionalSchwingerMeasure box
    rw [volume_pi, Measure.restrict_pi_pi]
  have hsub : directionalPermutedSector σ ⊆ box := by
    intro t ht
    apply Set.mem_pi.2
    intro j _
    have h := ((directionalOrderedSet_mem_iff (t ∘ σ)).1 ht).2 (σ.symm j)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
  rw [hb, Measure.restrict_restrict (directionalPermutedSector_measurable σ),
    Set.inter_eq_left.mpr hsub]

/-- A Schwinger integral is finite precisely when it is finite on each
ordered Lebesgue sector. This applies to nonnegative extended costs. -/
theorem directionalSchwinger_finite_iff_ordered_sectors {n : ℕ}
    (F : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ t, F t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ σ : Equiv.Perm (Fin n), (∫⁻ t in directionalPermutedSector σ, F t) < ⊤ := by
  let μ := directionalSchwingerMeasure (Fin n)
  have hae : ∀ᵐ t ∂μ, t ∈ ⋃ σ : Equiv.Perm (Fin n), directionalPermutedSector σ := by
    filter_upwards [directionalSchwingerMeasure_ae_ordered (n := n)] with t ht
    exact mem_iUnion.2 ht
  have hrestrict : μ.restrict (⋃ σ : Equiv.Perm (Fin n), directionalPermutedSector σ) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  constructor
  · intro h σ
    rw [← directionalSchwingerMeasure_restrict_sector]
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt h
  · intro h
    change (∫⁻ t, F t ∂μ) < ⊤
    rw [← hrestrict]
    refine (lintegral_iUnion_le _ F).trans_lt ?_
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 (fun σ _ => by
      change (∫⁻ t, F t ∂μ.restrict (directionalPermutedSector σ)) < ⊤
      rw [directionalSchwingerMeasure_restrict_sector]
      exact h σ)

/-- Relabelling a sector preserves the exact extended Lebesgue integral.
The inverse permutation returns its coordinates to the original edges. -/
theorem directionalPermutedSector_lintegral_eq {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (F : (Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ t in directionalPermutedSector σ, F t) =
      ∫⁻ t in directionalOrderedSet n, F (t ∘ σ.symm) := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm
  have he : MeasurePreserving e.symm volume volume :=
    measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ
  have happly (t : Fin n → ℝ) : e t = t ∘ σ := by
    funext j
    exact Equiv.piCongrLeft_symm_apply (fun _ : Fin n => ℝ) σ t j
  have hinv (t : Fin n → ℝ) : e.symm t = t ∘ σ.symm := by
    funext j
    have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ t (σ.symm j)
    simpa only [Equiv.apply_symm_apply] using h
  calc
    _ = ∫⁻ t, (directionalPermutedSector σ).indicator F (e.symm t) := by
      rw [← lintegral_indicator (directionalPermutedSector_measurable σ),
        he.lintegral_comp_emb e.symm.measurableEmbedding]
    _ = _ := by
      rw [← lintegral_indicator (directionalOrderedSet_open n).measurableSet]
      apply lintegral_congr
      intro t
      have hm : e.symm t ∈ directionalPermutedSector σ ↔ t ∈ directionalOrderedSet n := by
        change (e.symm t ∘ σ) ∈ directionalOrderedSet n ↔ _
        rw [← happly, e.apply_symm_apply]
      by_cases ht : t ∈ directionalOrderedSet n
      · rw [indicator_of_mem (hm.2 ht), indicator_of_mem ht, hinv]
      · rw [indicator_of_notMem (fun hc => ht (hm.1 hc)), indicator_of_notMem ht]

end UV

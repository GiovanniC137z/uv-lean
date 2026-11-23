import UV.ContinueCompressedModesFockGraphs
import UV.ContinueCompressedModesFockPlacement

/-! Finite spectral sections of the on-shell source. The matrix entry
and the normal amplitude are inserted into the Fock contraction before
applying the cycle estimate. -/

noncomputable section
open UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV.FermionWick
variable {V ν ι : Type*} [NormedAddCommGroup V]

def chargeMatrix (isDensity : Bool) (u : UnitVector Spatial) : DiracMatrix :=
  if isDensity then 1 else diracSlash (NextOpticalRadial.spinCoefficients 0 1 u)

def physicalSpin (m : ℝ) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (band : ι→Bool) (mom : ι→Spatial) (row : ι→Fin 4) (v:ν) (a b:ι) : ℂ :=
  (seaEnergyBand (band a) m (mom a)*chargeMatrix (isDensity v) (u v)*seaEnergyBand (band b) m (mom b)) (row a) (row b)

theorem physicalSpin_bound {m : ℝ} (hm : 0<m) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (band : ι→Bool) (mom : ι→Spatial) (row : ι→Fin 4) (v:ν) (a b:ι) :
    ‖physicalSpin m isDensity u band mom row v a b‖≤1 := by
  have hJ : ‖chargeMatrix (isDensity v) (u v)‖≤1 := by
    unfold chargeMatrix
    split_ifs
    · exact (sea_physical_slot_current_norm (u v)).1.le
    · exact (sea_physical_slot_current_norm _).2.le
  refine (wilson_matrix_entry_le_opnorm _ _ _).trans ?_
  simpa only [neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_smul] using
    sea_spin_slot_bound (mom a) (mom b) _ _ hm (le_refl (0:ℝ)) (chargeMatrix (isDensity v) (u v)) hJ

def physicalSource (diamond : Plane V) (m ℓ : ℝ) (N : ℕ) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (band : ι→Bool) (mom : ι→Spatial) (row : ι→Fin 4) (v:ν) (a b:ι) : ℂ :=
  physicalSpin m isDensity u band mom row v a b * seaRimMark diamond (signedRim diamond (band a))
    (band b != band a) m ℓ N (mom b) (mom a)

private theorem all_product [Fintype ν] (vs : List ν) (nd : vs.Nodup) (covers : ∀i:ν,i∈vs) (F : ν→ℂ) :
    (vs.map F).prod=∏i,F i := by
  classical
  have hp : vs.Perm (Finset.univ : Finset ν).toList := by
    apply (List.perm_ext_iff_of_nodup nd (Finset.nodup_toList _)).mpr
    simp [covers]
  simpa only [Finset.prod_map_toList] using (hp.map F).prod_eq

/-- Every nonzero resolved term of the complete exterior-Fock product is
the displayed signed time contraction times spin vertices and all the
properly oriented, complex normal amplitudes on its derived successor. -/
theorem physical_placement_factor [Fintype ν] [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (diamond : Plane V) (m ℓ : ℝ) (N : ℕ) (isDensity : ν→Bool) (u : ν→UnitVector Spatial)
    (band : ι→Bool) (mom : ι→Spatial) (row : ι→Fin 4) (t : ν→ℝ)
    (vs : List ν) (nd : vs.Nodup) (covers : ∀i:ν,i∈vs) (times : vs.Pairwise (fun i j => t j<t i))
    (p : ℂ × List (Block (Slot ν ι))) (es : List (Edge (Slot ν ι)))
    (hp : p∈placements (physicalSource diamond m ℓ N isDensity u band mom row) vs)
    (he : es∈matchings (slots p.2).length p.2)
    (hne : amplitude (seaCovariance band (fun j => FurtherOptical.energy m (mom j)) t) es≠0) :
    ∃ (a b : ν→ι) (σ : Equiv.Perm ν), p.2=sourceWord vs a b ∧
      (∀i, b (σ i)=a i ∧ (if band (a i) then t i<t (σ i) else t (σ i)<t i) ∧ σ i≠i) ∧
      p.1=(∏i,physicalSpin m isDensity u band mom row i (a i) (a (σ.symm i))) *
        ∏i, seaRimMark diamond (signedRim diamond (band (a i))) (band (a (σ.symm i)) != band (a i)) m ℓ N
          (mom (a (σ.symm i))) (mom (a i)) := by
  obtain ⟨a,b,hl,hw⟩ := placement_source _ vs nd p hp
  have h := he
  rw [hl] at h
  obtain ⟨σ,_,H⟩ := matching_permutation band _ t vs nd covers times a b es _ h hne
  refine ⟨a,b,σ,hl,H,?_⟩
  rw [hw,all_product vs nd covers,←Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hb := (H (σ.symm i)).1
  rw [Equiv.apply_symm_apply] at hb
  simp only [physicalSource,hb]

end UV.FermionWick

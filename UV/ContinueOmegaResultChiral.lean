import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! The physical Weyl slots on a fixed sector plane, with the identical
two spin components in each chirality absorbed into its coefficient
space. A charge-equivariant unitary acts on the internal multiplicity
in the right slot. The canonical mass exchanges the two chiralities. -/

noncomputable section

namespace UV

abbrev OmegaPair (L R : Type*) := WithLp 2 (L × R)

variable {L R : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R]

private theorem omega_pair_ext {A B : Type*} {x y : OmegaPair A B} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  (WithLp.equiv 2 (A × B)).injective (Prod.ext h₁ h₂)

def omegaPairedUnitary (J : L ≃ₗᵢ[ℂ] R) : OmegaPair L L ≃ₗᵢ[ℂ] OmegaPair L R where
  toLinearEquiv := ((WithLp.linearEquiv 2 ℂ (L × L)).trans
    ((LinearEquiv.refl ℂ L).prodCongr J.toLinearEquiv)).trans (WithLp.linearEquiv 2 ℂ (L × R)).symm
  norm_map' x := by
    have h : ‖WithLp.toLp 2 (x.fst,J x.snd)‖^2 = ‖x‖^2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Coordinates are ordered by spin chirality, then by internal grading. -/
def omegaPhysicalInclusion (v : OmegaPair L R) : OmegaPair (OmegaPair L R) (OmegaPair L R) :=
  WithLp.toLp 2 (WithLp.toLp 2 (v.fst,0),WithLp.toLp 2 (0,v.snd))

def omegaTotalGrading (x : OmegaPair (OmegaPair L R) (OmegaPair L R)) :=
  WithLp.toLp 2 (WithLp.toLp 2 (-x.fst.fst,x.fst.snd),WithLp.toLp 2 (x.snd.fst,-x.snd.snd))

private theorem omega_neg_fixed_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v : V) (hv : v = -v) : v = 0 := by
  have h2 : (2:ℂ) • v = 0 := by rw [two_smul]; exact neg_eq_iff_add_eq_zero.mp hv.symm
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem omega_physical_range (J : L ≃ₗᵢ[ℂ] R) (x : OmegaPair (OmegaPair L R) (OmegaPair L R)) :
    (∃ u, omegaPhysicalInclusion (omegaPairedUnitary J u) = x) ↔ omegaTotalGrading x = -x := by
  constructor
  · rintro ⟨u,rfl⟩
    apply omega_pair_ext <;> apply omega_pair_ext <;> simp [omegaTotalGrading,omegaPhysicalInclusion]
  · intro h
    have hr := congrArg (fun z : OmegaPair (OmegaPair L R) (OmegaPair L R) => z.fst.snd) h
    have hl := congrArg (fun z : OmegaPair (OmegaPair L R) (OmegaPair L R) => z.snd.fst) h
    change x.fst.snd = -x.fst.snd at hr
    change x.snd.fst = -x.snd.fst at hl
    refine ⟨(omegaPairedUnitary J).symm (WithLp.toLp 2 (x.fst.fst,x.snd.snd)),?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply omega_pair_ext <;> apply omega_pair_ext
    · rfl
    · exact (omega_neg_fixed_zero x.fst.snd hr).symm
    · exact (omega_neg_fixed_zero x.snd.fst hl).symm
    · rfl

/-- The Hamiltonian mass β⊗Jₒ flips both the spin and internal slots. -/
def omegaAmbientMass (J : L ≃ₗᵢ[ℂ] R) (m : ℝ) (x : OmegaPair (OmegaPair L R) (OmegaPair L R)) :=
  WithLp.toLp 2 (WithLp.toLp 2 ((m:ℂ) • J.symm x.snd.snd,(m:ℂ) • J x.snd.fst),
    WithLp.toLp 2 ((m:ℂ) • J.symm x.fst.snd,(m:ℂ) • J x.fst.fst))

def omegaReferenceMass (m : ℝ) (u : OmegaPair L L) : OmegaPair L L :=
  WithLp.toLp 2 ((m:ℂ) • u.snd,(m:ℂ) • u.fst)

theorem omega_mass_identification (J : L ≃ₗᵢ[ℂ] R) (m : ℝ) (u : OmegaPair L L) :
    omegaAmbientMass J m (omegaPhysicalInclusion (omegaPairedUnitary J u)) =
      omegaPhysicalInclusion (omegaPairedUnitary J (omegaReferenceMass m u)) := by
  apply omega_pair_ext <;> apply omega_pair_ext
  · exact congrArg ((m:ℂ) • ·) (J.symm_apply_apply _)
  · change (m:ℂ) • J 0 = 0
    simp
  · change (m:ℂ) • J.symm 0 = 0
    simp
  · exact (J.map_smul (m:ℂ) u.fst).symm

theorem omega_filled_mass_slot {m : ℝ} (hm : 0 < m) (u : OmegaPair L L) :
    omegaReferenceMass m u = (-m:ℂ) • u ↔ u.snd = -u.fst := by
  constructor
  · intro h
    have hh := congrArg (fun z : OmegaPair L L => z.fst) h
    change (m:ℂ) • u.snd = (-(m:ℂ)) • u.fst at hh
    apply (smul_right_injective L (Complex.ofReal_ne_zero.mpr hm.ne'))
    simpa only [smul_neg,neg_smul] using hh
  · intro h
    apply omega_pair_ext
    · change (m:ℂ) • u.snd = (-(m:ℂ)) • u.fst
      rw [h,smul_neg,neg_smul]
    · change (m:ℂ) • u.fst = (-(m:ℂ)) • u.snd
      rw [h,smul_neg,neg_smul,neg_neg]

/-- Covers charge on both slots, and chirality-preserving spatial symbols
with different left and right Weyl matrices. -/
theorem omega_diagonal_identification (J : L ≃ₗᵢ[ℂ] R) (A B : L → L) (C : R → R)
    (h : ∀ v, C (J v) = J (B v)) (u : OmegaPair L L) :
    WithLp.toLp 2 (A (omegaPairedUnitary J u).fst,C (omegaPairedUnitary J u).snd) =
      omegaPairedUnitary J (WithLp.toLp 2 (A u.fst,B u.snd)) := by
  exact omega_pair_ext rfl (h u.snd)

abbrev OmegaWeyl (L : Type*) := PiLp 2 (fun _ : Fin 2 => L)

def omegaWeylPairing (J : L ≃ₗᵢ[ℂ] R) : OmegaWeyl L ≃ₗᵢ[ℂ] OmegaWeyl R :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => J)

def omegaWeylSymbol (A : Matrix (Fin 2) (Fin 2) ℂ) (z : OmegaWeyl L) : OmegaWeyl L :=
  WithLp.toLp 2 (fun i => ∑ j, A i j • z j)

/-- Actual two-component Weyl symbols with arbitrary internal multiplicity.
This includes the chiral blocks ±σ·p of the spatial Dirac Hamiltonian. -/
theorem omega_weyl_spatial_identification (J : L ≃ₗᵢ[ℂ] R) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (u : OmegaPair (OmegaWeyl L) (OmegaWeyl L)) :
    let P := omegaPairedUnitary (omegaWeylPairing J)
    WithLp.toLp 2 (omegaWeylSymbol A (P u).fst,omegaWeylSymbol B (P u).snd) =
      P (WithLp.toLp 2 (omegaWeylSymbol A u.fst,omegaWeylSymbol B u.snd)) := by
  apply omega_diagonal_identification
  intro z
  ext i
  change (∑ j, B i j • J (z j)) = J (∑ j, B i j • z j)
  simp

/-- Multiplicity-space charge and its endpoint evolution lift independently
through the two Weyl components, without acting on the spin index. -/
theorem omega_weyl_charge_identification (J : L ≃ₗᵢ[ℂ] R) (Q : L → L) (S : R → R)
    (h : ∀ z, S (J z) = J (Q z)) (u : OmegaPair (OmegaWeyl L) (OmegaWeyl L)) :
    let P := omegaPairedUnitary (omegaWeylPairing J)
    let q := fun v : OmegaWeyl L => WithLp.toLp 2 (fun i => Q (v i))
    let s := fun v : OmegaWeyl R => WithLp.toLp 2 (fun i => S (v i))
    WithLp.toLp 2 (q (P u).fst,s (P u).snd) = P (WithLp.toLp 2 (q u.fst,q u.snd)) := by
  dsimp only
  refine omega_diagonal_identification (omegaWeylPairing J) (fun v => WithLp.toLp 2 (fun i => Q (v i)))
    (fun v => WithLp.toLp 2 (fun i => Q (v i))) (fun v => WithLp.toLp 2 (fun i => S (v i))) ?_ u
  intro z
  ext i
  exact h (z i)

/-- Every finite exterior occupation, including the filled wedge, is
intertwined on actual decomposable states and hence all their spans. -/
theorem omega_occupation_transport (J : L ≃ₗᵢ[ℂ] R) (n : ℕ) (u : Fin n → OmegaPair L L) :
    exteriorPower.map n (omegaPairedUnitary J).toLinearEquiv.toLinearMap (exteriorPower.ιMulti ℂ n u) =
      exteriorPower.ιMulti ℂ n (fun i => omegaPairedUnitary J (u i)) := by
  exact exteriorPower.map_apply_ιMulti ..

theorem omega_sourced_determinant {X : Type*} (J : L ≃ₗᵢ[ℂ] R)
    (F : X → Module.End ℂ (OmegaPair L L)) (G : X → Module.End ℂ (OmegaPair L R))
    (h : ∀ x u, G x (omegaPairedUnitary J u) = omegaPairedUnitary J (F x u)) :
    (fun x => (G x).det) = fun x => (F x).det := by
  let e := (omegaPairedUnitary J).toLinearEquiv
  funext x
  have he : G x = e.conj (F x) := by
    ext v
    obtain ⟨u,rfl⟩ := e.surjective v
    change (G x) (e u) = e (F x (e.symm (e u)))
    rw [e.symm_apply_apply]
    exact h x u
  rw [he]
  exact LinearMap.det_conj (F x) e

end UV

import UV.ContinueOmegaResultChiral
import UV.ContinuationSectorPlane
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The optical heat symbol in Weyl coordinates and its transport on each
physical charged block. Carrier or pole vectors are unaffected by this
internal change of basis on the selected plane. -/

noncomputable section
open scoped Matrix InnerProductSpace
namespace UV

variable {L R : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- The symbol σ·k in the spin frame on the three physical spatial axes. -/
def omegaWeylMomentum (k : SectorPlane.Spatial) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(k 2 : ℂ), (k 0 : ℂ)-Complex.I*(k 1 : ℂ);
    (k 0 : ℂ)+Complex.I*(k 1 : ℂ), -(k 2 : ℂ)]

/-- The Wilson-free heat symbol with heat lapse τ (τ=κr in the reference
model). Its two spin chirality blocks carry opposite spatial signs. -/
def omegaHeatWeyl (v τ : ℝ) (k : SectorPlane.Spatial) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((v*Real.exp (-τ*‖k‖^2):ℝ):ℂ) • omegaWeylMomentum k

def omegaReferenceHeatHamiltonian (m v τ : ℝ) (k : SectorPlane.Spatial)
    (x : OmegaPair (OmegaWeyl L) (OmegaWeyl L)) :=
  omegaReferenceMass m x + WithLp.toLp 2
    (omegaWeylSymbol (-omegaHeatWeyl v τ k) x.fst,omegaWeylSymbol (omegaHeatWeyl v τ k) x.snd)

def omegaPhysicalHeatHamiltonian (J : L ≃ₗᵢ[ℂ] R) (m v τ : ℝ) (k : SectorPlane.Spatial)
    (x : OmegaPair (OmegaWeyl L) (OmegaWeyl R)) : OmegaPair (OmegaWeyl L) (OmegaWeyl R) :=
  WithLp.toLp 2 ((m:ℂ) • (omegaWeylPairing J).symm x.snd,(m:ℂ) • omegaWeylPairing J x.fst) +
    WithLp.toLp 2 (omegaWeylSymbol (-omegaHeatWeyl v τ k) x.fst,omegaWeylSymbol (omegaHeatWeyl v τ k) x.snd)

theorem omega_heat_hamiltonian_identification (J : L ≃ₗᵢ[ℂ] R) (m v τ : ℝ)
    (k : SectorPlane.Spatial) (x : OmegaPair (OmegaWeyl L) (OmegaWeyl L)) :
    let P := omegaPairedUnitary (omegaWeylPairing J)
    omegaPhysicalHeatHamiltonian J m v τ k (P x) = P (omegaReferenceHeatHamiltonian m v τ k x) := by
  dsimp only [omegaPhysicalHeatHamiltonian,omegaReferenceHeatHamiltonian]
  rw [map_add,omega_weyl_spatial_identification]
  congr 1
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change (m:ℂ) • (omegaWeylPairing J).symm (omegaWeylPairing J x.snd) = (m:ℂ) • x.snd
    rw [LinearIsometryEquiv.symm_apply_apply]
  · exact ((omegaWeylPairing J).map_smul (m:ℂ) x.fst).symm

omit [InnerProductSpace ℂ L] [InnerProductSpace ℂ R] in
/-- Multiplication by the covariant row factor β⊗1 reverses the total
grading on physical kets. -/
theorem omega_covariant_row_grading (x : OmegaPair L R) :
    let y := omegaPhysicalInclusion x
    let row := WithLp.toLp 2 (y.snd,y.fst)
    omegaTotalGrading row = row := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> apply (WithLp.equiv 2 _).injective <;> apply Prod.ext <;>
    simp [omegaPhysicalInclusion,omegaTotalGrading]

private def omegaWeylOperator (A : Matrix (Fin 2) (Fin 2) ℂ) : OmegaWeyl L →L[ℂ] OmegaWeyl L where
  toFun := omegaWeylSymbol A
  map_add' x y := by ext i; simp [omegaWeylSymbol,smul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp only [omegaWeylSymbol,PiLp.toLp_apply,PiLp.smul_apply,RingHom.id_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  cont := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact continuous_finset_sum _ (fun j _ => (PiLp.continuous_apply 2 _ j).const_smul _)

def omegaReferenceOperator (m v τ : ℝ) (k : SectorPlane.Spatial) :
    OmegaPair (OmegaWeyl L) (OmegaWeyl L) →L[ℂ] OmegaPair (OmegaWeyl L) (OmegaWeyl L) where
  toFun := omegaReferenceHeatHamiltonian m v τ k
  map_add' x y := by
    let A := omegaHeatWeyl v τ k
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · change (m:ℂ) • (x.snd+y.snd) + omegaWeylOperator (-A) (x.fst+y.fst) = _
      rw [map_add]
      simp [omegaReferenceHeatHamiltonian,omegaReferenceMass,smul_add,add_add_add_comm,
        A,omegaWeylOperator]
    · change (m:ℂ) • (x.fst+y.fst) + omegaWeylOperator A (x.snd+y.snd) = _
      rw [map_add]
      simp [omegaReferenceHeatHamiltonian,omegaReferenceMass,smul_add,add_add_add_comm,
        A,omegaWeylOperator]
  map_smul' c x := by
    let A := omegaHeatWeyl v τ k
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · change (m:ℂ) • c • x.snd + omegaWeylOperator (-A) (c • x.fst) = _
      simp [smul_comm (m:ℂ) c,map_smul,omegaReferenceHeatHamiltonian,omegaReferenceMass,
        A,omegaWeylOperator,smul_add]
    · change (m:ℂ) • c • x.fst + omegaWeylOperator A (c • x.snd) = _
      simp [smul_comm (m:ℂ) c,map_smul,omegaReferenceHeatHamiltonian,omegaReferenceMass,
        A,omegaWeylOperator,smul_add]
  cont := by
    let A := omegaHeatWeyl v τ k
    have hf : Continuous (fun x : OmegaPair (OmegaWeyl L) (OmegaWeyl L) => x.fst) := continuous_fst
    have hs : Continuous (fun x : OmegaPair (OmegaWeyl L) (OmegaWeyl L) => x.snd) := continuous_snd
    exact ((WithLp.prod_continuous_toLp 2 _ _).comp ((hs.const_smul (m:ℂ)).prodMk (hf.const_smul (m:ℂ)))).add
      ((WithLp.prod_continuous_toLp 2 _ _).comp (((omegaWeylOperator (-A)).continuous.comp hf).prodMk
        ((omegaWeylOperator A).continuous.comp hs)))

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private def omegaConjugation (P : E ≃ₗᵢ[ℂ] F) : (E →L[ℂ] E) →+* (F →L[ℂ] F) where
  toFun := P.toContinuousLinearEquiv.arrowCongr P.toContinuousLinearEquiv
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by ext u; exact P.apply_symm_apply _
  map_mul' A B := by ext u; exact congrArg (fun z => P (A z)) (P.symm_apply_apply _).symm

/-- Every bounded Euclidean transfer exponential of intertwined generators
is intertwined on the entire Hilbert space, for arbitrary step size. -/
theorem omega_bounded_transfer_exp [CompleteSpace E] [CompleteSpace F] (P : E ≃ₗᵢ[ℂ] F)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (h : ∀ x, B (P x) = P (A x)) (τ : ℝ) (x : E) :
    (NormedSpace.exp ℂ ((-τ:ℂ) • B)) (P x) = P ((NormedSpace.exp ℂ ((-τ:ℂ) • A)) x) := by
  let C := omegaConjugation P
  have hh : C ((-τ:ℂ) • A) = (-τ:ℂ) • B := by
    ext y
    obtain ⟨u,rfl⟩ := P.surjective y
    change P ((-τ:ℂ) • A (P.symm (P u))) = (-τ:ℂ) • B (P u)
    rw [P.symm_apply_apply,P.map_smul,h]
  have hc : Continuous C := (P.toContinuousLinearEquiv.arrowCongr P.toContinuousLinearEquiv).continuous
  rw [←hh,←NormedSpace.map_exp ℂ C hc]
  change P ((NormedSpace.exp ℂ ((-τ:ℂ) • A)) (P.symm (P x))) = _
  rw [P.symm_apply_apply]

/-- Positive diagonal matrix elements and strict positivity of a vacuum
denominator are preserved by the physical identification. -/
theorem omega_transfer_matrix_element (P : E ≃ₗᵢ[ℂ] F) (A : E → E) (B : F → F)
    (h : ∀ x, B (P x) = P (A x)) (u w : E) :
    ⟪P u, B (P w)⟫_ℂ = ⟪u,A w⟫_ℂ := by rw [h,P.inner_map_map]

/-- An actual bounded self-adjoint half-step yields a strictly positive
full diagonal transfer at every nonzero state, by the norm square and
invertibility of its exponential. -/
theorem omega_transfer_diagonal_pos [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) {u : E} (hu : u ≠ 0) :
    0 < (⟪u,(NormedSpace.exp ℂ (A+A)) u⟫_ℂ).re := by
  let B := NormedSpace.exp ℂ A
  have hB : B.adjoint = B := ContinuousLinearMap.isSelfAdjoint_iff'.mp (hA.exp ℂ)
  have hv : B u ≠ 0 := by
    intro hv
    have hI : NormedSpace.exp ℂ (-A) * B = 1 := by
      rw [←NormedSpace.exp_add_of_commute (Commute.refl A).neg_left,neg_add_cancel,NormedSpace.exp_zero]
    apply hu
    calc
      u = (NormedSpace.exp ℂ (-A) * B) u := by rw [hI]; rfl
      _ = 0 := by change (NormedSpace.exp ℂ (-A)) (B u) = 0; rw [hv,map_zero]
  rw [NormedSpace.exp_add_of_commute (Commute.refl A)]
  change 0 < (⟪u,B (B u)⟫_ℂ).re
  have hh : ⟪u,B (B u)⟫_ℂ = ⟪B u,B u⟫_ℂ := by
    calc
      _ = ⟪u,B.adjoint (B u)⟫_ℂ := by rw [hB]
      _ = _ := B.adjoint_inner_right _ _
  rw [hh]
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr hv

/-- A diagonal trace-class preparation over a countable orthonormal
family gives a positive vacuum denominator for a bounded self-adjoint
transfer. Summability follows from the operator norm and summability of
the preparation weights. -/
theorem omega_bounded_diagonal_denominator [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (w : ℕ → ℝ) (hw : Summable w) (hw₀ : ∀ n, 0 ≤ w n)
    (hw₁ : ∃ n, 0 < w n) (u : ℕ → E) (hu : ∀ n, ‖u n‖ = 1) :
    let D := fun n => w n * (⟪u n,(NormedSpace.exp ℂ (A+A)) (u n)⟫_ℂ).re
    Summable D ∧ 0 < ∑' n, D n := by
  let B := NormedSpace.exp ℂ (A+A)
  have hs (n) := omega_transfer_diagonal_pos A hA (show u n ≠ 0 by
    intro he
    have h := hu n
    rw [he,norm_zero] at h
    exact zero_ne_one h)
  have hb (n) : (⟪u n,B (u n)⟫_ℂ).re ≤ ‖B‖ := by
    calc
      _ ≤ ‖⟪u n,B (u n)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖u n‖ * ‖B (u n)‖ := norm_inner_le_norm _ _
      _ ≤ ‖B‖ := by simpa only [hu,one_mul,mul_one] using B.le_opNorm (u n)
  have hd := Summable.of_nonneg_of_le (fun n => mul_nonneg (hw₀ n) (hs n).le)
    (fun n => mul_le_mul_of_nonneg_left (hb n) (hw₀ n)) (hw.mul_right ‖B‖)
  obtain ⟨j,hj⟩ := hw₁
  exact ⟨hd,hd.tsum_pos (fun n => mul_nonneg (hw₀ n) (hs n).le) j (mul_pos hj (hs j))⟩

/-- The spatial heat-symbol Hamiltonian, as a bounded endomorphism of the
physical chiral fibre. Its coordinates are identified below. -/
def omegaPhysicalOperator (J : L ≃ₗᵢ[ℂ] R) (m v τ : ℝ) (k : SectorPlane.Spatial) :=
  omegaConjugation (omegaPairedUnitary (omegaWeylPairing J)) (omegaReferenceOperator m v τ k)

theorem omega_physical_operator_coords (J : L ≃ₗᵢ[ℂ] R) (m v τ : ℝ) (k : SectorPlane.Spatial)
    (y : OmegaPair (OmegaWeyl L) (OmegaWeyl R)) :
    omegaPhysicalOperator J m v τ k y = omegaPhysicalHeatHamiltonian J m v τ k y := by
  let P := omegaPairedUnitary (omegaWeylPairing J)
  obtain ⟨x,rfl⟩ := P.surjective y
  change P (omegaReferenceHeatHamiltonian m v τ k (P.symm (P x))) = _
  rw [P.symm_apply_apply]
  exact (omega_heat_hamiltonian_identification J m v τ k x).symm

private def omegaStep [CompleteSpace E] (t : ℝ) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  NormedSpace.exp ℂ ((-t:ℂ) • A)

/-- The exponential transfer of the specified heat-damped chiral Hamiltonian
at fixed physical momentum and depth, for any real transfer time. -/
theorem omega_heat_transfer [CompleteSpace L] [CompleteSpace R] (J : L ≃ₗᵢ[ℂ] R)
    (m v τ t : ℝ) (k : SectorPlane.Spatial) (x : OmegaPair (OmegaWeyl L) (OmegaWeyl L)) :
    let P := omegaPairedUnitary (omegaWeylPairing J)
    omegaStep t (omegaPhysicalOperator J m v τ k) (P x) =
      P (omegaStep t (omegaReferenceOperator (L := L) m v τ k) x) := by
  apply omega_bounded_transfer_exp
  intro y
  rw [omega_physical_operator_coords]
  exact omega_heat_hamiltonian_identification J m v τ k y

end Transfer
end UV

import UV.ContinueTwoBandPositiveCoulomb
import UV.ContinueCompressedModesFockWick

/-! The filled finite-mode density square. In the exterior-algebra particle
and hole representation the creation/annihilation maps use the two actual
spectral projectors of the Hamiltonian. Momentum transfer keeps the physical
two-component slot unchanged before resolving these projectors. -/

noncomputable section

open Matrix UV.FermionWick
open scoped BigOperators Matrix

namespace UV.SectorPlane

variable {K : Type*} [DecidableEq K]

abbrev DensityOrbital (K : Type*) := Bool × K × Fin 2

/-- Coordinates of the particle created by a physical creation field or
the hole created by a physical annihilation field. -/
def densityExcitation (m : ℝ) (v : K → ℝ) (x y : DensityOrbital K) : ℂ :=
  if x.1 = y.1 ∧ x.2.1 = y.2.1 then
    if x.1 then twoBandProjector true m (v x.2.1) y.2.2 x.2.2
    else twoBandProjector false m (v x.2.1) x.2.2 y.2.2
  else 0

def densityRemoval (m : ℝ) (v : K → ℝ) (x : DensityOrbital K) : Module.Dual ℂ (DensityOrbital K → ℂ) :=
  ∑ i : Fin 2, (if x.1 then twoBandProjector false m (v x.2.1) i x.2.2
    else twoBandProjector true m (v x.2.1) x.2.2 i) • LinearMap.proj (!x.1,x.2.1,i)

theorem density_filled_contraction {m : ℝ} (hm : 0 < m) (v : K → ℝ) (c d : Bool)
    (k l : K) (i j : Fin 2) :
    densityRemoval m v (c,k,i) (densityExcitation m v (d,l,j)) =
    if c ≠ d ∧ k = l then if c then twoBandProjector false m (v k) j i
      else twoBandProjector true m (v k) i j else 0 := by
  by_cases h : k = l
  · subst l
    cases c <;> cases d
    · simp [densityRemoval,densityExcitation,LinearMap.smul_apply]
    · have hP := congrFun (congrFun (twoBand_projector_spectral hm (v k) true).2.1 i) j
      simpa [densityRemoval,densityExcitation,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.mul_apply] using hP
    · have hP := congrFun (congrFun (twoBand_projector_spectral hm (v k) false).2.1 j) i
      simpa [densityRemoval,densityExcitation,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.mul_apply,mul_comm] using hP
    · simp [densityRemoval,densityExcitation,LinearMap.smul_apply]
  · cases c <;> cases d <;> simp [densityRemoval,densityExcitation,LinearMap.smul_apply,h,Ne.symm h]

private theorem two_normal_wick {M A : Type*} [AddCommGroup M] [Module ℂ M] (u : A → M) (d : A → Module.Dual ℂ M)
    (a b c e : A) : vacuum (state u d [.normal a b,.normal c e]) =
      d a (u e)*d b (u c) - d a (u c)*d b (u e) := by
  have hp (x y : A) : vacuum (state u d [.one x,.one y]) = d x (u y) := by
    rw [vacuum_step]
    simp [successors,cuts,edgeWeight,state]
  rw [vacuum_step]
  simp [successors,cuts,edgeWeight,hp]
  ring

/-- The density carrying the orbital from s to t sums its two physical slot
entries. Normal ordering acts on each one-body bilinear only. -/
def twoBandDensityLink (m : ℝ) (v : K → ℝ) (s t : K) :
    Fock (DensityOrbital K → ℂ) →ₗ[ℂ] Fock (DensityOrbital K → ℂ) :=
  ∑ i : Fin 2, blockOp (densityExcitation m v) (densityRemoval m v) (.normal (true,t,i) (false,s,i))

/-- The sum of the subtracted diagonal contractions equals one per
momentum, for both the filled hopping state and the onsite state. -/
theorem twoBand_density_subtraction {m : ℝ} (hm : 0 < m) (v : K → ℝ) (s t : K) :
    (∑ i : Fin 2, densityRemoval m v (true,t,i) (densityExcitation m v (false,s,i))) =
      if t = s then (1:ℂ) else 0 := by
  simp only [density_filled_contraction hm]
  by_cases h : t = s
  · simp [h,Fin.sum_univ_two,twoBandProjector]
    ring
  · simp [h]

/-- The equal-time anticommutator contractions add to the physical
orbital delta, including the diagonal contribution in the density square. -/
theorem twoBand_density_car {m : ℝ} (hm : 0 < m) (v : K → ℝ) (s t : K) (i j : Fin 2) :
    densityRemoval m v (true,t,i) (densityExcitation m v (false,s,j)) +
    densityRemoval m v (false,s,j) (densityExcitation m v (true,t,i)) =
      if t=s ∧ i=j then 1 else 0 := by
  by_cases h : t=s
  · subst s
    fin_cases i <;> fin_cases j <;> simp [density_filled_contraction hm,twoBandProjector] <;> ring
  · simp [density_filled_contraction hm,h,Ne.symm h]

theorem twoBand_density_normal_order {m : ℝ} (hm : 0 < m) (v : K → ℝ) (s t : K) :
    twoBandDensityLink m v s t =
      (∑ i : Fin 2, (field (densityExcitation m v (true,t,i)) (densityRemoval m v (true,t,i))).comp
        (field (densityExcitation m v (false,s,i)) (densityRemoval m v (false,s,i)))) -
      (if t=s then (1:ℂ) else 0) • LinearMap.id := by
  unfold twoBandDensityLink
  rw [← twoBand_density_subtraction hm v s t]
  simp only [blockOp,Finset.sum_sub_distrib,Finset.sum_smul]

/-- Two oppositely oriented density operators on the filled vacuum.
Nonmatching momentum pairs give zero; matching pairs give exactly W. -/
theorem twoBand_density_link_square {m : ℝ} (hm : 0 < m) (v : K → ℝ) (s t s' t' : K) :
    vacuum (twoBandDensityLink m v t s (twoBandDensityLink m v s' t' 1)) =
      if s = s' ∧ t = t' then (twoBandTransitionWeight m (v s) (v t) : ℂ) else 0 := by
  change vacuum.toLinearMap _ = _
  simp only [twoBandDensityLink,LinearMap.sum_apply,map_sum]
  have h (i j : Fin 2) : vacuum.toLinearMap
      (blockOp (densityExcitation m v) (densityRemoval m v) (.normal (true,s,i) (false,t,i))
      (blockOp (densityExcitation m v) (densityRemoval m v) (.normal (true,t',j) (false,s',j)) 1)) =
    (if s=s' then twoBandProjector false m (v s) j i else 0) *
    (if t=t' then twoBandProjector true m (v t) i j else 0) := by
    have hW := two_normal_wick (densityExcitation m v) (densityRemoval m v)
      (true,s,i) (false,t,i) (true,t',j) (false,s',j)
    simpa [state,density_filled_contraction hm] using hW
  simp only [h]
  by_cases hs : s=s'
  · subst s'
    by_cases ht : t=t'
    · subst t'
      simp only [ite_true,and_self]
      rw [Finset.sum_comm]
      exact twoBand_transition_projector_trace hm _ _
    · simp [ht]
  · simp [hs]

variable {J : Type*} [Fintype J]

def twoBandDensityTransfer (m : ℝ) (v : K → ℝ) (s t : J → K) :
    Fock (DensityOrbital K → ℂ) →ₗ[ℂ] Fock (DensityOrbital K → ℂ) :=
  ∑ j, twoBandDensityLink m v (s j) (t j)

/-- The square includes self-contractions. Each labelled Fourier transfer
sends one allowed source momentum to one target. Injectivity of the source
list avoids counting a transfer more than once. -/
theorem twoBand_filled_density_square {m : ℝ} (hm : 0 < m) (v : K → ℝ)
    (s t : J → K) (hs : Function.Injective s) :
    vacuum (twoBandDensityTransfer m v t s (twoBandDensityTransfer m v s t 1)) =
      ∑ j, (twoBandTransitionWeight m (v (s j)) (v (t j)) : ℂ) := by
  classical
  change vacuum.toLinearMap _ = _
  simp only [twoBandDensityTransfer,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (twoBand_density_link_square hm v _ _ _ _).trans (if_pos ⟨rfl,rfl⟩)
  · intro j _ hji
    exact (twoBand_density_link_square hm v _ _ _ _).trans (if_neg (fun h => hji (hs h.1)))
  · simp

/-- Apply the finite occupation calculation to the original Gaussian
Hamiltonian and the harmonic Coulomb multiplier at external momentum p.
Every allowed pair in the chosen mode cutoff has transfer exactly p. -/
theorem twoBand_filled_coulomb_mode {m : ℝ} (hm : 0 < m) (g σ q a : ℝ)
    (momentum : K → Spatial) (s t : J → K) (hs : Function.Injective s) (p : Spatial)
    (hshift : ∀ j, momentum (t j) = momentum (s j) + p) :
    let v := fun k => twoBandSpatialHop g σ (momentum k)
    (twoBandCoulombMultiplier q a p / 2 : ℂ) *
      vacuum (twoBandDensityTransfer m v t s (twoBandDensityTransfer m v s t 1)) =
      (∑ j, ((twoBandCoulombSpatialDensity m g σ q a (p,momentum (s j)) / 2 : ℝ) : ℂ)) := by
  intro v
  rw [twoBand_filled_density_square hm v s t hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [v,hshift,twoBandCoulombSpatialDensity,twoBandSpatialWeight,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

end UV.SectorPlane

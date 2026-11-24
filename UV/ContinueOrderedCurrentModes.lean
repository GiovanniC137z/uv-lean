import UV.ContinueOrderedCurrentVariation

/-! Fourier modes of the complete ordered Wilson phase. Real and imaginary
test components are honest real connection variations. The common harmonic
factor is attached once to each mark. -/

noncomputable section

open MeasureTheory Finset
open scoped ContinuousMap RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

inductive MarkPolarization where
  | density
  | spatial (u : UnitVector Spatial)

structure ElectricMark where
  frequency : ℝ
  momentum : Spatial
  polarization : MarkPolarization

def chartWave (ω : ℝ) (p : Spatial) (tx : ℝ × Spatial) : ℂ :=
  Complex.exp (Complex.I*(ω:ℂ)*(tx.1:ℂ))*spatialWave p tx.2

private theorem chart_wave_continuous (ω : ℝ) (p : Spatial) : Continuous (chartWave ω p) := by
  unfold chartWave spatialWave
  fun_prop

private theorem hop_chart (P : OrderedTwoBandPath) (j : ℕ) (ω : ℝ) (p : Spatial) :
    P.hopWave j ω p = ∫ r in (0:ℝ)..1, chartWave ω p (P.time (j+1), P.position j+r • P.step j) := by
  unfold hopWave wilsonEdgeWave
  apply intervalIntegral.integral_congr
  intro r _
  simp only [thinPlaneWave,inner_add_right,real_inner_smul_right,carrier_inner,mul_zero,zero_add,
    chartWave,spatialWave,←Complex.exp_add,Complex.ofReal_add,Complex.ofReal_mul]
  congr 1
  ring

def ElectricMark.current (m : ElectricMark) (P : OrderedTwoBandPath) : ℂ :=
  match m.polarization with
  | .density => P.density m.frequency m.momentum
  | .spatial u => P.spatialCurrent m.frequency m.momentum u.val

/-- Real-linear projection of a single smeared Fourier probe. For the two
components take respectively reCLM and imCLM. -/
def ElectricMark.connection (m : ElectricMark) (a : ℝ) (L : ℂ →L[ℝ] ℝ) : RealConnection :=
  let w := Real.exp (-a*‖m.momentum‖)
  let phase : C(ℝ × Spatial,ℝ) := ⟨fun z => L (w • chartWave m.frequency m.momentum z),
    L.continuous.comp ((chart_wave_continuous _ _).const_smul _)⟩
  match m.polarization with
  | .density => (phase,0)
  | .spatial u => (0,⟨fun z => phase z • innerSL ℝ u.val,phase.continuous.smul continuous_const⟩)

theorem mode_connection_integral (P : OrderedTwoBandPath) (m : ElectricMark) (a : ℝ) (L : ℂ →L[ℝ] ℝ) :
    P.connectionIntegral (m.connection a L) = L (Real.exp (-a*‖m.momentum‖) • m.current P) := by
  rcases m with ⟨ω,p,m⟩
  let w := Real.exp (-a*‖p‖)
  cases m with
  | density =>
    change (∑ j ∈ range P.hops, ((∫ t in P.time j..P.time (j+1), L (w • chartWave ω p (t,P.position j))) +
      ∫ _r in (0:ℝ)..1, (0:ℝ))) = L (w • P.density ω p)
    simp only [intervalIntegral.integral_zero,add_zero,density,smul_sum,map_sum]
    apply sum_congr rfl
    intro j _
    have hc : Continuous (fun t : ℝ => w • chartWave ω p (t,P.position j)) :=
      ((chart_wave_continuous _ _).comp (continuous_id.prodMk continuous_const)).const_smul _
    rw [L.intervalIntegral_comp_comm (hc.intervalIntegrable _ _),intervalIntegral.integral_smul]
    congr 2
    simp only [chartWave,intervalIntegral.integral_mul_const,pulse,mul_comm]
  | spatial u =>
    change (∑ j ∈ range P.hops, ((∫ _t in P.time j..P.time (j+1), (0:ℝ)) +
      ∫ r in (0:ℝ)..1, L (w • chartWave ω p (P.time (j+1),P.position j+r • P.step j)) *
        ⟪u.val,P.step j⟫)) = L (w • P.spatialCurrent ω p u.val)
    simp only [intervalIntegral.integral_zero,zero_add,spatialCurrent,smul_sum,map_sum]
    apply sum_congr rfl
    intro j _
    let W := fun r : ℝ => chartWave ω p (P.time (j+1),P.position j+r • P.step j)
    have hc : Continuous (fun r => w • W r) := ((chart_wave_continuous _ _).comp
      (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const)))).const_smul _
    change (∫ r in (0:ℝ)..1, L (w • W r)*⟪u.val,P.step j⟫) = _
    rw [intervalIntegral.integral_mul_const,L.intervalIntegral_comp_comm (hc.intervalIntegrable _ _),
      intervalIntegral.integral_smul,P.hop_chart]
    change L (w • ∫ r in (0:ℝ)..1, W r) * ⟪u.val,P.step j⟫ =
      L (w • ((⟪u.val,P.step j⟫:ℂ) * ∫ r in (0:ℝ)..1, W r))
    rw [←Complex.real_smul,smul_comm,map_smul,smul_eq_mul,mul_comm]
    simp only [map_smul,smul_eq_mul]

def ElectricMark.tests (m : ElectricMark) (a : ℝ) : RealConnection × RealConnection :=
  (m.connection a Complex.reCLM,m.connection a Complex.imCLM)

/-- Every labelled Fourier variation acts on the very same complete phase.
No injectivity condition is imposed on marks, momenta, polarizations, times,
or occupied links. The oriented Green inverse fixes the common −i q factor. -/
theorem complete_fourier_variations (P : OrderedTwoBandPath) (q a : ℝ) (marks : List ElectricMark) (B : RealConnection) :
    mixedVariation (marks.map (fun m => m.tests a)) (P.connectionPhase q) B =
      (marks.map (fun m => -Complex.I*(q:ℂ)*(Real.exp (-a*‖m.momentum‖):ℂ)*m.current P)).prod *
        P.connectionPhase q B := by
  rw [phase_mixed_variation,List.map_map]
  congr 2
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply,ElectricMark.tests,P.mode_connection_integral,Complex.reCLM_apply,Complex.imCLM_apply]
  rw [mul_comm Complex.I,Complex.re_add_im,Complex.real_smul]
  ring

theorem actual_fourier_coefficient (P : OrderedTwoBandPath) (q a : ℝ) (marks : List ElectricMark) :
    mixedVariation (marks.map (fun m => m.tests a)) (P.connectionPhase q) 0 =
      (-Complex.I*(q:ℂ))^marks.length *
        (marks.map (fun m => (Real.exp (-a*‖m.momentum‖):ℂ)*m.current P)).prod := by
  rw [P.complete_fourier_variations]
  have hb : P.connectionPhase q 0 = 1 := by simp [connectionPhase,connectionIntegral]
  rw [hb,mul_one]
  induction marks with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]; ring

end UV.SectorPlane.OrderedTwoBandPath

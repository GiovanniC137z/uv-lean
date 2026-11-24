import UV.ContinueOrderedCurrentPlane
import UV.ContinueWilsonLinkMarks

/-! Ordinary real external connections on the time-local ordered two-band path.
Every variation is taken on the complete Wilson phase before choosing a
Fourier mode. Directed durations appear with their original sign. -/

noncomputable section

open MeasureTheory Finset
open scoped ContinuousMap RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

/-- Scalar and spatial covector fields on the same real sector-plane chart. -/
abbrev RealConnection := C(ℝ × Spatial,ℝ) × C(ℝ × Spatial,Spatial →L[ℝ] ℝ)

def connectionIntegral (P : OrderedTwoBandPath) (B : RealConnection) : ℝ :=
  ∑ j ∈ range P.hops, ((∫ t in P.time j..P.time (j+1), B.1 (t,P.position j)) +
    ∫ r in (0:ℝ)..1, B.2 (P.time (j+1),P.position j+r • P.step j) (P.step j))

/-- With the onsite convention ∂τ+i q A, forward parallel transport has
exp(−i q integral). The same coupling and orientation are used on both legs. -/
def connectionPhase (P : OrderedTwoBandPath) (q : ℝ) (B : RealConnection) : ℂ :=
  Complex.exp (-Complex.I*(q:ℂ)*(P.connectionIntegral B:ℂ))

theorem connection_integral_variation (P : OrderedTwoBandPath) (B A : RealConnection) (r : ℝ) :
    P.connectionIntegral (B+r • A) = P.connectionIntegral B+r*P.connectionIntegral A := by
  unfold connectionIntegral
  rw [Finset.mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hv (C : RealConnection) : Continuous (fun t : ℝ => C.1 (t,P.position j)) := C.1.continuous.comp
    (continuous_id.prodMk continuous_const)
  have hh (C : RealConnection) : Continuous (fun s : ℝ => C.2 (P.time (j+1),P.position j+s • P.step j) (P.step j)) :=
    (C.2.continuous.comp (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const)))).clm_apply continuous_const
  have he (t : ℝ) : (B+r • A).1 (t,P.position j) = B.1 (t,P.position j)+r*A.1 (t,P.position j) := rfl
  have ha (s : ℝ) : (B+r • A).2 (P.time (j+1),P.position j+s • P.step j) (P.step j) =
      B.2 (P.time (j+1),P.position j+s • P.step j) (P.step j)+r*A.2 (P.time (j+1),P.position j+s • P.step j) (P.step j) := rfl
  simp only [he,ha,intervalIntegral.integral_add ((hv B).intervalIntegrable _ _) (((hv A).intervalIntegrable _ _).const_mul r),
    intervalIntegral.integral_add ((hh B).intervalIntegrable _ _) (((hh A).intervalIntegrable _ _).const_mul r),
    intervalIntegral.integral_const_mul]
  ring

theorem connection_phase_derivative (P : OrderedTwoBandPath) (q : ℝ) (B A : RealConnection) :
    HasDerivAt (fun r : ℝ => P.connectionPhase q (B+r • A))
      ((-Complex.I*(q:ℂ)*(P.connectionIntegral A:ℂ))*P.connectionPhase q B) 0 := by
  let k := -Complex.I*(q:ℂ)*(P.connectionIntegral A:ℂ)
  let c := -Complex.I*(q:ℂ)*(P.connectionIntegral B:ℂ)
  have he (r : ℝ) : P.connectionPhase q (B+r • A) = Complex.exp (c+(r:ℂ)*k) := by
    rw [connectionPhase,P.connection_integral_variation]
    push_cast
    congr 1
    dsimp [c,k]
    ring
  rw [funext he]
  simpa only [id_eq,k,c,connectionPhase,one_mul,Complex.ofReal_zero,zero_mul,add_zero,mul_comm]
    using ((((hasDerivAt_id (0:ℂ)).mul_const k).const_add c).cexp).comp_ofReal

/-- Complex-linear extension of iterated real derivatives. Each pair is the
cosine and sine probe for one complex mode. Repeated directions are allowed. -/
def mixedVariation : List (RealConnection × RealConnection) → (RealConnection → ℂ) → RealConnection → ℂ
  | [],F,B => F B
  | (A,D)::L,F,B => deriv (fun r : ℝ => mixedVariation L F (B+r • A)) 0 +
      Complex.I*deriv (fun r : ℝ => mixedVariation L F (B+r • D)) 0

theorem phase_mixed_variation (P : OrderedTwoBandPath) (q : ℝ) (L : List (RealConnection × RealConnection))
    (B : RealConnection) :
    mixedVariation L (P.connectionPhase q) B =
      (L.map (fun A => -Complex.I*(q:ℂ)*((P.connectionIntegral A.1:ℂ)+Complex.I*(P.connectionIntegral A.2:ℂ)))).prod *
        P.connectionPhase q B := by
  induction L generalizing B with
  | nil => simp [mixedVariation]
  | cons Ls L ih =>
    rcases Ls with ⟨A,D⟩
    let C := (L.map (fun A => -Complex.I*(q:ℂ)*((P.connectionIntegral A.1:ℂ)+Complex.I*(P.connectionIntegral A.2:ℂ)))).prod
    simp only [mixedVariation,ih,List.map_cons,List.prod_cons]
    rw [((P.connection_phase_derivative q B A).const_mul C).deriv,
      ((P.connection_phase_derivative q B D).const_mul C).deriv]
    dsimp only [C]
    ring

end UV.SectorPlane.OrderedTwoBandPath

module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §11.2.1–11.2.2 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "mₛ(" F ", " S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    0 0 _ (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm F).ker.subtype) ω
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "localTheta(" F ", " S ", " a ", " ω ", " f ")" =>
  modulationWeight (mₛ(F, S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)

local notation "qₛ(" F ", " S ", " ω ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)).mkQ

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
The absolute local closure presupposes that each weighted class in the §7.3.2 level is in
the ambient Sobolev space, for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalAbsolutePWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalAbsolutePW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
Take F = ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0.
Let H be the inverse Fourier transform of a nonzero nonnegative even smooth bump
supported where 1/8 < |ξ| < 1/4. The test is (H(u) - H(2u)) times the 2-adic
integer indicator. Both zero moments vanish. At the class of (t, 1), the local
theta series telescopes to 2 H(t), up to the positive norm-one Haar mass.
Since H(0) > 0, its squared integral against dt/t diverges at zero. -/
theorem Printed.sLocalAbsolutePWSobolev_memLp_false :
    ¬ Printed.sLocalAbsolutePWSobolev_memLp := by sorry

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
The invariant local closure presupposes Sobolev membership of the weighted
classes in the §7.3.2 level for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalInvariantPWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalInvariantPW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
Use ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0. The test
(H(u) - H(2u)) times the 2-adic integer indicator from the absolute-level
counterexample also lies in the invariant region. Its Fourier support satisfies
|ξ∞| ≤ 1 and |ξ₂|₂ ≤ 1. The local theta is proportional to 2 H(t) and is outside L²(dt/t). -/
theorem Printed.sLocalInvariantPWSobolev_memLp_false :
    ¬ Printed.sLocalInvariantPWSobolev_memLp := by sorry

local notation "GeoIsotype(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    (-(0 : ℝ)) 0 _ (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "cutoffConv(" F ", " hs ", " ω ", " a ", " hρ ", " φ ")" =>
  ((GeoIsotype(F, hs, ω)).orthogonalProjectionOnto.comp
    ((geometricTruncatedConvolution (F := F) a (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
      (GeoIsotype(F, hs, ω)).subtypeL))
local notation "aboveOne(" F ", " φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽(F)).val ⊆ {g | 1 ≤ ((m𝔽(F) g).val : ℝ)})
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
For every fixed cutoff, the trace-norm limit of absolute condensation is asserted
to be the uncompressed cutoff geometric convolution.
Deviation: Use the global absolute projector specified by the declared codomain
in (11.2.1.3), with the Fourier box bound X = Λ. -/
def Printed.absolutePWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- A trace-norm limit of right products determines the operator value on a pointwise limit. -/
private theorem absolutePWCondensation_traceNorm_tendsto_false_apply
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (P : ℝ → H →L[ℂ] H) (u v : H)
    (hP : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v))
    (hT : Tendsto (fun Λ ↦ traceNorm
      ((⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ : nuclearEndomorphisms H) - T))
      atTop (𝓝 0)) : T.val v = T.val u := by
  by_cases hu : u = 0
  · subst u
    simp only [map_zero] at hP ⊢
    rw [tendsto_nhds_unique hP tendsto_const_nhds, map_zero]
  let f := innerSL ℂ u
  let A := f.smulRight u
  let D (Λ : ℝ) : nuclearEndomorphisms H :=
    ⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ - T
  have hbound (Λ : ℝ) : ‖f‖ * ‖T.val (P Λ u) - T.val u‖ ≤ ‖A‖ * traceNorm (D Λ) := by
    have hmul : (D Λ).val * A = f.smulRight (T.val (P Λ u) - T.val u) := by
      ext1 x
      simp [D, A, smul_sub]
    rw [← traceNorm_smulRight f (T.val (P Λ u) - T.val u)]
    have hprod : (⟨(D Λ).val * A, mul_mem_nuclearEndomorphisms_right A (D Λ)⟩ :
        nuclearEndomorphisms H) =
        ⟨f.smulRight (T.val (P Λ u) - T.val u), smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext hmul
    rw [← hprod]
    exact traceNorm_mul_right_le A (D Λ)
  have hLeft : Tendsto (fun Λ ↦ ‖f‖ * ‖T.val (P Λ u) - T.val u‖) atTop
      (𝓝 (‖f‖ * ‖T.val v - T.val u‖)) :=
    tendsto_const_nhds.mul (((T.val.continuous.tendsto v).comp hP).sub tendsto_const_nhds).norm
  have hRight : Tendsto (fun Λ ↦ ‖A‖ * traceNorm (D Λ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hT
  have hle := le_of_tendsto_of_tendsto' hLeft hRight hbound
  have hf : 0 < ‖f‖ := by simpa only [f, innerSL_apply_norm, norm_pos_iff] using hu
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hle hf) (norm_nonneg _)))

open scoped nonZeroDivisors in
/-- The rational integers have trivial Picard group. -/
private theorem rational_empty_picTrivial :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The restriction of the trivial rational character is unramified everywhere. -/
private theorem rational_one_unramifiedOutside_empty :
    NormOneCharacterUnramifiedOutside
      ((1 : PontryaginDual C𝔽(ℚ)).comp
        (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ := by
  refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- A fixed-cutoff geometric convolution is nonzero on a vector orthogonal to theta
in the trivial rational isotype. Use a critical-line ordinate γ and the log-norm
vector `exp(-iγx)/(1+x²)`. Pair its translates with the theta vector from
`(3u² - 2πu⁴) exp(-πu²)` and the finite integer indicators. The pairing is analytic,
and the Cauchy kernel has a nonvanishing Fourier multiplier, so it is nonzero at some
positive translation. A bump near that point and a large cutoff preserve the
nonzero geometric output. -/
private theorem rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero :
    let hs : (0 : ℝ) ≤ 2 := by norm_num
    let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
    letI : CompleteSpace ↥(GeoIsotype(ℚ, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    ∃ (φ : BruhatCompactSupport C𝔽(ℚ)), aboveOne(ℚ, φ) ∧
      ∃ (R ε : ℝ) (ρ : C𝔽(ℚ) → ℝ) (hρ : IsModulatedCutoff (m𝔽(ℚ)) R ε ρ)
          (u : GeoIsotype(ℚ, hs, ω)),
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u = 0 ∧
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricTruncatedConvolution (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u ≠ 0 := by sorry

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
On the trivial rational component with no finite places, a = 1/2 and s = 2, let γ be
the first positive ordinate of a critical-line zeta zero. The vector
v(x) = exp(-iγx)/(1+x²) is orthogonal to theta by the Mellin zero.
Use the nonzero half-weighted theta profile G of
(3u² - 2πu⁴) exp(-πu²) with integer indicators at finite places.
The inner products of the translates v(x-t) with G cannot vanish for all t > 0.
Up to a phase they convolve G(x) exp(iγx)(1+x²) with 1/(1+x²).
That convolution is real analytic and its Fourier multiplier is nowhere zero.
A nonnegative test bump near a positive t with nonzero inner product still pairs
nontrivially, and a sufficiently large fixed symmetric cutoff preserves a nonzero
part of its geometric projection. Every right PW projection kills v. -/
theorem Printed.absolutePWCondensation_traceNorm_tendsto_false :
    ¬ Printed.absolutePWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := absolutePWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := absolutePWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For every fixed cutoff, the trace-norm limit of invariant condensation is asserted
to be the uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For ℚ with no finite places, the trivial character, a = 1/2 and s = 2, the product
region is the same interval as the absolute box. The zeta-zero vector, positive test bump and
fixed symmetric cutoff of the absolute counterexample also refute this limit. -/
theorem Printed.invariantPWCondensation_traceNorm_tendsto_false :
    ¬ Printed.invariantPWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := invariantPWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := invariantPWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution.
Deviation: Interpret the absolute projector by the PW codomain of (11.2.1.3)
and take the box parameter X = Λ, as for the operator assertion. -/
def Printed.absolutePWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
In the rational trivial isotype take S = {∞}, a = 1/2 and s = 2.
In Fourier H¹ let E project onto the complement of the functions vanishing
at the critical-line ordinates. A smooth frequency multiplier supported
around a single ordinate γ and equal to one there induces a rank-one
idempotent in the quotient. A fixed large symmetric cutoff leaves its trace
near one. Translate the inverse transform far to the right, compensate by
the phase at γ and cut the Schwartz tails to obtain a positive-time test.
The spatially cut translated operator on E tends to zero in trace norm,
while its quotient action retains the rank-one trace. The two fixed-cutoff
traces thus differ. See the rational calculation in the PR review. -/
theorem Printed.absolutePWCondensation_trace_tendsto_false :
    ¬ Printed.absolutePWCondensation_trace_tendsto := by sorry

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
For the rational data of the absolute scalar counterexample the
only place in S is real. The product region equals the box at every level,
so both scalar limits have the same discrepancy. -/
theorem Printed.invariantPWCondensation_trace_tendsto_false :
    ¬ Printed.invariantPWCondensation_trace_tendsto := by sorry

local notation "theta0(" F ", " hs ")" => globalThetaSobolev F 0 (le_rfl (a := (0 : ℝ))) hs
local notation "Sₚ(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Paragraph before (11.2.2.1), p. 489.
The raw principal-value range defining the prime quotient is asserted to be
closed in the zero-line theta isotype.
Deviation: Use the equivalent ambient isotypic model at zero twist. -/
def Printed.primeOrbitalSobolevDenominator_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (p : HeightOneSpectrum (𝓞 ℚ)),
    (∀ v ∈ Sₚ(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
      IsClosed {x : Wω(F, hs, ω) | ∃ y : theta0(F, hs), y.val ∈ Wω(F, hs, ω) ∧
        (globalThetaSobolevPrincipalValue F (Sₚ(F, p)) 0 hs y).val = x.val}

/-- Paper: Paragraph before (11.2.2.1), p. 489.
Take ℚ, the trivial character, p = 2 and s = 2. In log norm the principal
value is the difference with a shift by log 2, up to translation sign.
It is injective on weighted L² because every periodic vector there vanishes.
For any nonzero smooth bump ψ supported in (1, 2), the normalized difference
of ψ(x/R) tends to zero as R grows. The map is therefore not bounded below,
so its range is not closed. -/
theorem Printed.primeOrbitalSobolevDenominator_closed_false :
    ¬ Printed.primeOrbitalSobolevDenominator_closed := by sorry

end RiemannMasullo

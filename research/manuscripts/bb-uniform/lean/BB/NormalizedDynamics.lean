import BB.BaselineNormalized
import BB.ScalarStep

set_option autoImplicit false

noncomputable section
namespace BB.Baseline
open scoped BigOperators Topology
open Filter

variable {ι : Type*} [Fintype ι]

/-- The finite probability simplex of spectral energies. -/
abbrev Simplex (ι : Type*) [Fintype ι] :=
  {w : ι → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- Current normalized energies followed by preceding normalized energies. -/
abbrev NormalizedState (ι : Type*) [Fintype ι] := Simplex ι × Simplex ι

def simplexPhi (lam : ι → ℝ) (z : Simplex ι) (i : ι) : ℝ :=
  (1-lam i/tau lam z.val)^2

def radialSquare (lam : ι → ℝ) (chi : NormalizedState ι) : ℝ :=
  ∑ i, simplexPhi lam chi.2 i*chi.1.val i

def radialMultiplier (lam : ι → ℝ) (chi : NormalizedState ι) : ℝ :=
  Real.sqrt (radialSquare lam chi)

theorem simplexPhi_nonneg (lam : ι → ℝ) (z : Simplex ι) (i : ι) :
    0 ≤ simplexPhi lam z i := sq_nonneg _

theorem radialSquare_nonneg (lam : ι → ℝ) (chi : NormalizedState ι) :
    0 ≤ radialSquare lam chi :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (simplexPhi_nonneg lam chi.2 i) (chi.1.property.1 i))

theorem radialMultiplier_nonneg (lam : ι → ℝ) (chi : NormalizedState ι) :
    0 ≤ radialMultiplier lam chi := Real.sqrt_nonneg _

theorem radialMultiplier_sq (lam : ι → ℝ) (chi : NormalizedState ι) :
    radialMultiplier lam chi^2 = radialSquare lam chi :=
  Real.sq_sqrt (radialSquare_nonneg lam chi)

theorem radialMultiplier_pos_iff (lam : ι → ℝ) (chi : NormalizedState ι) :
    0 < radialMultiplier lam chi ↔ 0 < radialSquare lam chi := Real.sqrt_pos

def normalizedNext (lam : ι → ℝ) (chi : NormalizedState ι)
    (hchi : 0 < radialSquare lam chi) : Simplex ι :=
  ⟨fun i => simplexPhi lam chi.2 i*chi.1.val i/radialSquare lam chi,
    (fun i => div_nonneg
      (mul_nonneg (simplexPhi_nonneg lam chi.2 i) (chi.1.property.1 i)) hchi.le),by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hchi)⟩

/-- The manuscript's normalized map on regular states. It is totalized by the
identity at terminal states; terminal multipliers are independent of this choice. -/
def normalizedMap (lam : ι → ℝ) (chi : NormalizedState ι) : NormalizedState ι := by
  classical
  exact if hchi : 0 < radialSquare lam chi then (normalizedNext lam chi hchi,chi.1) else chi

theorem normalizedMap_regular (lam : ι → ℝ) {chi : NormalizedState ι}
    (hchi : 0 < radialSquare lam chi) :
    normalizedMap lam chi = (normalizedNext lam chi hchi,chi.1) := by
  simp only [normalizedMap,dif_pos hchi]

theorem normalizedMap_terminal (lam : ι → ℝ) {chi : NormalizedState ι}
    (hchi : radialMultiplier lam chi = 0) : normalizedMap lam chi = chi := by
  have hzero : radialSquare lam chi = 0 := by
    rw [← radialMultiplier_sq,hchi,zero_pow (by decide : 2 ≠ 0)]
  simp [normalizedMap,hzero]

theorem simplex_tau_bounds {lam : ι → ℝ} {a b : ℝ}
    (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b) (z : Simplex ι) :
    a ≤ tau lam z.val ∧ tau lam z.val ≤ b :=
  tau_bounds z.property.1 z.property.2 hlo hhi

theorem simplex_tau_pos {lam : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ i, a ≤ lam i) (z : Simplex ι) : 0 < tau lam z.val := by
  have hlow : a ≤ tau lam z.val := by
    calc
      a = ∑ i, a*z.val i := by rw [← Finset.mul_sum,z.property.2,mul_one]
      _ ≤ tau lam z.val := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (hlo i) (z.property.1 i))
  exact ha.trans_le hlow

/-- A uniform, explicit radial growth bound on the entire simplex product. -/
theorem radialMultiplier_bound {lam : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b)
    (chi : NormalizedState ι) : radialMultiplier lam chi ≤ b/a-1 := by
  have hM : 0 ≤ b/a-1 := by have hh := (one_le_div ha).mpr hab; linarith only [hh]
  have ht := simplex_tau_bounds hlo hhi chi.2
  have htpos : 0 < tau lam chi.2.val := ha.trans_le ht.1
  have hphi (i : ι) : simplexPhi lam chi.2 i ≤ (b/a-1)^2 := by
    have hm := BB.Spectral.multiplier_bound ha hab (hlo i) (hhi i)
      (one_div_le_one_div_of_le htpos ht.2) (one_div_le_one_div_of_le ha ht.1)
    have hrewrite : (1/tau lam chi.2.val)*lam i = lam i/tau lam chi.2.val := by ring
    rw [hrewrite] at hm
    unfold simplexPhi
    nlinarith only [hm,abs_nonneg (1-lam i/tau lam chi.2.val),
      sq_abs (1-lam i/tau lam chi.2.val),hM]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hM,?_⟩
  calc
    radialSquare lam chi ≤ ∑ i, (b/a-1)^2*chi.1.val i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hphi i) (chi.1.property.1 i))
    _ = (b/a-1)^2 := by rw [← Finset.mul_sum,chi.1.property.2,mul_one]

theorem tau_continuous (lam : ι → ℝ) : Continuous (tau lam) :=
  continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem simplexPhi_continuous {lam : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ i, a ≤ lam i) (i : ι) : Continuous (fun z : Simplex ι => simplexPhi lam z i) := by
  exact (continuous_const.sub (continuous_const.div
    ((tau_continuous lam).comp continuous_subtype_val)
    (fun z => ne_of_gt (simplex_tau_pos ha hlo z)))).pow 2

theorem radialSquare_continuous {lam : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ i, a ≤ lam i) : Continuous (radialSquare lam) := by
  apply continuous_finset_sum _
  intro i _
  exact ((simplexPhi_continuous ha hlo i).comp continuous_snd).mul
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))

theorem radialMultiplier_continuous {lam : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ i, a ≤ lam i) : Continuous (radialMultiplier lam) :=
  (radialSquare_continuous ha hlo).sqrt

/-- The actual normalized map is continuous wherever its multiplier is positive. -/
theorem normalizedMap_continuousAt {lam : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ i, a ≤ lam i) (chi : NormalizedState ι)
    (hchi : 0 < radialMultiplier lam chi) : ContinuousAt (normalizedMap lam) chi := by
  have hpos := (radialMultiplier_pos_iff lam chi).mp hchi
  have hnear : ∀ᶠ y in 𝓝 chi, 0 < radialSquare lam y :=
    (radialSquare_continuous ha hlo).continuousAt.tendsto.eventually (lt_mem_nhds hpos)
  have hraw : ContinuousAt
      (fun y : NormalizedState ι => fun i => simplexPhi lam y.2 i*y.1.val i/radialSquare lam y) chi := by
    apply continuousAt_pi.mpr
    intro i
    exact (((simplexPhi_continuous ha hlo i).comp continuous_snd).continuousAt.mul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).continuousAt).div
        (radialSquare_continuous ha hlo).continuousAt (ne_of_gt hpos)
  have hfstval : ContinuousAt (fun y => (normalizedMap lam y).1.val) chi := by
    apply hraw.congr
    filter_upwards [hnear] with y hy
    rw [normalizedMap_regular lam hy]
    rfl
  have hfst : ContinuousAt (fun y => (normalizedMap lam y).1) chi :=
    tendsto_subtype_rng.mpr hfstval
  have hsnd : ContinuousAt (fun y => (normalizedMap lam y).2) chi := by
    apply continuous_fst.continuousAt.congr
    filter_upwards [hnear] with y hy
    rw [normalizedMap_regular lam hy]
  exact hfst.prod hsnd

/-- Lemma 6.1 instantiated with the concrete simplex BB1 dynamics, including
all terminal states. -/
theorem normalized_terminalMultiplier_continuous {lam : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b)
    (n : ℕ) : Continuous (terminalMultiplier (radialMultiplier lam) (normalizedMap lam) n) := by
  have hM : 0 ≤ b/a-1 := by have hh := (one_le_div ha).mpr hab; linarith only [hh]
  exact terminalMultiplier_continuous hM (radialMultiplier_nonneg lam)
    (radialMultiplier_bound ha hab hlo hhi) (radialMultiplier_continuous ha hlo)
    (normalizedMap_continuousAt ha hlo) n

end BB.Baseline

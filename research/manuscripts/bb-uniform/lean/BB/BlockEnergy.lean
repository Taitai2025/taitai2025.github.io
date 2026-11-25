import BB.BlockNorms

set_option autoImplicit false

namespace BB.Blocks
open BB.Spectral
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- A common positive scaling of all block energies does not change the quotient. -/
theorem blockAlpha_scale (lam : ι → ℝ) (q : ∀ i, E i → ℝ) (u : ∀ i, E i)
    {m : ℝ} (hm : m ≠ 0) :
    blockAlpha lam (fun i x => q i x / m) u = blockAlpha lam q u := by
  unfold blockAlpha
  have hn : (∑ i, q i (u i)/m) = (∑ i, q i (u i))/m := by rw [Finset.sum_div]
  have hd : (∑ i, lam i*(q i (u i)/m)) = (∑ i, lam i*q i (u i))/m := by
    simp only [mul_div_assoc,Finset.sum_div]
  rw [hn,hd]
  exact div_div_div_cancel_right _ hm

/-- The block iteration also ignores that common scaling. -/
theorem blockMap_scale (lam : ι → ℝ) (q : ∀ i, E i → ℝ) (z : BState E)
    {m : ℝ} (hm : m ≠ 0) :
    blockMap lam (fun i x => q i x / m) z = blockMap lam q z := by
  unfold blockMap
  rw [blockAlpha_scale lam q z.1 hm]

/-- Coercivity bounds normalized by their lower spectral scale. -/
theorem normalized_energy_bounds {q : ∀ i, E i → ℝ} {m χ : ℝ} (hm : 0 < m)
    (hlo : ∀ i x, m*‖x‖^2 ≤ q i x) (hhi : ∀ i x, q i x ≤ (χ*m)*‖x‖^2) :
    (∀ i x, ‖x‖^2 ≤ q i x/m) ∧ (∀ i x, q i x/m ≤ χ*‖x‖^2) := by
  constructor
  · intro i x
    apply (le_div_iff hm).mpr
    simpa only [mul_comm] using hlo i x
  · intro i x
    apply (div_le_iff hm).mpr
    nlinarith only [hhi i x]

/-- Cone invariance for actual block updates. -/
theorem blockMap_cone {lam : ι → ℝ} {q : ∀ i, E i → ℝ} {a b χ M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 1 ≤ χ)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hqlo : ∀ i x, ‖x‖^2 ≤ q i x) (hqhi : ∀ i x, q i x ≤ χ*‖x‖^2)
    {z : BState E} (hz : blockCone M z) : blockCone M (blockMap lam q z) := by
  apply (stateRadius_cone M _).mp
  rw [stateRadius_blockMap hqlo hqhi]
  apply (absState_cone (M := M) _).mpr
  apply stateMap_cone ha hab (fun i => (effectiveWeight_bounds hχ hqlo hqhi z.1 i).1) hlama hlamb hM
  exact (stateRadius_cone M z).mpr hz

/-- A common certificate also covers unnormalized energies with a variable positive scale. -/
noncomputable def liftScaledCertificate {Ω : Type*} {lam : ι → ℝ} {χ M c : ℝ}
    (q : Ω → ∀ i, E i → ℝ) (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω) (hχ : 1 ≤ χ)
    (hqlo : ∀ ω i x, m ω*‖x‖^2 ≤ q ω i x)
    (hqhi : ∀ ω i x, q ω i x ≤ (χ*m ω)*‖x‖^2)
    (v : BB.Gluing.Certificate (fun w : ScalarWeights ι χ => stateMap lam w.val) {z | Cone M z} c)
    (habs : ∀ z, v.value (absState z) = v.value z) :
    BB.Gluing.Certificate (fun ω => blockMap lam (q ω)) {z | blockCone M z} c := by
  let q' : Ω → ∀ i, E i → ℝ := fun ω i x => q ω i x / m ω
  have hlo : ∀ ω i x, ‖x‖^2 ≤ q' ω i x :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).1
  have hhi : ∀ ω i x, q' ω i x ≤ χ*‖x‖^2 :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).2
  have hmaps : (fun ω => blockMap lam (q' ω)) = (fun ω => blockMap lam (q ω)) := by
    funext ω z
    exact blockMap_scale lam (q ω) z (ne_of_gt (hm ω))
  rw [← hmaps]
  exact liftCertificate q' hχ hlo hhi v habs

end BB.Blocks

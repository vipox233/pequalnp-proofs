import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_099_aux

abbrev F := ZMod 2

lemma choose_mod_two (N k : ℕ) :
    Nat.choose N k % 2 = (Nat.choose (N % 2) (k % 2) * Nat.choose (N / 2) (k / 2)) % 2 := by
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k =>
      have hk : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by omega
      rcases hk with h0 | h1
      · rw [Nat.choose_zero_succ, h0]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (k + 1) / 2 ≠ 0)
        rw [hm]
        simp
      · rw [Nat.choose_zero_succ, h1]
        simp
  | succ N ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ, Nat.add_mod, ih k, ih (k + 1)]
      have hN : N % 2 = 0 ∨ N % 2 = 1 := by omega
      have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hN with hN0 | hN1 <;> rcases hk with hk0 | hk1
      · have h1 : (N + 1) % 2 = 1 := by omega
        have h2 : (k + 1) % 2 = 1 := by omega
        have h3 : (N + 1) / 2 = N / 2 := by omega
        have h4 : (k + 1) / 2 = k / 2 := by omega
        rw [hN0, hk0, h1, h2, h3, h4]
        simp
      · have h1 : (N + 1) % 2 = 1 := by omega
        have h2 : (k + 1) % 2 = 0 := by omega
        have h3 : (N + 1) / 2 = N / 2 := by omega
        have h4 : (k + 1) / 2 = k / 2 + 1 := by omega
        rw [hN0, hk1, h1, h2, h3, h4]
        simp
      · have h1 : (N + 1) % 2 = 0 := by omega
        have h2 : (k + 1) % 2 = 1 := by omega
        have h3 : (N + 1) / 2 = N / 2 + 1 := by omega
        have h4 : (k + 1) / 2 = k / 2 := by omega
        rw [hN1, hk0, h1, h2, h3, h4]
        simp only [Nat.choose_zero_right, Nat.choose_self, one_mul, Nat.choose_zero_succ, zero_mul,
          Nat.zero_mod]
        omega
      · have h1 : (N + 1) % 2 = 0 := by omega
        have h2 : (k + 1) % 2 = 0 := by omega
        have h3 : (N + 1) / 2 = N / 2 + 1 := by omega
        have h4 : (k + 1) / 2 = k / 2 + 1 := by omega
        rw [hN1, hk1, h1, h2, h3, h4]
        simp only [Nat.choose_self, Nat.choose_zero_right, one_mul, Nat.choose_succ_succ]
        rw [← Nat.add_mod]

lemma choose_pow_two_mod_two (N j : ℕ) :
    Nat.choose N (2 ^ j) % 2 = (N / 2 ^ j) % 2 := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', choose_mod_two]
    have hm : (2 * 2 ^ j) % 2 = 0 := by omega
    have hd : (2 * 2 ^ j) / 2 = 2 ^ j := by omega
    rw [hm, hd, Nat.choose_zero_right, one_mul, ih (N / 2), Nat.div_div_eq_div_mul]

lemma testBit_eq_choose_testBit_zero (N j : ℕ) :
    N.testBit j = (Nat.choose N (2 ^ j)).testBit 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [choose_pow_two_mod_two]

def scopeDef (n w : ℕ) (hn : 0 < n) (i : Fin n) : Finset (Fin n) :=
  (Finset.range (min n (w + 1))).image (fun t => ⟨(i.val + t) % n, Nat.mod_lt _ hn⟩)

lemma card_scopeDef (n w : ℕ) (hn : 0 < n) (i : Fin n) :
    (scopeDef n w hn i).card = min n (w + 1) := by
  dsimp only [scopeDef]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro t1 ht1 t2 ht2 heq
  rw [Finset.mem_coe, Finset.mem_range] at ht1 ht2
  have hv : (i.val + t1) % n = (i.val + t2) % n := congrArg Fin.val heq
  have hle : min n (w + 1) ≤ n := min_le_left n (w + 1)
  by_cases h1 : i.val + t1 < n <;> by_cases h2 : i.val + t2 < n
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv; omega
  · have hmod2 : (i.val + t2) % n = i.val + t2 - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt h1, hmod2] at hv; omega
  · have hmod1 : (i.val + t1) % n = i.val + t1 - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod1, Nat.mod_eq_of_lt h2] at hv; omega
  · have hmod1 : (i.val + t1) % n = i.val + t1 - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hmod2 : (i.val + t2) % n = i.val + t2 - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod1, hmod2] at hv; omega

def fullDef (n w : ℕ) (hn : 0 < n) : Finset (Fin n × Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n × Finset (Fin n))).filter (fun p => p.2 ⊆ scopeDef n w hn p.1)

lemma card_fullDef (n w : ℕ) (hn : 0 < n) :
    (fullDef n w hn).card = n * 2 ^ min n (w + 1) := by
  have hbi : fullDef n w hn =
      (Finset.univ : Finset (Fin n)).biUnion (fun i =>
        (scopeDef n w hn i).powerset.image (fun S => (i, S))) := by
    ext ⟨i, S⟩
    simp [fullDef, Finset.mem_powerset]
  rw [hbi, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
      Finset.card_powerset, card_scopeDef, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  · intro i1 _ i2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨_, _, rfl⟩ := hp1
    obtain ⟨_, _, heq⟩ := hp2
    exact hne (Prod.mk.inj heq).1.symm

def patDef (n w : ℕ) (hn : 0 < n) (x : Finset (Fin n)) : Finset (Fin n × Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin n => (i, x ∩ scopeDef n w hn i))

lemma card_patDef (n w : ℕ) (hn : 0 < n) (x : Finset (Fin n)) :
    (patDef n w hn x).card = n := by
  dsimp only [patDef]
  rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_univ,
    Fintype.card_fin]

lemma patDef_subset_fullDef (n w : ℕ) (hn : 0 < n) (x : Finset (Fin n)) :
    patDef n w hn x ⊆ fullDef n w hn := by
  intro p hp
  rw [patDef, Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  rw [fullDef, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Finset.inter_subset_right⟩

lemma patDef_subset_iff (n w : ℕ) (hn : 0 < n) (x : Finset (Fin n))
    (T : Finset (Fin n × Finset (Fin n))) :
    patDef n w hn x ⊆ T ↔ ∀ i : Fin n, (i, x ∩ scopeDef n w hn i) ∈ T := by
  simp [patDef, Finset.subset_iff]

def totalDef (n w : ℕ) (hn : 0 < n) (T : Finset (Fin n × Finset (Fin n))) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => ∀ i : Fin n, (i, x ∩ scopeDef n w hn i) ∈ T)).card

def coeffDef (n w : ℕ) (hn : 0 < n) (bit : ℕ) (M : Finset (Fin n × Finset (Fin n))) : Bool :=
  ((M.powerset.filter (fun T => (totalDef n w hn T).testBit bit)).card).testBit 0

lemma coeffDef_eq_biUnion_parity (n w : ℕ) (hn : 0 < n) (j : ℕ)
    (M : Finset (Fin n × Finset (Fin n))) :
    coeffDef n w hn j M =
      (((Finset.univ : Finset (Finset (Fin n))).powersetCard (2 ^ j)).filter
        (fun A => A.biUnion (patDef n w hn) = M)).card.testBit 0 := by
  rw [coeffDef, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  congr 1
  have h1 : (M.powerset.filter (fun T => (totalDef n w hn T).testBit j)).card % 2 =
      (∑ T ∈ M.powerset, Nat.choose (totalDef n w hn T) (2 ^ j)) % 2 := by
    rw [Finset.card_filter, Finset.sum_nat_mod]
    symm
    rw [Finset.sum_nat_mod]
    symm
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    rw [testBit_eq_choose_testBit_zero, Nat.testBit_eq_decide_div_mod_eq]
    simp only [Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
    have hmod : Nat.choose (totalDef n w hn T) (2 ^ j) % 2 = 0 ∨
        Nat.choose (totalDef n w hn T) (2 ^ j) % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl
  rw [h1]
  have h2 : ∀ T : Finset (Fin n × Finset (Fin n)),
      Nat.choose (totalDef n w hn T) (2 ^ j) =
        (((Finset.univ : Finset (Finset (Fin n))).powersetCard (2 ^ j)).filter
          (fun A => A.biUnion (patDef n w hn) ⊆ T)).card := by
    intro T
    rw [totalDef, ← Finset.card_powersetCard]
    congr 1
    ext A
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and,
      Finset.biUnion_subset, patDef_subset_iff]
    constructor
    · rintro ⟨hA, hc⟩
      exact ⟨hc, fun x hx => (Finset.mem_filter.mp (hA hx)).2⟩
    · rintro ⟨hc, hA⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hA x hx⟩, hc⟩
  simp_rw [h2, Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_nat_mod]
  have h3 : ∀ A ∈ (Finset.univ : Finset (Finset (Fin n))).powersetCard (2 ^ j),
      (∑ T ∈ M.powerset, if A.biUnion (patDef n w hn) ⊆ T then 1 else 0) % 2 =
        if A.biUnion (patDef n w hn) = M then 1 else 0 := by
    intro A _
    let U := A.biUnion (patDef n w hn)
    change (∑ T ∈ M.powerset, if U ⊆ T then 1 else 0) % 2 = if U = M then 1 else 0
    rw [← Finset.card_filter]
    by_cases hUM : U ⊆ M
    · have hcard : (M.powerset.filter (fun T => U ⊆ T)).card = 2 ^ (M \ U).card := by
        rw [← Finset.card_powerset]
        refine Finset.card_bij (fun T _ => T \ U) ?_ ?_ ?_
        · intro T hT
          rw [Finset.mem_filter, Finset.mem_powerset] at hT
          rw [Finset.mem_powerset]
          exact Finset.sdiff_subset_sdiff hT.1 (Finset.Subset.refl U)
        · intro T1 hT1 T2 hT2 heq
          rw [Finset.mem_filter] at hT1 hT2
          rw [← Finset.sdiff_union_of_subset hT1.2, ← Finset.sdiff_union_of_subset hT2.2, heq]
        · intro S hS
          rw [Finset.mem_powerset] at hS
          refine ⟨S ∪ U, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.union_subset (hS.trans Finset.sdiff_subset) hUM, Finset.subset_union_right⟩
          · have hdisj : Disjoint S U := Disjoint.mono_left hS Finset.sdiff_disjoint
            exact Finset.union_sdiff_cancel_right hdisj
      rw [hcard]
      by_cases heq : U = M
      · subst heq
        simp
      · have hpos : 0 < (M \ U).card := by
          rw [Finset.card_pos, Finset.sdiff_nonempty]
          intro hMU
          exact heq (Finset.Subset.antisymm hUM hMU)
        have heven : 2 ^ (M \ U).card % 2 = 0 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
          rw [hk, pow_succ]
          omega
        simp [heq, heven]
    · have hne : U ≠ M := fun heq => hUM (heq ▸ Finset.Subset.refl M)
      have hempty : M.powerset.filter (fun T => U ⊆ T) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT hUT
        rw [Finset.mem_powerset] at hT
        exact hUM (hUT.trans hT)
      simp [hne, hempty]
  rw [Finset.sum_congr rfl h3, ← Finset.card_filter]

lemma prepend_cyclic_window_inj {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m)
    (g : (Fin j → F) →ₗ[F] (Fin m → F))
    (hg : ∀ start : Fin m, Function.Injective (fun s => fun t : Fin j =>
      g s ⟨(start.val + t.val) % m, Nat.mod_lt _ (by omega)⟩)) :
    ∃ f : (Fin j → F) →ₗ[F] (Fin (m + j) → F),
      ∀ start : Fin (m + j), Function.Injective (fun s => fun t : Fin j =>
        f s ⟨(start.val + t.val) % (m + j), Nat.mod_lt _ (by omega)⟩) := by
  let f : (Fin j → F) →ₗ[F] (Fin (m + j) → F) :=
    { toFun := fun s i => if hi : i.val < j then g s ⟨i.val, by omega⟩ else g s ⟨i.val - j, by omega⟩
      map_add' := fun s1 s2 => by
        ext i
        dsimp only [Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c s => by
        ext i
        dsimp only [Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  refine ⟨f, fun start => ?_⟩
  let L : (Fin j → F) →ₗ[F] (Fin j → F) :=
    { toFun := fun s t => f s ⟨(start.val + t.val) % (m + j), Nat.mod_lt _ (by omega)⟩
      map_add' := fun s1 s2 => by ext t; simp
      map_smul' := fun c s => by ext t; simp }
  change Function.Injective L
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hzero : ∀ t : Fin j, f s ⟨(start.val + t.val) % (m + j), Nat.mod_lt _ (by omega)⟩ = 0 :=
    fun t => congrFun hs t
  by_cases hst : start.val < j
  · have hg0 : (fun t : Fin j => g s ⟨(0 + t.val) % m, Nat.mod_lt _ (by omega)⟩) = 0 := by
      ext t
      have hmod : (0 + t.val) % m = t.val := by rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
      simp only [Pi.zero_apply]
      by_cases ht : start.val ≤ t.val
      · have h1 := hzero ⟨t.val - start.val, by omega⟩
        have hidx : (start.val + (t.val - start.val)) % (m + j) = t.val := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [dif_pos (by omega)] at h1
        convert h1 using 2
        apply Fin.ext
        dsimp only
        rw [hidx]
        omega
      · have h1 := hzero ⟨t.val + j - start.val, by omega⟩
        have hidx : (start.val + (t.val + j - start.val)) % (m + j) = t.val + j := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [dif_neg (by omega)] at h1
        convert h1 using 2
        apply Fin.ext
        dsimp only
        rw [hidx]
        omega
    have h00 : (fun t : Fin j => g 0 ⟨(0 + t.val) % m, Nat.mod_lt _ (by omega)⟩) = 0 := by
      ext t; simp
    exact hg ⟨0, by omega⟩ (hg0.trans h00.symm)
  · have hgm : (fun t : Fin j => g s ⟨((start.val - j) + t.val) % m, Nat.mod_lt _ (by omega)⟩) = 0 := by
      ext t
      simp only [Pi.zero_apply]
      have h1 := hzero t
      dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk] at h1
      by_cases hwrap : start.val + t.val < m + j
      · have hidx : (start.val + t.val) % (m + j) = start.val + t.val := Nat.mod_eq_of_lt hwrap
        rw [dif_neg (by omega)] at h1
        convert h1 using 2
        apply Fin.ext
        dsimp only
        have hltm : start.val - j + t.val < m := by omega
        rw [Nat.mod_eq_of_lt hltm, hidx]
        omega
      · have hidx : (start.val + t.val) % (m + j) = start.val + t.val - (m + j) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [dif_pos (by omega)] at h1
        convert h1 using 2
        apply Fin.ext
        dsimp only
        have hmodm : (start.val - j + t.val) % m = start.val + t.val - (m + j) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hmodm, hidx]
    have h00 : (fun t : Fin j => g 0 ⟨((start.val - j) + t.val) % m, Nat.mod_lt _ (by omega)⟩) = 0 := by
      ext t; simp
    exact hg ⟨start.val - j, by omega⟩ (hgm.trans h00.symm)

lemma exists_cyclic_window_inj :
    ∀ n j : ℕ, (hj : 1 ≤ j) → (hjn : j ≤ n) →
      ∃ f : (Fin j → F) →ₗ[F] (Fin n → F),
        ∀ start : Fin n, Function.Injective (fun s => fun t : Fin j =>
          f s ⟨(start.val + t.val) % n, Nat.mod_lt _ (by omega)⟩) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj hjn
    by_cases heq : j = n
    · subst heq
      refine ⟨LinearMap.id, fun start => ?_⟩
      intro s1 s2 h12
      ext t
      have hidx : (start.val + (t.val + j - start.val) % j) % j = t.val := by
        have h1 : (start.val + (t.val + j - start.val)) % j = t.val := by
          have : start.val + (t.val + j - start.val) = t.val + j := by
            have := start.isLt; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
        calc (start.val + (t.val + j - start.val) % j) % j
            = (start.val % j + (t.val + j - start.val) % j % j) % j := Nat.add_mod _ _ _
          _ = (start.val % j + (t.val + j - start.val) % j) % j := by rw [Nat.mod_mod]
          _ = (start.val + (t.val + j - start.val)) % j := (Nat.add_mod _ _ _).symm
          _ = t.val := h1
      have hval := congrFun h12 ⟨(t.val + j - start.val) % j, Nat.mod_lt _ (by omega)⟩
      change s1 ⟨(start.val + (t.val + j - start.val) % j) % j, Nat.mod_lt _ (by omega)⟩ =
        s2 ⟨(start.val + (t.val + j - start.val) % j) % j, Nat.mod_lt _ (by omega)⟩ at hval
      have hfin : (⟨(start.val + (t.val + j - start.val) % j) % j, Nat.mod_lt _ (by omega)⟩ : Fin j) = t :=
        Fin.ext hidx
      rw [hfin] at hval
      exact hval
    · by_cases h2j : 2 * j ≤ n
      · obtain ⟨g, hg⟩ := ih (n - j) (by omega) j hj (by omega)
        obtain ⟨f0, hf0⟩ := prepend_cyclic_window_inj hj (by omega : j ≤ n - j) g hg
        have hnm : n - j + j = n := by omega
        let f : (Fin j → F) →ₗ[F] (Fin n → F) :=
          { toFun := fun s i => f0 s ⟨i.val, by omega⟩
            map_add' := fun s1 s2 => by ext i; simp
            map_smul' := fun c s => by ext i; simp }
        refine ⟨f, fun start s1 s2 h12 => ?_⟩
        apply hf0 ⟨start.val, by omega⟩
        ext t
        have ht := congrFun h12 t
        dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk] at ht ⊢
        have hidx : (⟨(start.val + t.val) % (n - j + j), Nat.mod_lt _ (by omega)⟩ : Fin (n - j + j)) =
            ⟨(start.val + t.val) % n, by rw [hnm]; exact Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp only; rw [hnm])
        rw [hidx]
        exact ht
      · let r := n - j
        have hr1 : 1 ≤ r := by omega
        have hrj : r ≤ j := by omega
        have hjn_lt : j < n := by omega
        obtain ⟨g, hg⟩ := ih j hjn_lt r hr1 hrj
        obtain ⟨wmap, hwmap⟩ := prepend_cyclic_window_inj hr1 hrj g hg
        have hjr : j + r = n := by omega
        let w : (Fin r → F) →ₗ[F] (Fin n → F) :=
          { toFun := fun s i => wmap s ⟨i.val, by omega⟩
            map_add' := fun s1 s2 => by ext i; simp
            map_smul' := fun c s => by ext i; simp }
        have hw : ∀ start : Fin n, Function.Injective (fun s => fun u : Fin r =>
            w s ⟨(start.val + u.val) % n, Nat.mod_lt _ (by omega)⟩) := by
          intro start s1 s2 h12
          apply hwmap ⟨start.val, by omega⟩
          ext u
          have hu := congrFun h12 u
          dsimp only [w, LinearMap.coe_mk, AddHom.coe_mk] at hu ⊢
          have hidx : (⟨(start.val + u.val) % (j + r), Nat.mod_lt _ (by omega)⟩ : Fin (j + r)) =
              ⟨(start.val + u.val) % n, by rw [hjr]; exact Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp only; rw [hjr])
          rw [hidx]
          exact hu
        let W : (Fin n → F) →ₗ[F] (Fin r → F) :=
          { toFun := fun y p => ∑ i : Fin n, y i * w (Pi.single p 1) i
            map_add' := fun y1 y2 => by
              ext p; simp [add_mul, Finset.sum_add_distrib]
            map_smul' := fun c y => by
              ext p; simp [Finset.mul_sum, mul_assoc] }
        have hW_dot : ∀ (y : Fin n → F) (s : Fin r → F),
            (∑ i : Fin n, y i * w s i) = ∑ p : Fin r, s p * W y p := by
          intro y s
          have hs : s = ∑ p : Fin r, s p • Pi.single p (1 : F) := by
            ext q; simp [Finset.sum_apply, Pi.single_apply]
          conv_lhs => rw [hs]
          simp_rw [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p _
          dsimp only [W, LinearMap.coe_mk, AddHom.coe_mk]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hW_surj : Function.Surjective W := by
          let emb : (Fin r → F) →ₗ[F] (Fin n → F) :=
            { toFun := fun z i => if hi : i.val < r then z ⟨i.val, hi⟩ else 0
              map_add' := fun z1 z2 => by ext i; dsimp only [Pi.add_apply]; split_ifs <;> simp
              map_smul' := fun c z => by ext i; dsimp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
          let comp := W.comp emb
          have hcomp_inj : Function.Injective comp := by
            rw [injective_iff_map_eq_zero]
            intro z hz
            let win0 : (Fin r → F) →ₗ[F] (Fin r → F) :=
              { toFun := fun s u => w s ⟨(0 + u.val) % n, Nat.mod_lt _ (by omega)⟩
                map_add' := fun s1 s2 => by ext u; simp
                map_smul' := fun c s => by ext u; simp }
            have hwin0_surj : Function.Surjective win0 :=
              (LinearMap.injective_iff_surjective (f := win0)).mp (hw ⟨0, by omega⟩)
            ext u0
            obtain ⟨s, hs⟩ := hwin0_surj (Pi.single u0 1)
            have hsum0 : ∑ i : Fin n, emb z i * w s i = 0 := by
              rw [hW_dot]
              have hWz : W (emb z) = 0 := hz
              simp [hWz]
            have hsum_eq : ∑ i : Fin n, emb z i * w s i = z u0 := by
              have hsub : ∑ i : Fin n, emb z i * w s i =
                  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < r), emb z i * w s i := by
                symm
                apply Finset.sum_subset (Finset.filter_subset _ _)
                intro i _ hi
                rw [Finset.mem_filter] at hi
                have hnot : ¬ i.val < r := fun h' => hi ⟨Finset.mem_univ i, h'⟩
                simp [emb, hnot]
              rw [hsub, Finset.sum_eq_single ⟨u0.val, by omega⟩]
              · have hws : w s ⟨u0.val, by omega⟩ = 1 := by
                  have := congrFun hs u0
                  dsimp only [win0, LinearMap.coe_mk, AddHom.coe_mk] at this
                  have hmod : (0 + u0.val) % n = u0.val := by rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
                  have hfin : (⟨(0 + u0.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = ⟨u0.val, by omega⟩ := Fin.ext hmod
                  rw [hfin, Pi.single_apply, if_pos rfl] at this
                  exact this
                simp [emb, u0.isLt, hws]
              · intro i hi hne
                rw [Finset.mem_filter] at hi
                have hws : w s i = 0 := by
                  have := congrFun hs ⟨i.val, hi.2⟩
                  dsimp only [win0, LinearMap.coe_mk, AddHom.coe_mk] at this
                  have hmod : (0 + i.val) % n = i.val := by rw [zero_add]; exact Nat.mod_eq_of_lt i.isLt
                  have hne' : (⟨i.val, hi.2⟩ : Fin r) ≠ u0 := fun heq => hne (Fin.ext (by simpa using congrArg Fin.val heq))
                  have hfin : (⟨(0 + i.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = i := Fin.ext hmod
                  rw [hfin, Pi.single_apply, if_neg hne'] at this
                  exact this
                simp [hws]
              · intro hnot
                exfalso
                apply hnot
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u0.isLt⟩
            rw [hsum_eq] at hsum0
            exact hsum0
          have hcomp_surj : Function.Surjective comp :=
            (LinearMap.injective_iff_surjective (f := comp)).mp hcomp_inj
          intro b
          obtain ⟨z, hz⟩ := hcomp_surj b
          exact ⟨emb z, hz⟩
        have hker_dim : Module.finrank F (LinearMap.ker W) = j := by
          have hrk := LinearMap.finrank_range_add_finrank_ker W
          rw [LinearMap.range_eq_top.mpr hW_surj, finrank_top, Module.finrank_fin_fun,
            Module.finrank_fin_fun] at hrk
          omega
        let e : (Fin j → F) ≃ₗ[F] LinearMap.ker W :=
          LinearEquiv.ofFinrankEq (Fin j → F) (LinearMap.ker W) (by rw [Module.finrank_fin_fun, hker_dim])
        let f : (Fin j → F) →ₗ[F] (Fin n → F) := (LinearMap.ker W).subtype.comp e.toLinearMap
        refine ⟨f, fun start => ?_⟩
        let L : (Fin j → F) →ₗ[F] (Fin j → F) :=
          { toFun := fun s t => f s ⟨(start.val + t.val) % n, Nat.mod_lt _ (by omega)⟩
            map_add' := fun s1 s2 => by ext t; simp
            map_smul' := fun c s => by ext t; simp }
        change Function.Injective L
        rw [injective_iff_map_eq_zero]
        intro s hs
        have hzero : ∀ t : Fin j, (e s : Fin n → F) ⟨(start.val + t.val) % n, Nat.mod_lt _ (by omega)⟩ = 0 :=
          fun t => congrFun hs t
        let start' : Fin n := ⟨(start.val + j) % n, Nat.mod_lt _ (by omega)⟩
        let win' : (Fin r → F) →ₗ[F] (Fin r → F) :=
          { toFun := fun a u => w a ⟨(start'.val + u.val) % n, Nat.mod_lt _ (by omega)⟩
            map_add' := fun a1 a2 => by ext u; simp
            map_smul' := fun c a => by ext u; simp }
        have hwin'_surj : Function.Surjective win' :=
          (LinearMap.injective_iff_surjective (f := win')).mp (hw start')
        have hy_zero : (e s : Fin n → F) = 0 := by
          ext i
          by_cases hin : (i.val + n - start.val) % n < j
          · let t : Fin j := ⟨(i.val + n - start.val) % n, hin⟩
            have hfin : (⟨(start.val + t.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = i := by
              apply Fin.ext
              dsimp only [t]
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have hsum : start.val + (i.val + n - start.val) = i.val + n := by omega
              rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
            rw [← hfin]
            exact hzero t
          · let u0 : Fin r := ⟨(i.val + n - start.val) % n - j, by
              have := Nat.mod_lt (i.val + n - start.val) (by omega : 0 < n); omega⟩
            obtain ⟨a, ha⟩ := hwin'_surj (Pi.single u0 1)
            have hsum0 : ∑ k : Fin n, (e s : Fin n → F) k * w a k = 0 := by
              rw [hW_dot]
              have hWe : W (e s : Fin n → F) = 0 := (e s).2
              simp [hWe]
            have hidx_eq : ∀ u : Fin r, (start'.val + u.val) % n = (start.val + j + u.val) % n := by
              intro u
              dsimp only [start']
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hi_eq : (⟨(start'.val + u0.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = i := by
              apply Fin.ext
              dsimp only
              rw [hidx_eq]
              dsimp only [u0]
              have h1 : start.val + j + ((i.val + n - start.val) % n - j) =
                  start.val + (i.val + n - start.val) % n := by omega
              rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have h2 : start.val + (i.val + n - start.val) = i.val + n := by omega
              rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
            have hsum_single : ∑ k : Fin n, (e s : Fin n → F) k * w a k = (e s : Fin n → F) i := by
              rw [Finset.sum_eq_single i]
              · have hwa : w a i = 1 := by
                  have := congrFun ha u0
                  dsimp only [win', LinearMap.coe_mk, AddHom.coe_mk] at this
                  rw [hi_eq, Pi.single_apply, if_pos rfl] at this
                  exact this
                rw [hwa, mul_one]
              · intro k _ hki
                by_cases hk_in : (k.val + n - start.val) % n < j
                · let t : Fin j := ⟨(k.val + n - start.val) % n, hk_in⟩
                  have hfk : (⟨(start.val + t.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = k := by
                    apply Fin.ext
                    dsimp only [t]
                    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
                    have hsum : start.val + (k.val + n - start.val) = k.val + n := by omega
                    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
                  rw [← hfk, hzero t, zero_mul]
                · let uk : Fin r := ⟨(k.val + n - start.val) % n - j, by
                    have := Nat.mod_lt (k.val + n - start.val) (by omega : 0 < n); omega⟩
                  have hfk : (⟨(start'.val + uk.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = k := by
                    apply Fin.ext
                    dsimp only
                    rw [hidx_eq]
                    dsimp only [uk]
                    have h1 : start.val + j + ((k.val + n - start.val) % n - j) =
                        start.val + (k.val + n - start.val) % n := by omega
                    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
                    have h2 : start.val + (k.val + n - start.val) = k.val + n := by omega
                    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
                  have hne_u : uk ≠ u0 := by
                    intro heq_u
                    have hmid : (⟨(start'.val + uk.val) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) =
                        ⟨(start'.val + u0.val) % n, Nat.mod_lt _ (by omega)⟩ :=
                      Fin.ext (by dsimp only; rw [heq_u])
                    exact hki (hfk.symm.trans (hmid.trans hi_eq))
                  have hwa : w a k = 0 := by
                    have := congrFun ha uk
                    dsimp only [win', LinearMap.coe_mk, AddHom.coe_mk] at this
                    rw [hfk, Pi.single_apply, if_neg hne_u] at this
                    exact this
                  rw [hwa, mul_zero]
              · intro hnot
                exact absurd (Finset.mem_univ i) hnot
            rw [hsum_single] at hsum0
            exact hsum0
        exact e.injective (Subtype.ext (by rw [hy_zero, map_zero]; rfl))

lemma exists_sharp_witness (n w j : ℕ) (hn : 0 < n) (hjn : j ≤ n)
    (hcase : j ≤ w ∨ min n (w + 1) = n) :
    ∃ M ∈ (fullDef n w hn).powerset, M.card = n * 2 ^ j ∧
      ∀ T ∈ M.powerset, (totalDef n w hn T).testBit j = decide (T = M) := by
  have hfrom_A0 : ∀ A0 : Finset (Finset (Fin n)), A0.card = 2 ^ j →
      (∀ x ∈ A0, ∀ y ∈ A0, x ≠ y → Disjoint (patDef n w hn x) (patDef n w hn y)) →
      (∀ x : Finset (Fin n), patDef n w hn x ⊆ A0.biUnion (patDef n w hn) → x ∈ A0) →
      ∃ M ∈ (fullDef n w hn).powerset, M.card = n * 2 ^ j ∧
        ∀ T ∈ M.powerset, (totalDef n w hn T).testBit j = decide (T = M) := by
    intro A0 hcard hdisj hclosed
    let M := A0.biUnion (patDef n w hn)
    refine ⟨M, ?_, ?_, ?_⟩
    · rw [Finset.mem_powerset, Finset.biUnion_subset]
      intro x _
      exact patDef_subset_fullDef n w hn x
    · rw [Finset.card_biUnion (fun x hx y hy hne => hdisj x hx y hy hne)]
      simp only [card_patDef, Finset.sum_const, hcard, smul_eq_mul, mul_comm]
    · intro T hT
      rw [Finset.mem_powerset] at hT
      have hpass_sub : (Finset.univ.filter (fun x : Finset (Fin n) =>
          ∀ i : Fin n, (i, x ∩ scopeDef n w hn i) ∈ T)) ⊆ A0 := by
        intro x hx
        rw [Finset.mem_filter] at hx
        apply hclosed x
        exact (patDef_subset_iff n w hn x T).mpr hx.2 |>.trans hT
      by_cases hTM : T = M
      · subst hTM
        have hpass_eq : (Finset.univ.filter (fun x : Finset (Fin n) =>
            ∀ i : Fin n, (i, x ∩ scopeDef n w hn i) ∈ M)) = A0 := by
          apply Finset.Subset.antisymm hpass_sub
          intro x hx
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ x, (patDef_subset_iff n w hn x M).mp ?_⟩
          exact Finset.subset_biUnion_of_mem _ hx
        dsimp only [totalDef]
        rw [hpass_eq, hcard, Nat.testBit_two_pow]
        simp
      · have hlt : totalDef n w hn T < 2 ^ j := by
          rw [← hcard]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset hpass_sub]
          have hne_sdiff : (M \ T).Nonempty := by
            rw [Finset.sdiff_nonempty]
            intro hMT
            exact hTM (Finset.Subset.antisymm hT hMT)
          obtain ⟨p, hp⟩ := hne_sdiff
          rw [Finset.mem_sdiff] at hp
          obtain ⟨x0, hx0, hpx0⟩ := Finset.mem_biUnion.mp hp.1
          refine ⟨x0, hx0, ?_⟩
          rw [Finset.mem_filter]
          intro hgood
          exact hp.2 ((patDef_subset_iff n w hn x0 T).mpr hgood.2 hpx0)
        simp only [hTM, decide_false]
        exact Nat.testBit_eq_false_of_lt hlt
  rcases hcase with hjw | hkn
  · by_cases hj0 : j = 0
    · subst hj0
      apply hfrom_A0 {∅} (by simp)
      · intro x hx y hy hne
        simp only [Finset.mem_singleton] at hx hy
        exact absurd (hx.trans hy.symm) hne
      · intro x hx
        rw [Finset.mem_singleton, Finset.eq_empty_iff_forall_notMem]
        intro i hi
        have hmem : (i, x ∩ scopeDef n w hn i) ∈ ({∅} : Finset (Finset (Fin n))).biUnion (patDef n w hn) :=
          hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        obtain ⟨y, hy, hp⟩ := Finset.mem_biUnion.mp hmem
        rw [Finset.mem_singleton] at hy
        subst hy
        rw [patDef, Finset.mem_image] at hp
        obtain ⟨i', _, hi'⟩ := hp
        have hS : x ∩ scopeDef n w hn i = ∅ := by
          have := (Prod.mk.inj hi').2
          simpa using this.symm
        have hi_scope : i ∈ scopeDef n w hn i := by
          rw [scopeDef, Finset.mem_image]
          refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
          apply Fin.ext
          dsimp only
          rw [add_zero, Nat.mod_eq_of_lt i.isLt]
        have hi_inter : i ∈ x ∩ scopeDef n w hn i := Finset.mem_inter.mpr ⟨hi, hi_scope⟩
        rw [hS] at hi_inter
        exact Finset.notMem_empty i hi_inter
    · by_cases hkn2 : min n (w + 1) = n
      · have hle_card : 2 ^ j ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
          rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
          exact Nat.pow_le_pow_right (by omega) hjn
        obtain ⟨A0, _, hA0_card⟩ := Finset.exists_subset_card_eq hle_card
        have hscope_univ : ∀ i : Fin n, scopeDef n w hn i = Finset.univ := by
          intro i
          apply Finset.eq_univ_of_card
          rw [card_scopeDef, hkn2, Fintype.card_fin]
        apply hfrom_A0 A0 hA0_card
        · intro x _ y _ hne
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rw [patDef, Finset.mem_image] at hp1 hp2
          obtain ⟨i1, _, rfl⟩ := hp1
          obtain ⟨i2, _, heq⟩ := hp2
          have hS := (Prod.mk.inj heq).2
          rw [hscope_univ, hscope_univ, Finset.inter_univ, Finset.inter_univ] at hS
          exact hne hS.symm
        · intro x hx
          have hmem : (⟨0, hn⟩, x ∩ scopeDef n w hn ⟨0, hn⟩) ∈ A0.biUnion (patDef n w hn) :=
            hx (Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩)
          rw [Finset.mem_biUnion] at hmem
          obtain ⟨y, hy, hp⟩ := hmem
          rw [patDef, Finset.mem_image] at hp
          obtain ⟨i, _, heq⟩ := hp
          have hS := (Prod.mk.inj heq).2
          rw [hscope_univ, hscope_univ, Finset.inter_univ, Finset.inter_univ] at hS
          rw [← hS]
          exact hy
      · have hj1 : 1 ≤ j := by omega
        have hk_eq : min n (w + 1) = w + 1 := by omega
        obtain ⟨f, hf⟩ := exists_cyclic_window_inj n j hj1 hjn
        let word : (Fin j → F) → Finset (Fin n) := fun s =>
          Finset.univ.filter (fun i : Fin n => f s i = 1)
        have hword_win_inj : ∀ start : Fin n, ∀ s1 s2 : Fin j → F,
            (∀ t : Fin j,
              (⟨(start.val + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ word s1 ↔
              (⟨(start.val + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ word s2) →
            s1 = s2 := by
          intro start s1 s2 hiff
          apply hf start
          ext t
          dsimp only
          have h := hiff t
          simp only [word, Finset.mem_filter, Finset.mem_univ, true_and] at h
          have hF : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
            fin_cases a
            · exact Or.inl rfl
            · exact Or.inr rfl
          have h1 := hF (f s1 ⟨(start.val + t.val) % n, Nat.mod_lt _ hn⟩)
          have h2 := hF (f s2 ⟨(start.val + t.val) % n, Nat.mod_lt _ hn⟩)
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · rw [h1, h2]
          · exfalso; have := h.mpr h2; rw [h1] at this; exact zero_ne_one this
          · exfalso; have := h.mp h1; rw [h2] at this; exact zero_ne_one this
          · rw [h1, h2]
        have hword_inj : Function.Injective word := by
          intro s1 s2 h12
          exact hword_win_inj ⟨0, hn⟩ s1 s2 (fun t => by rw [h12])
        let A0 : Finset (Finset (Fin n)) := Finset.univ.image word
        have hA0_card : A0.card = 2 ^ j := by
          rw [Finset.card_image_of_injective _ hword_inj, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, ZMod.card]
        apply hfrom_A0 A0 hA0_card
        · intro x hx y hy hne
          rw [Finset.mem_image] at hx hy
          obtain ⟨s1, _, rfl⟩ := hx
          obtain ⟨s2, _, rfl⟩ := hy
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rw [patDef, Finset.mem_image] at hp1 hp2
          obtain ⟨i1, _, rfl⟩ := hp1
          obtain ⟨i2, _, heq⟩ := hp2
          have hi : i2 = i1 := (Prod.mk.inj heq).1
          subst hi
          have hS : word s2 ∩ scopeDef n w hn i2 = word s1 ∩ scopeDef n w hn i2 := (Prod.mk.inj heq).2
          have hs_eq : s1 = s2 := by
            apply hword_win_inj i2
            intro t
            have ht_mem : (⟨(i2.val + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ scopeDef n w hn i2 := by
              rw [scopeDef, Finset.mem_image]
              exact ⟨t.val, Finset.mem_range.mpr (by omega), rfl⟩
            have h1 := Finset.ext_iff.mp hS ⟨(i2.val + t.val) % n, Nat.mod_lt _ hn⟩
            simp only [Finset.mem_inter, ht_mem, and_true] at h1
            exact h1.symm
          exact hne (congrArg word hs_eq)
        · intro x hx
          have hstep : ∀ i : Fin n, ∃ s : Fin j → F,
              x ∩ scopeDef n w hn i = word s ∩ scopeDef n w hn i := by
            intro i
            have hmem : (i, x ∩ scopeDef n w hn i) ∈ A0.biUnion (patDef n w hn) :=
              hx (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
            rw [Finset.mem_biUnion] at hmem
            obtain ⟨y, hy, hp⟩ := hmem
            rw [Finset.mem_image] at hy
            obtain ⟨s, _, rfl⟩ := hy
            rw [patDef, Finset.mem_image] at hp
            obtain ⟨i', _, heq⟩ := hp
            have hi' : i' = i := (Prod.mk.inj heq).1
            subst hi'
            exact ⟨s, (Prod.mk.inj heq).2.symm⟩
          choose s hs using hstep
          have hs_adj : ∀ i : Fin n,
              s i = s ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ := by
            intro i
            let i1 : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
            apply hword_win_inj i1
            intro t
            have hidx : (i1.val + t.val) % n = (i.val + (t.val + 1)) % n := by
              dsimp only [i1]
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 t.val]
            have hmem_i : (⟨(i1.val + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ scopeDef n w hn i := by
              rw [scopeDef, Finset.mem_image]
              refine ⟨t.val + 1, Finset.mem_range.mpr (by omega), ?_⟩
              exact Fin.ext hidx.symm
            have hmem_i1 : (⟨(i1.val + t.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ scopeDef n w hn i1 := by
              rw [scopeDef, Finset.mem_image]
              exact ⟨t.val, Finset.mem_range.mpr (by omega), rfl⟩
            have h1 := Finset.ext_iff.mp (hs i) ⟨(i1.val + t.val) % n, Nat.mod_lt _ hn⟩
            have h2 := Finset.ext_iff.mp (hs i1) ⟨(i1.val + t.val) % n, Nat.mod_lt _ hn⟩
            simp only [Finset.mem_inter, hmem_i, hmem_i1, and_true] at h1 h2
            exact h1.symm.trans h2
          have hs_const : ∀ i : Fin n, s i = s ⟨0, hn⟩ := by
            intro ⟨a, ha⟩
            induction a with
            | zero => rfl
            | succ a iha =>
              have ha' : a < n := Nat.lt_of_succ_lt ha
              have hnext : (⟨(a + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨a + 1, ha⟩ :=
                Fin.ext (Nat.mod_eq_of_lt ha)
              have h1 := hs_adj ⟨a, ha'⟩
              rw [hnext] at h1
              rw [← h1, iha ha']
          have hx_eq : x = word (s ⟨0, hn⟩) := by
            ext i
            have hi_mem : i ∈ scopeDef n w hn i := by
              rw [scopeDef, Finset.mem_image]
              exact ⟨0, Finset.mem_range.mpr (by omega), Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])⟩
            have h1 := Finset.ext_iff.mp (hs i) i
            simp only [Finset.mem_inter, hi_mem, and_true] at h1
            rw [h1, hs_const i]
          rw [hx_eq]
          exact Finset.mem_image.mpr ⟨s ⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  · have hle_card : 2 ^ j ≤ (Finset.univ : Finset (Finset (Fin n))).card := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
      exact Nat.pow_le_pow_right (by omega) hjn
    obtain ⟨A0, _, hA0_card⟩ := Finset.exists_subset_card_eq hle_card
    have hscope_univ : ∀ i : Fin n, scopeDef n w hn i = Finset.univ := by
      intro i
      apply Finset.eq_univ_of_card
      rw [card_scopeDef, hkn, Fintype.card_fin]
    apply hfrom_A0 A0 hA0_card
    · intro x _ y _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [patDef, Finset.mem_image] at hp1 hp2
      obtain ⟨i1, _, rfl⟩ := hp1
      obtain ⟨i2, _, heq⟩ := hp2
      have hS := (Prod.mk.inj heq).2
      rw [hscope_univ, hscope_univ, Finset.inter_univ, Finset.inter_univ] at hS
      exact hne hS.symm
    · intro x hx
      have hmem : (⟨0, hn⟩, x ∩ scopeDef n w hn ⟨0, hn⟩) ∈ A0.biUnion (patDef n w hn) :=
        hx (Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩)
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨y, hy, hp⟩ := hmem
      rw [patDef, Finset.mem_image] at hp
      obtain ⟨i, _, heq⟩ := hp
      have hS := (Prod.mk.inj heq).2
      rw [hscope_univ, hscope_univ, Finset.inter_univ, Finset.inter_univ] at hS
      rw [← hS]
      exact hy

lemma scopeDef_w_zero (n : ℕ) (hn : 0 < n) (i : Fin n) :
    scopeDef n 0 hn i = {i} := by
  have hk : min n 1 = 1 := Nat.min_eq_right hn
  dsimp only [scopeDef]
  rw [hk, Finset.range_one, Finset.image_singleton]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

lemma totalDef_w_zero (n : ℕ) (hn : 0 < n) (T : Finset (Fin n × Finset (Fin n))) :
    totalDef n 0 hn T =
      if ∀ i : Fin n, (i, ∅) ∈ T ∨ (i, {i}) ∈ T then
        2 ^ (Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T)).card
      else 0 := by
  dsimp only [totalDef]
  have hinter : ∀ (x : Finset (Fin n)) (i : Fin n),
      x ∩ scopeDef n 0 hn i = if i ∈ x then {i} else ∅ := by
    intro x i
    rw [scopeDef_w_zero]
    split_ifs with hi
    · ext a; simp only [Finset.mem_inter, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩
    · ext a; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨h1, rfl⟩; exact hi h1
  by_cases hall : ∀ i : Fin n, (i, ∅) ∈ T ∨ (i, {i}) ∈ T
  · rw [if_pos hall]
    let D := Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T)
    let forced := Finset.univ.filter (fun i : Fin n => (i, ∅) ∉ T)
    have hdisj : Disjoint D forced := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_filter] at hi1 hi2
      exact hi2.2 hi1.2.1
    rw [← Finset.card_powerset]
    refine Finset.card_bij (fun x _ => x ∩ D) ?_ ?_ ?_
    · intro x _
      rw [Finset.mem_powerset]
      exact Finset.inter_subset_right
    · intro x1 hx1 x2 hx2 heq
      rw [Finset.mem_filter] at hx1 hx2
      ext i
      by_cases hiD : i ∈ D
      · have := Finset.ext_iff.mp heq i
        simpa [Finset.mem_inter, hiD] using this
      · have h1 := hx1.2 i
        have h2 := hx2.2 i
        rw [hinter] at h1 h2
        rw [Finset.mem_filter] at hiD
        rcases hall i with h0 | h1T
        · have hnot1 : (i, {i}) ∉ T := fun h' => hiD ⟨Finset.mem_univ i, h0, h'⟩
          have hx1' : i ∉ x1 := fun h => hnot1 (by simpa [h] using h1)
          have hx2' : i ∉ x2 := fun h => hnot1 (by simpa [h] using h2)
          simp [hx1', hx2']
        · have hnot0 : (i, ∅) ∉ T := fun h' => hiD ⟨Finset.mem_univ i, h', h1T⟩
          have hx1' : i ∈ x1 := by by_contra h; exact hnot0 (by simpa [h] using h1)
          have hx2' : i ∈ x2 := by by_contra h; exact hnot0 (by simpa [h] using h2)
          simp [hx1', hx2']
    · intro S hS
      rw [Finset.mem_powerset] at hS
      refine ⟨S ∪ forced, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun i => ?_⟩
        rw [hinter]
        by_cases hi : i ∈ S ∪ forced
        · rw [if_pos hi]
          rcases Finset.mem_union.mp hi with hiS | hiF
          · exact (Finset.mem_filter.mp (hS hiS)).2.2
          · have hnot0 := (Finset.mem_filter.mp hiF).2
            rcases hall i with h0 | h1T
            · exact absurd h0 hnot0
            · exact h1T
        · rw [if_neg hi]
          have hnotF : i ∉ forced := fun h => hi (Finset.mem_union_right S h)
          by_contra hnot0
          exact hnotF (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot0⟩)
      · ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hiS | hiF, hiD⟩
          · exact hiS
          · exact absurd hiF (Finset.disjoint_left.mp hdisj hiD)
        · intro hiS
          exact ⟨Or.inl hiS, hS hiS⟩
  · rw [if_neg hall]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply hall
    intro i
    have hi := hx i
    rw [hinter] at hi
    split_ifs at hi
    · exact Or.inr hi
    · exact Or.inl hi

lemma coeffDef_w_zero_iff (n j : ℕ) (hn : 0 < n) (M : Finset (Fin n × Finset (Fin n)))
    (hM : M ⊆ fullDef n 0 hn) :
    coeffDef n 0 hn j M = true → M.card = n + j := by
  intro hcoeff
  let D := Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M ∧ (i, {i}) ∈ M)
  have hM_mem : ∀ p ∈ M, p.2 = ∅ ∨ p.2 = {p.1} := by
    intro ⟨i, S⟩ hp
    have hf := hM hp
    rw [fullDef, Finset.mem_filter, scopeDef_w_zero, Finset.subset_singleton_iff] at hf
    exact hf.2
  have hall : ∀ i : Fin n, (i, ∅) ∈ M ∨ (i, {i}) ∈ M := by
    by_contra hnot
    have hempty : M.powerset.filter (fun T => (totalDef n 0 hn T).testBit j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro T hT hbit
      rw [Finset.mem_powerset] at hT
      rw [totalDef_w_zero] at hbit
      have hnotT : ¬ ∀ i : Fin n, (i, ∅) ∈ T ∨ (i, {i}) ∈ T := by
        intro hallT
        apply hnot
        intro i
        rcases hallT i with h0 | h1
        · exact Or.inl (hT h0)
        · exact Or.inr (hT h1)
      rw [if_neg hnotT] at hbit
      simp at hbit
    dsimp only [coeffDef] at hcoeff
    rw [hempty] at hcoeff
    simp at hcoeff
  have hM_card : M.card = n + D.card := by
    have hsplit : M = (Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M)).image (fun i => (i, ∅)) ∪
        (Finset.univ.filter (fun i : Fin n => (i, {i}) ∈ M)).image (fun i => (i, {i})) := by
      ext ⟨i, S⟩
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hp
        rcases hM_mem (i, S) hp with hS | hS <;> dsimp only at hS <;> subst hS
        · left; exact ⟨i, hp, rfl⟩
        · right; exact ⟨i, hp, rfl⟩
      · rintro (⟨i', hi', heq⟩ | ⟨i', hi', heq⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact hi'
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact hi'
    have hdisj : Disjoint
        ((Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M)).image (fun i => (i, (∅ : Finset (Fin n)))))
        ((Finset.univ.filter (fun i : Fin n => (i, {i}) ∈ M)).image (fun i => (i, {i}))) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_image] at hp1 hp2
      obtain ⟨i1, _, rfl⟩ := hp1
      obtain ⟨i2, _, heq⟩ := hp2
      have hS := (Prod.mk.inj heq).2
      exact Finset.singleton_ne_empty i2 hS
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
    have hunion : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M) ∪
        Finset.univ.filter (fun i : Fin n => (i, {i}) ∈ M) = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hall i
    have hinter : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M) ∩
        Finset.univ.filter (fun i : Fin n => (i, {i}) ∈ M) = D := by
      ext i
      simp [D]
    have hcu := Finset.card_union_add_card_inter
      (Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M))
      (Finset.univ.filter (fun i : Fin n => (i, {i}) ∈ M))
    rw [hunion, hinter, Finset.card_univ, Fintype.card_fin] at hcu
    omega
  have hD_eq : D.card = j := by
    by_contra hne
    by_cases hlt : D.card < j
    · have hempty : M.powerset.filter (fun T => (totalDef n 0 hn T).testBit j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT hbit
        rw [Finset.mem_powerset] at hT
        rw [totalDef_w_zero] at hbit
        split_ifs at hbit with hallT
        · have hsub : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) ⊆ D := by
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨Finset.mem_univ i, hT hi.2.1, hT hi.2.2⟩
          have hcard_le := Finset.card_le_card hsub
          rw [Nat.testBit_two_pow] at hbit
          simp only [decide_eq_true_eq] at hbit
          omega
        · simp at hbit
      dsimp only [coeffDef] at hcoeff
      rw [hempty] at hcoeff
      simp at hcoeff
    · have hgt : j < D.card := by omega
      have hcard_even : (M.powerset.filter (fun T => (totalDef n 0 hn T).testBit j)).card % 2 = 0 := by
        let Good := M.powerset.filter (fun T => (totalDef n 0 hn T).testBit j)
        have hfib : Good.card = ∑ S ∈ D.powersetCard j,
            (Good.filter (fun T => Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) = S)).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext T
            simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_filter]
            constructor
            · intro hTG
              have hT := (Finset.mem_filter.mp hTG).1
              have hbit := (Finset.mem_filter.mp hTG).2
              rw [Finset.mem_powerset] at hT
              rw [totalDef_w_zero] at hbit
              split_ifs at hbit with hallT
              · rw [Nat.testBit_two_pow, decide_eq_true_eq] at hbit
                refine ⟨Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T), ⟨?_, hbit⟩, hTG, rfl⟩
                intro i hi
                rw [Finset.mem_filter] at hi ⊢
                exact ⟨Finset.mem_univ i, hT hi.2.1, hT hi.2.2⟩
              · simp at hbit
            · rintro ⟨S, _, hTG, _⟩
              exact hTG
          · intro S1 _ S2 _ hneS
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro T h1 h2
            rw [Finset.mem_filter] at h1 h2
            exact hneS (h1.2.symm.trans h2.2)
        have hfib_card : ∀ S ∈ D.powersetCard j,
            (Good.filter (fun T => Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) = S)).card =
              2 ^ (D \ S).card := by
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          rw [← Finset.card_powerset]
          refine Finset.card_bij (fun T _ => (D \ S).filter (fun i => (i, {i}) ∈ T)) ?_ ?_ ?_
          · intro T _
            rw [Finset.mem_powerset]
            exact Finset.filter_subset _ _
          · intro T1 hT1 T2 hT2 heq
            rw [Finset.mem_filter] at hT1 hT2
            have hT1M := (Finset.mem_powerset.mp (Finset.mem_filter.mp hT1.1).1)
            have hT2M := (Finset.mem_powerset.mp (Finset.mem_filter.mp hT2.1).1)
            have hall1 : ∀ i : Fin n, (i, ∅) ∈ T1 ∨ (i, {i}) ∈ T1 := by
              have hb := (Finset.mem_filter.mp hT1.1).2
              rw [totalDef_w_zero] at hb
              by_contra h; rw [if_neg h] at hb; simp at hb
            have hall2 : ∀ i : Fin n, (i, ∅) ∈ T2 ∨ (i, {i}) ∈ T2 := by
              have hb := (Finset.mem_filter.mp hT2.1).2
              rw [totalDef_w_zero] at hb
              by_contra h; rw [if_neg h] at hb; simp at hb
            ext ⟨i, A⟩
            by_cases hAM : (i, A) ∈ M
            · rcases hM_mem (i, A) hAM with hA | hA <;> dsimp only at hA <;> subst hA
              · by_cases hiS : i ∈ S
                · have h1 := (Finset.mem_filter.mp (hT1.2.symm ▸ hiS)).2.1
                  have h2 := (Finset.mem_filter.mp (hT2.2.symm ▸ hiS)).2.1
                  simp [h1, h2]
                · by_cases hiD : i ∈ D
                  · have hiDS : i ∈ D \ S := Finset.mem_sdiff.mpr ⟨hiD, hiS⟩
                    have hiff1 : (i, {i}) ∈ T1 ↔ (i, {i}) ∈ T2 := by
                      have := Finset.ext_iff.mp heq i
                      simpa [Finset.mem_filter, hiDS] using this
                    have hnotboth1 : ¬ ((i, ∅) ∈ T1 ∧ (i, {i}) ∈ T1) := fun h =>
                      hiS (hT1.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
                    have hnotboth2 : ¬ ((i, ∅) ∈ T2 ∧ (i, {i}) ∈ T2) := fun h =>
                      hiS (hT2.2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
                    rcases hall1 i with h10 | h11 <;> rcases hall2 i with h20 | h21
                    · simp [h10, h20]
                    · exfalso
                      have h11' : (i, {i}) ∈ T1 := hiff1.mpr h21
                      exact hnotboth1 ⟨h10, h11'⟩
                    · exfalso
                      have h21' : (i, {i}) ∈ T2 := hiff1.mp h11
                      exact hnotboth2 ⟨h20, h21'⟩
                    · have h10' : (i, ∅) ∉ T1 := fun h => hnotboth1 ⟨h, h11⟩
                      have h20' : (i, ∅) ∉ T2 := fun h => hnotboth2 ⟨h, h21⟩
                      simp [h10', h20']
                  · have hnot1M : (i, {i}) ∉ M := fun h' => hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hAM, h'⟩)
                    have h10 : (i, ∅) ∈ T1 := (hall1 i).resolve_right (fun h => hnot1M (hT1M h))
                    have h20 : (i, ∅) ∈ T2 := (hall2 i).resolve_right (fun h => hnot1M (hT2M h))
                    simp [h10, h20]
              · by_cases hiS : i ∈ S
                · have h1 := (Finset.mem_filter.mp (hT1.2.symm ▸ hiS)).2.2
                  have h2 := (Finset.mem_filter.mp (hT2.2.symm ▸ hiS)).2.2
                  simp [h1, h2]
                · by_cases hiD : i ∈ D
                  · have hiDS : i ∈ D \ S := Finset.mem_sdiff.mpr ⟨hiD, hiS⟩
                    have := Finset.ext_iff.mp heq i
                    simpa [Finset.mem_filter, hiDS] using this
                  · have hnot0M : (i, ∅) ∉ M := fun h' => hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h', hAM⟩)
                    have h11 : (i, {i}) ∈ T1 := (hall1 i).resolve_left (fun h => hnot0M (hT1M h))
                    have h21 : (i, {i}) ∈ T2 := (hall2 i).resolve_left (fun h => hnot0M (hT2M h))
                    simp [h11, h21]
            · have h1 : (i, A) ∉ T1 := fun h => hAM (hT1M h)
              have h2 : (i, A) ∉ T2 := fun h => hAM (hT2M h)
              simp [h1, h2]
          · intro R hR
            rw [Finset.mem_powerset] at hR
            let T := (M.filter (fun p => p.1 ∉ D \ S)) ∪
              (R.image (fun i => (i, {i}))) ∪
              (((D \ S) \ R).image (fun i => (i, ∅)))
            have hTM : T ⊆ M := by
              intro p hp
              rcases Finset.mem_union.mp hp with hp1 | hp2
              · rcases Finset.mem_union.mp hp1 with hp11 | hp12
                · exact (Finset.mem_filter.mp hp11).1
                · rw [Finset.mem_image] at hp12
                  obtain ⟨i, hi, rfl⟩ := hp12
                  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hR hi)).1).2.2
              · rw [Finset.mem_image] at hp2
                obtain ⟨i, hi, rfl⟩ := hp2
                exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).1).2.1
            have hT_double : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) = S := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨h0, h1⟩
                by_contra hiS
                by_cases hiD : i ∈ D
                · have hiDS : i ∈ D \ S := Finset.mem_sdiff.mpr ⟨hiD, hiS⟩
                  by_cases hiR : i ∈ R
                  · rcases Finset.mem_union.mp h0 with h01 | h02
                    · rcases Finset.mem_union.mp h01 with h011 | h012
                      · exact (Finset.mem_filter.mp h011).2 hiDS
                      · rw [Finset.mem_image] at h012
                        obtain ⟨k, _, heq⟩ := h012
                        exact Finset.singleton_ne_empty k (Prod.mk.inj heq).2
                    · rw [Finset.mem_image] at h02
                      obtain ⟨k, hk, heq⟩ := h02
                      have hk' := (Prod.mk.inj heq).1
                      subst hk'
                      exact (Finset.mem_sdiff.mp hk).2 hiR
                  · rcases Finset.mem_union.mp h1 with h11 | h12
                    · rcases Finset.mem_union.mp h11 with h111 | h112
                      · exact (Finset.mem_filter.mp h111).2 hiDS
                      · rw [Finset.mem_image] at h112
                        obtain ⟨k, hk, heq⟩ := h112
                        have hk' := (Prod.mk.inj heq).1
                        subst hk'
                        exact hiR hk
                    · rw [Finset.mem_image] at h12
                      obtain ⟨k, _, heq⟩ := h12
                      exact Finset.singleton_ne_empty i (Prod.mk.inj heq).2.symm
                · exact hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hTM h0, hTM h1⟩)
              · intro hiS
                have hiD := hS.1 hiS
                have hnotDS : i ∉ D \ S := fun h => (Finset.mem_sdiff.mp h).2 hiS
                have hM0 := (Finset.mem_filter.mp hiD).2.1
                have hM1 := (Finset.mem_filter.mp hiD).2.2
                exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hM0, hnotDS⟩)),
                  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hM1, hnotDS⟩))⟩
            have hallT : ∀ i : Fin n, (i, ∅) ∈ T ∨ (i, {i}) ∈ T := by
              intro i
              by_cases hiDS : i ∈ D \ S
              · by_cases hiR : i ∈ R
                · exact Or.inr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiR, rfl⟩)))
                · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hiDS, hiR⟩, rfl⟩))
              · rcases hall i with h0 | h1
                · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h0, hiDS⟩)))
                · exact Or.inr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h1, hiDS⟩)))
            refine ⟨T, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTM, ?_⟩, hT_double⟩
              rw [totalDef_w_zero, if_pos hallT, hT_double, hS.2, Nat.testBit_two_pow]
              simp
            · ext i
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hiDS, h1⟩
                rcases Finset.mem_union.mp h1 with h11 | h12
                · rcases Finset.mem_union.mp h11 with h111 | h112
                  · exact absurd hiDS (Finset.mem_filter.mp h111).2
                  · rw [Finset.mem_image] at h112
                    obtain ⟨k, hk, heq⟩ := h112
                    have := (Prod.mk.inj heq).1
                    subst this; exact hk
                · rw [Finset.mem_image] at h12
                  obtain ⟨k, _, heq⟩ := h12
                  exact absurd (Prod.mk.inj heq).2.symm (Finset.singleton_ne_empty i)
              · intro hiR
                exact ⟨hR hiR, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiR, rfl⟩))⟩
        rw [hfib, Finset.sum_nat_mod]
        have hzero : ∀ S ∈ D.powersetCard j,
            (Good.filter (fun T => Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) = S)).card % 2 = 0 := by
          intro S hS
          rw [hfib_card S hS]
          rw [Finset.mem_powersetCard] at hS
          have hcard_sdiff : (D \ S).card = D.card - j := by
            rw [Finset.card_sdiff_of_subset hS.1, hS.2]
          rw [hcard_sdiff]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D.card - j ≠ 0)
          rw [hk, pow_succ]
          omega
        rw [Finset.sum_congr rfl hzero]
        simp
      dsimp only [coeffDef] at hcoeff
      rw [Nat.testBit_eq_decide_div_mod_eq] at hcoeff
      simp only [Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one, hcard_even] at hcoeff
      simp at hcoeff
  rw [hM_card, hD_eq]

lemma exists_w_zero_witness (n j : ℕ) (hn : 0 < n) (hjn : j ≤ n) :
    ∃ M ∈ (fullDef n 0 hn).powerset, M.card = n + j ∧ coeffDef n 0 hn j M = true := by
  let D : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < j)
  have hD_card : D.card = j := by
    refine (Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin j)) ?_ ?_ ?_).trans (Fintype.card_fin j)
    · intro i _; exact Finset.mem_univ _
    · intro i1 _ i2 _ h12; exact Fin.ext (by simpa using congrArg Fin.val h12)
    · intro k _
      refine ⟨⟨k.val, lt_of_lt_of_le k.isLt hjn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, ?_⟩
      exact Fin.ext rfl
  let M : Finset (Fin n × Finset (Fin n)) :=
    Finset.univ.image (fun i : Fin n => (i, ∅)) ∪ D.image (fun i : Fin n => (i, {i}))
  have hdisj : Disjoint (Finset.univ.image (fun i : Fin n => (i, (∅ : Finset (Fin n)))))
      (D.image (fun i : Fin n => (i, {i}))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_image] at hp1 hp2
    obtain ⟨i1, _, rfl⟩ := hp1
    obtain ⟨i2, _, heq⟩ := hp2
    exact Finset.singleton_ne_empty i2 (Prod.mk.inj heq).2
  have hM_sub : M ⊆ fullDef n 0 hn := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · rw [Finset.mem_image] at hp1
      obtain ⟨i, _, rfl⟩ := hp1
      rw [fullDef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Finset.empty_subset _⟩
    · rw [Finset.mem_image] at hp2
      obtain ⟨i, _, rfl⟩ := hp2
      rw [fullDef, Finset.mem_filter, scopeDef_w_zero]
      exact ⟨Finset.mem_univ _, Finset.Subset.refl _⟩
  have hM_card : M.card = n + j := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_fin, hD_card]
  refine ⟨M, Finset.mem_powerset.mpr hM_sub, hM_card, ?_⟩
  dsimp only [coeffDef]
  have hfilt : M.powerset.filter (fun T => (totalDef n 0 hn T).testBit j) = {M} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hTM, hbit⟩
      rw [totalDef_w_zero] at hbit
      split_ifs at hbit with hallT
      · rw [Nat.testBit_two_pow, decide_eq_true_eq] at hbit
        have hsubD : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) ⊆ D := by
          intro i hi
          rw [Finset.mem_filter] at hi
          have h1M := hTM hi.2.2
          rcases Finset.mem_union.mp h1M with h11 | h12
          · rw [Finset.mem_image] at h11
            obtain ⟨k, _, heq⟩ := h11
            exact absurd (Prod.mk.inj heq).2.symm (Finset.singleton_ne_empty i)
          · rw [Finset.mem_image] at h12
            obtain ⟨k, hk, heq⟩ := h12
            have := (Prod.mk.inj heq).1
            subst this; exact hk
        have heqD : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ T ∧ (i, {i}) ∈ T) = D :=
          Finset.eq_of_subset_of_card_le hsubD (by rw [hD_card, hbit])
        apply Finset.Subset.antisymm hTM
        intro p hp
        rcases Finset.mem_union.mp hp with hp1 | hp2
        · rw [Finset.mem_image] at hp1
          obtain ⟨i, _, rfl⟩ := hp1
          by_cases hiD : i ∈ D
          · exact (Finset.mem_filter.mp (heqD.symm ▸ hiD)).2.1
          · have hnot1 : (i, {i}) ∉ T := fun h => by
              have h1M := hTM h
              rcases Finset.mem_union.mp h1M with h11 | h12
              · rw [Finset.mem_image] at h11
                obtain ⟨k, _, heq⟩ := h11
                exact Finset.singleton_ne_empty i (Prod.mk.inj heq).2.symm
              · rw [Finset.mem_image] at h12
                obtain ⟨k, hk, heq⟩ := h12
                have := (Prod.mk.inj heq).1
                subst this; exact hiD hk
            exact (hallT i).resolve_right hnot1
        · rw [Finset.mem_image] at hp2
          obtain ⟨i, hiD, rfl⟩ := hp2
          exact (Finset.mem_filter.mp (heqD.symm ▸ hiD)).2.2
      · simp at hbit
    · rintro rfl
      refine ⟨Finset.Subset.refl M, ?_⟩
      rw [totalDef_w_zero]
      have hallM : ∀ i : Fin n, (i, ∅) ∈ M ∨ (i, {i}) ∈ M := fun i =>
        Or.inl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      rw [if_pos hallM]
      have heqD : Finset.univ.filter (fun i : Fin n => (i, ∅) ∈ M ∧ (i, {i}) ∈ M) = D := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h1⟩
          rcases Finset.mem_union.mp h1 with h11 | h12
          · rw [Finset.mem_image] at h11
            obtain ⟨k, _, heq⟩ := h11
            exact absurd (Prod.mk.inj heq).2.symm (Finset.singleton_ne_empty i)
          · rw [Finset.mem_image] at h12
            obtain ⟨k, hk, heq⟩ := h12
            have := (Prod.mk.inj heq).1
            subst this; exact hk
        · intro hiD
          exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiD, rfl⟩)⟩
      rw [heqD, hD_card, Nat.testBit_two_pow]
      simp
  rw [hfilt]
  simp

end PEqualNP.Outside.L_clb_099_aux

open PEqualNP.Outside.L_clb_099_aux in
theorem PEqualNP.Outside.L_clb_099 : (∀ (n w : Nat) (hn : 0 < n),
  let Site := Fin n
  let Slot := Site × Finset Site
  let k := min n (w+1)
  let scope := fun i : Site => (Finset.range k).image
    (fun t => (⟨(i.val+t)%n, Nat.mod_lt _ hn⟩ : Site))
  let full := (Finset.univ : Finset Slot).filter (fun candidate => candidate.2 ⊆ scope candidate.1)
  let total := fun table : Finset Slot =>
    ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (bit : Nat) (support : Finset Slot) =>
    ((support.powerset.filter (fun sub => (total sub).testBit bit)).card).testBit 0
  let degree := fun idx : Nat => (full.powerset.filter (fun mon => coeff idx mon = true)).sup Finset.card
  let E := n*2^k
  ∀ j : Nat, j ≤ n →
    degree j ≤ min E (n*2^j) ∧
    ((j ≤ w ∨ k = n) →
      degree j = n*2^j ∧
        ∃ M ∈ full.powerset, M.card = n*2^j ∧
          ∀ T ∈ M.powerset, (total T).testBit j = decide (T = M)) ∧
    (w = 0 → degree j = n+j) ∧
    (j = n → degree j = E)) := by
  intro n w hn Site Slot k scope full total coeff degree E j hjn
  have hdeg_le : degree j ≤ min E (n * 2 ^ j) := by
    apply Finset.sup_le
    intro M hM
    rw [Finset.mem_filter, Finset.mem_powerset] at hM
    apply le_min
    · have hc : full.card = E := card_fullDef n w hn
      rw [← hc]
      exact Finset.card_le_card hM.1
    · have hcoeff : coeffDef n w hn j M = true := hM.2
      rw [coeffDef_eq_biUnion_parity] at hcoeff
      have hne : (((Finset.univ : Finset (Finset (Fin n))).powersetCard (2 ^ j)).filter
          (fun A => A.biUnion (patDef n w hn) = M)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        rw [hempty] at hcoeff
        simp at hcoeff
      obtain ⟨A, hA⟩ := hne
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hA
      rw [← hA.2]
      calc (A.biUnion (patDef n w hn)).card
          ≤ ∑ x ∈ A, (patDef n w hn x).card := Finset.card_biUnion_le
        _ = ∑ _x ∈ A, n := Finset.sum_congr rfl (fun x _ => card_patDef n w hn x)
        _ = n * 2 ^ j := by rw [Finset.sum_const, hA.1.2, smul_eq_mul, mul_comm]
  refine ⟨hdeg_le, ?_, ?_, ?_⟩
  · intro hcase
    obtain ⟨M, hM_pow, hM_card, hM_sharp⟩ := exists_sharp_witness n w j hn hjn hcase
    have hM_coeff : coeff j M = true := by
      dsimp only [coeff]
      have hfilt : M.powerset.filter (fun T => (total T).testBit j) = {M} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hT, hbit⟩
          have h := hM_sharp T hT
          change (totalDef n w hn T).testBit j = true at hbit
          rw [hbit] at h
          exact of_decide_eq_true h.symm
        · rintro rfl
          refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl T), ?_⟩
          have h := hM_sharp T (Finset.mem_powerset.mpr (Finset.Subset.refl T))
          simp only [decide_true] at h
          exact h
      rw [hfilt]
      simp
    have hge : n * 2 ^ j ≤ degree j := by
      rw [← hM_card]
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨hM_pow, hM_coeff⟩)
    have hle : degree j ≤ n * 2 ^ j := le_trans hdeg_le (min_le_right _ _)
    exact ⟨le_antisymm hle hge, M, hM_pow, hM_card, hM_sharp⟩
  · intro hw0
    subst hw0
    have hle : degree j ≤ n + j := by
      apply Finset.sup_le
      intro M hM
      rw [Finset.mem_filter, Finset.mem_powerset] at hM
      exact le_of_eq (coeffDef_w_zero_iff n j hn M hM.1 hM.2)
    obtain ⟨M, hM_pow, hM_card, hM_coeff⟩ := exists_w_zero_witness n j hn hjn
    have hge : n + j ≤ degree j := by
      rw [← hM_card]
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨hM_pow, hM_coeff⟩)
    exact le_antisymm hle hge
  · intro hjeq
    subst j
    have hle : degree n ≤ E := le_trans hdeg_le (min_le_left _ _)
    have hfull_coeff : coeff n full = true := by
      change coeffDef n w hn n (fullDef n w hn) = true
      rw [coeffDef_eq_biUnion_parity]
      have hfilt : ((Finset.univ : Finset (Finset (Fin n))).powersetCard (2 ^ n)).filter
          (fun A => A.biUnion (patDef n w hn) = fullDef n w hn) = {Finset.univ} := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨_, hAcard⟩, _⟩
          apply Finset.eq_univ_of_card
          rw [hAcard, Fintype.card_finset, Fintype.card_fin]
        · rintro rfl
          refine ⟨⟨Finset.Subset.refl _, ?_⟩, ?_⟩
          · rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
          · apply Finset.Subset.antisymm
            · rw [Finset.biUnion_subset]
              intro x _
              exact patDef_subset_fullDef n w hn x
            · intro ⟨i, S⟩ hp
              rw [fullDef, Finset.mem_filter] at hp
              rw [Finset.mem_biUnion]
              refine ⟨S, Finset.mem_univ S, ?_⟩
              rw [patDef, Finset.mem_image]
              refine ⟨i, Finset.mem_univ i, ?_⟩
              rw [Finset.inter_eq_left.mpr hp.2]
      rw [hfilt]
      simp
    have hge : E ≤ degree n := by
      have hc : full.card = E := card_fullDef n w hn
      rw [← hc]
      exact Finset.le_sup (f := Finset.card)
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl full), hfull_coeff⟩)
    exact le_antisymm hle hge

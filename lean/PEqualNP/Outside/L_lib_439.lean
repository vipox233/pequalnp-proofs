import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_439_aux

def bitsOf (m : ℕ) (a : Fin (2 ^ m)) : Fin m → ZMod 2 :=
  fun k => if a.val.testBit k.val then 1 else 0

def natOfBits : (m : ℕ) → (Fin m → ZMod 2) → ℕ
  | 0, _ => 0
  | m + 1, v => (if v ⟨0, Nat.zero_lt_succ m⟩ = 1 then 1 else 0) + 2 * natOfBits m (fun k => v k.succ)

theorem natOfBits_lt : ∀ (m : ℕ) (v : Fin m → ZMod 2), natOfBits m v < 2 ^ m
  | 0, _ => by simp [natOfBits]
  | m + 1, v => by
    unfold natOfBits
    have ih := natOfBits_lt m (fun k => v k.succ)
    have h0 : (if v ⟨0, Nat.zero_lt_succ m⟩ = 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    rw [pow_succ']
    omega

theorem testBit_natOfBits : ∀ (m : ℕ) (v : Fin m → ZMod 2) (k : Fin m),
    (natOfBits m v).testBit k.val = decide (v k = 1)
  | 0, _, k => Fin.elim0 k
  | m + 1, v, k => by
    unfold natOfBits
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.testBit_zero]
      split_ifs with h
      · simp [Nat.add_mul_mod_self_left]; exact h
      · simp [Nat.mul_mod_right]; exact h
    | succ k' =>
      simp only [Fin.val_succ, Nat.testBit_succ]
      have hdiv : ((if v ⟨0, Nat.zero_lt_succ m⟩ = 1 then 1 else 0) +
          2 * natOfBits m (fun j => v j.succ)) / 2 = natOfBits m (fun j => v j.succ) := by
        split_ifs <;> omega
      rw [hdiv]
      exact testBit_natOfBits m (fun j => v j.succ) k'

theorem natOfBits_bitsOf : ∀ (m : ℕ) (a : ℕ) (ha : a < 2 ^ m),
    natOfBits m (fun k : Fin m => if a.testBit k.val then 1 else 0) = a
  | 0, a, ha => by simp [natOfBits]; omega
  | m + 1, a, ha => by
    unfold natOfBits
    have hdiv_lt : a / 2 < 2 ^ m := by rw [pow_succ'] at ha; omega
    have hsucc : (fun k : Fin m => if a.testBit k.succ.val then (1 : ZMod 2) else 0) =
        (fun k : Fin m => if (a / 2).testBit k.val then 1 else 0) := by
      funext k
      simp [Nat.testBit_succ]
    rw [hsucc, natOfBits_bitsOf m (a / 2) hdiv_lt]
    have h0 : (if (if a.testBit 0 then (1 : ZMod 2) else 0) = 1 then 1 else 0) = a % 2 := by
      rw [Nat.testBit_zero]
      have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hmod with h | h <;> simp [h]
    rw [h0]
    omega

def bitsEquiv (m : ℕ) : Fin (2 ^ m) ≃ (Fin m → ZMod 2) where
  toFun := bitsOf m
  invFun v := ⟨natOfBits m v, natOfBits_lt m v⟩
  left_inv a := by
    ext
    exact natOfBits_bitsOf m a.val a.isLt
  right_inv v := by
    funext k
    unfold bitsOf
    simp only [testBit_natOfBits]
    have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := fun z => by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hv (v k) with h | h <;> simp [h]

def linPart (n : ℕ) (v : Fin (2 * n) → ZMod 2) (x : Fin n → ZMod 2) (i : Fin (n + 1)) : ZMod 2 :=
  ∑ j : Fin n, v ⟨i.val + (n - 1 - j.val), by omega⟩ * x j

theorem linPart_eq_seed (n : ℕ) (a : Fin (2 ^ (2 * n))) (x : Fin n → ZMod 2) (i : Fin (n + 1)) :
    linPart n (bitsOf (2 * n) a) x i =
      ∑ j : Fin n, if a.val.testBit (i.val + (n - 1 - j.val)) then x j else 0 := by
  unfold linPart bitsOf
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem linPart_add (n : ℕ) (v w : Fin (2 * n) → ZMod 2) (x : Fin n → ZMod 2) (i : Fin (n + 1)) :
    linPart n (v + w) x i = linPart n v x i + linPart n w x i := by
  unfold linPart
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [add_mul]

theorem linPart_sub_x (n : ℕ) (v : Fin (2 * n) → ZMod 2) (x y : Fin n → ZMod 2) (i : Fin (n + 1)) :
    linPart n v (fun j => x j - y j) i = linPart n v x i - linPart n v y i := by
  unfold linPart
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

theorem zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

theorem zmod2_eq_one_of_ne_zero {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

theorem exists_min_diff {n : ℕ} {x y : Fin n → ZMod 2} (hne : x ≠ y) :
    ∃ j₀ : Fin n, x j₀ ≠ y j₀ ∧ ∀ j : Fin n, j.val < j₀.val → x j = y j := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun j => x j ≠ y j)
  have hDne : D.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne
    funext j
    by_contra hne'
    have : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩
    rw [h] at this
    exact Finset.notMem_empty j this
  let j₀ := D.min' hDne
  have hj₀_mem : j₀ ∈ D := Finset.min'_mem D hDne
  refine ⟨j₀, (Finset.mem_filter.mp hj₀_mem).2, fun j hj => ?_⟩
  by_contra hne'
  have hj_mem : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩
  have hle : j₀ ≤ j := Finset.min'_le D j hj_mem
  have : j₀.val ≤ j.val := hle
  omega

theorem linPart_surj (n : ℕ) (level : Fin (n + 1)) (d : Fin n → ZMod 2) (j₀ : Fin n)
    (hd0 : d j₀ = 1) (hdmin : ∀ j : Fin n, j.val < j₀.val → d j = 0) :
    ∀ c : Fin (level.val + 1) → ZMod 2, ∃ v : Fin (2 * n) → ZMod 2,
      ∀ i : Fin (level.val + 1), linPart n v d ⟨i.val, by omega⟩ = c i := by
  intro c
  let p : ℕ := n - 1 - j₀.val
  have hp_lt : ∀ r : ℕ, r ≤ level.val → r + p < 2 * n := fun r hr => by omega
  have hbuild : ∀ (m : ℕ) (hm : m ≤ level.val + 1),
      ∃ v : Fin (2 * n) → ZMod 2,
        ∀ (r : ℕ) (hr : r < m), linPart n v d ⟨r, by omega⟩ = c ⟨r, by omega⟩ := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => 0, fun _ h => by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨v, hv⟩ := ih (by omega)
      let idx : Fin (2 * n) := ⟨m + p, hp_lt m (by omega)⟩
      let cur : ZMod 2 := linPart n v d ⟨m, by omega⟩
      let delta : ZMod 2 := c ⟨m, hm⟩ - cur
      let v' : Fin (2 * n) → ZMod 2 := Function.update v idx (v idx + delta)
      refine ⟨v', fun r hr => ?_⟩
      by_cases hrm : r < m
      · have hsame : linPart n v' d ⟨r, by omega⟩ = linPart n v d ⟨r, by omega⟩ := by
          unfold linPart
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hdj : d j = 0
          · simp [hdj]
          · have hge : j₀.val ≤ j.val := by
              by_contra hlt
              exact hdj (hdmin j (by omega))
            have hne_idx : (⟨r + (n - 1 - j.val), by omega⟩ : Fin (2 * n)) ≠ idx := by
              intro heq
              have := congrArg Fin.val heq
              dsimp only [idx, p] at this
              omega
            simp [v', Function.update, hne_idx]
        rw [hsame]
        exact hv r hrm
      · have hreq : r = m := by omega
        subst hreq
        have hdiff : linPart n v' d ⟨r, by omega⟩ - linPart n v d ⟨r, by omega⟩ = delta := by
          unfold linPart
          rw [← Finset.sum_sub_distrib]
          have hterm : ∀ j : Fin n,
              v' ⟨r + (n - 1 - j.val), by omega⟩ * d j - v ⟨r + (n - 1 - j.val), by omega⟩ * d j =
              if j = j₀ then delta else 0 := by
            intro j
            by_cases hj : j = j₀
            · subst hj
              have heq_idx : (⟨r + (n - 1 - j.val), by omega⟩ : Fin (2 * n)) = idx := by
                ext; rfl
              rw [heq_idx, hd0]
              simp [v', Function.update]
            · rw [if_neg hj]
              by_cases hdj : d j = 0
              · simp [hdj]
              · have hge : j₀.val ≤ j.val := by
                  by_contra hlt
                  exact hdj (hdmin j (by omega))
                have hgt : j₀.val < j.val := lt_of_le_of_ne hge (fun h => hj (Fin.ext h.symm))
                have hne_idx : (⟨r + (n - 1 - j.val), by omega⟩ : Fin (2 * n)) ≠ idx := by
                  intro heq
                  have := congrArg Fin.val heq
                  dsimp only [idx, p] at this
                  omega
                simp [v', Function.update, hne_idx]
          simp_rw [hterm]
          simp
        have hcur : cur = linPart n v d ⟨r, by omega⟩ := rfl
        have : linPart n v' d ⟨r, by omega⟩ = linPart n v d ⟨r, by omega⟩ + delta := by
          rw [← hdiff]; ring
        rw [this]
        dsimp only [delta, cur]
        ring
  obtain ⟨v, hv⟩ := hbuild (level.val + 1) (le_refl _)
  exact ⟨v, fun i => hv i.val i.isLt⟩

theorem card_ker_linPart (n : ℕ) (level : Fin (n + 1)) (x y : Fin n → ZMod 2) (hne : x ≠ y) :
    (Finset.univ.filter (fun a : Fin (2 ^ (2 * n)) =>
      ∀ i : Fin (n + 1), i.val ≤ level.val →
        linPart n (bitsOf (2 * n) a) x i = linPart n (bitsOf (2 * n) a) y i)).card *
      2 ^ (level.val + 1) = 2 ^ (2 * n) := by
  classical
  obtain ⟨j₀, hj₀ne, hj₀min⟩ := exists_min_diff hne
  let d : Fin n → ZMod 2 := fun j => x j - y j
  have hd0 : d j₀ = 1 := by
    apply zmod2_eq_one_of_ne_zero
    intro h
    exact hj₀ne (sub_eq_zero.mp h)
  have hdmin : ∀ j : Fin n, j.val < j₀.val → d j = 0 := fun j hj => by
    dsimp only [d]; rw [hj₀min j hj, sub_self]
  let T : (Fin (2 * n) → ZMod 2) → (Fin (level.val + 1) → ZMod 2) :=
    fun v i => linPart n v d ⟨i.val, by omega⟩
  have hTadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
    funext i; exact linPart_add n v w d ⟨i.val, by omega⟩
  have hTsurj : ∀ c, ∃ v, T v = c := fun c => by
    obtain ⟨v, hv⟩ := linPart_surj n level d j₀ hd0 hdmin c
    exact ⟨v, funext hv⟩
  let sec : (Fin (level.val + 1) → ZMod 2) → (Fin (2 * n) → ZMod 2) := fun c => (hTsurj c).choose
  have hsec : ∀ c, T (sec c) = c := fun c => (hTsurj c).choose_spec
  let K : Finset (Fin (2 * n) → ZMod 2) := Finset.univ.filter (fun v => T v = 0)
  have hcard_eq : (Finset.univ.filter (fun a : Fin (2 ^ (2 * n)) =>
      ∀ i : Fin (n + 1), i.val ≤ level.val →
        linPart n (bitsOf (2 * n) a) x i = linPart n (bitsOf (2 * n) a) y i)).card = K.card := by
    refine Finset.card_nbij' (bitsEquiv (2 * n)) (bitsEquiv (2 * n)).symm ?_ ?_ ?_ ?_
    · intro a ha
      simp only [K, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      funext i
      dsimp only [T, bitsEquiv, Equiv.coe_fn_mk]
      rw [linPart_sub_x, ha ⟨i.val, by omega⟩ (Nat.le_of_lt_succ i.isLt), sub_self]
      rfl
    · intro v hv
      simp only [K, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      intro i hi
      have hTi : T v ⟨i.val, by omega⟩ = 0 := congrFun hv ⟨i.val, by omega⟩
      have hbi : bitsOf (2 * n) ((bitsEquiv (2 * n)).symm v) = v := (bitsEquiv (2 * n)).apply_symm_apply v
      rw [hbi]
      have hsub : linPart n v x i - linPart n v y i = 0 := by
        rw [← linPart_sub_x]
        exact hTi
      exact sub_eq_zero.mp hsub
    · intro a _; exact (bitsEquiv (2 * n)).symm_apply_apply a
    · intro v _; exact (bitsEquiv (2 * n)).apply_symm_apply v
  rw [hcard_eq]
  have hbij : (K ×ˢ (Finset.univ : Finset (Fin (level.val + 1) → ZMod 2))).card =
      (Finset.univ : Finset (Fin (2 * n) → ZMod 2)).card := by
    refine Finset.card_nbij'
      (fun p => p.1 + sec p.2)
      (fun w => (w + sec (T w), T w)) ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · intro w _
      simp only [Finset.mem_coe, Finset.mem_product, K, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true]
      rw [hTadd, hsec]
      funext i
      exact zmod2_add_self (T w i)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, K, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at hp
      have hTp : T (p.1 + sec p.2) = p.2 := by
        rw [hTadd, hp, hsec, zero_add]
      ext k
      · dsimp only
        rw [hTp]
        show (p.1 k + sec p.2 k) + sec p.2 k = p.1 k
        rw [add_assoc, zmod2_add_self, add_zero]
      · exact congrFun hTp k
    · intro w _
      funext k
      show (w k + sec (T w) k) + sec (T w) k = w k
      rw [add_assoc, zmod2_add_self, add_zero]
  rw [Finset.card_product, Finset.card_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, Fintype.card_fin] at hbij
  exact hbij

theorem card_b_prefix (n : ℕ) (level : Fin (n + 1)) (target : Fin (n + 1) → ZMod 2) :
    (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 =>
      ∀ i : Fin (n + 1), i.val ≤ level.val → b i = target i)).card * 2 ^ (level.val + 1) =
    2 ^ (n + 1) := by
  classical
  let B0 : Finset (Fin (n + 1) → ZMod 2) :=
    Finset.univ.filter (fun b => ∀ i : Fin (n + 1), i.val ≤ level.val → b i = target i)
  have hbij : (B0 ×ˢ (Finset.univ : Finset (Fin (level.val + 1) → ZMod 2))).card =
      (Finset.univ : Finset (Fin (n + 1) → ZMod 2)).card := by
    refine Finset.card_nbij'
      (fun p i => if h : i.val ≤ level.val then p.2 ⟨i.val, by omega⟩ else p.1 i)
      (fun b => (fun i => if i.val ≤ level.val then target i else b i,
        fun j => b ⟨j.val, by omega⟩)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro b _
      simp only [Finset.mem_coe, Finset.mem_product, B0, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true]
      intro i hi
      simp [hi]
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_product, B0, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at hp
      apply Prod.ext
      · funext i
        by_cases hi : i.val ≤ level.val
        · simp [hi, hp i hi]
        · simp [hi]
      · funext j
        have hj : j.val ≤ level.val := by omega
        simp [hj]
    · intro b _
      funext i
      by_cases hi : i.val ≤ level.val
      · simp [hi]
      · simp [hi]
  rw [Finset.card_product, Finset.card_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, Fintype.card_fin] at hbij
  exact hbij

end PEqualNP.Outside.L_lib_439_aux

theorem PEqualNP.Outside.L_lib_439 : (∀ (n : Nat) (S : Finset (Fin n → ZMod 2)), S.Nonempty →
  let Seed := Fin (2^(2*n)) × (Fin (n+1) → ZMod 2)
  let hashBit := fun (seed : Seed) (x : Fin n → ZMod 2) (i : Fin (n+1)) =>
    seed.2 i + ∑ j : Fin n, if seed.1.val.testBit (i.val+(n-1-j.val)) then x j else 0
  let zeroPrefix := fun (seed : Seed) (level : Fin (n+1)) (x : Fin n → ZMod 2) =>
    ∀ i : Fin (n+1), i.val ≤ level.val → hashBit seed x i = 0
  ∃ level : Fin (n+1), 2*S.card ≤ 2^(level.val+1) ∧ 2^(level.val+1) < 4*S.card ∧
    Fintype.card Seed ≤ 8 * (Finset.univ.filter (fun draw : Seed =>
      (S.filter (zeroPrefix draw level)).card = 1)).card) := by
  classical
  intro n S hSne Seed hashBit zeroPrefix
  have hMpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hMle : S.card ≤ 2 ^ n := by
    have h1 := Finset.card_le_univ S
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
    exact h1
  let k : ℕ := Nat.log 2 (2 * S.card - 1)
  have hk_le : 2 ^ k ≤ 2 * S.card - 1 := Nat.pow_log_le_self 2 (by omega)
  have hk_lt : 2 * S.card - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) (2 * S.card - 1)
  have hk_bound : k < n + 1 := by
    have h1 : 2 ^ k < 2 ^ (n + 1) := by
      rw [pow_succ']
      omega
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h1
  let level : Fin (n + 1) := ⟨k, hk_bound⟩
  let Q : ℕ := 2 ^ (level.val + 1)
  have hQ_ge : 2 * S.card ≤ Q := by dsimp only [Q, level]; omega
  have hQ_lt : Q < 4 * S.card := by
    dsimp only [Q, level]
    rw [pow_succ']
    omega
  refine ⟨level, hQ_ge, hQ_lt, ?_⟩
  have hSeed_card : Fintype.card Seed = 2 ^ (2 * n) * 2 ^ (n + 1) := by
    simp [Seed, Fintype.card_prod, Fintype.card_fun, ZMod.card]
  let E : (Fin n → ZMod 2) → Finset Seed :=
    fun x => Finset.univ.filter (fun draw : Seed => zeroPrefix draw level x)
  let U : (Fin n → ZMod 2) → Finset Seed :=
    fun x => Finset.univ.filter (fun draw : Seed =>
      zeroPrefix draw level x ∧ ∀ y ∈ S, y ≠ x → ¬ zeroPrefix draw level y)
  let ISO : Finset Seed :=
    Finset.univ.filter (fun draw : Seed => (S.filter (zeroPrefix draw level)).card = 1)
  have hE_card : ∀ x : Fin n → ZMod 2, (E x).card * Q = Fintype.card Seed := by
    intro x
    have hsplit : (E x).card = ∑ a : Fin (2 ^ (2 * n)),
        (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card := by
      have hbi : (E x).card = ((Finset.univ : Finset (Fin (2 ^ (2 * n)))).sigma fun a =>
          Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card := by
        refine Finset.card_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [E, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sigma] at hp ⊢
          exact hp
        · intro p hp
          simp only [E, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sigma] at hp ⊢
          exact hp
        · intro p _; rfl
        · intro p _; rfl
      rw [hbi, Finset.card_sigma]
    rw [hsplit, Finset.sum_mul, hSeed_card]
    have hterm : ∀ a : Fin (2 ^ (2 * n)),
        (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card * Q =
        2 ^ (n + 1) := by
      intro a
      have heq : (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)) =
          (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 =>
            ∀ i : Fin (n + 1), i.val ≤ level.val →
              b i = PEqualNP.Outside.L_lib_439_aux.linPart n
                (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) x i)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, zeroPrefix, hashBit]
        refine forall_congr' fun i => imp_congr_right fun _ => ?_
        rw [← PEqualNP.Outside.L_lib_439_aux.linPart_eq_seed]
        constructor
        · intro h
          have h1 := congrArg (· + PEqualNP.Outside.L_lib_439_aux.linPart n
            (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) x i) h
          simp only [add_assoc, PEqualNP.Outside.L_lib_439_aux.zmod2_add_self, add_zero, zero_add] at h1
          exact h1
        · intro h
          rw [h, PEqualNP.Outside.L_lib_439_aux.zmod2_add_self]
      rw [heq]
      exact PEqualNP.Outside.L_lib_439_aux.card_b_prefix n level _
    simp_rw [hterm]
    simp
  have hPair_card : ∀ x y : Fin n → ZMod 2, x ≠ y →
      (E x ∩ E y).card * Q * Q = Fintype.card Seed := by
    intro x y hne
    let Aker : Finset (Fin (2 ^ (2 * n))) := Finset.univ.filter (fun a =>
      ∀ i : Fin (n + 1), i.val ≤ level.val →
        PEqualNP.Outside.L_lib_439_aux.linPart n (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) x i =
        PEqualNP.Outside.L_lib_439_aux.linPart n (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) y i)
    have hsplit : (E x ∩ E y).card = ∑ a ∈ Aker,
        (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card := by
      have hbi : (E x ∩ E y).card = (Aker.sigma fun a =>
          Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card := by
        refine Finset.card_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [E, Aker, Finset.mem_coe, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_sigma] at hp ⊢
          refine ⟨fun i hi => ?_, hp.1⟩
          have hx := hp.1 i hi
          have hy := hp.2 i hi
          dsimp only [hashBit] at hx hy
          rw [← PEqualNP.Outside.L_lib_439_aux.linPart_eq_seed] at hx hy
          have hxy : p.2 i + PEqualNP.Outside.L_lib_439_aux.linPart n
              (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) p.1) x i =
              p.2 i + PEqualNP.Outside.L_lib_439_aux.linPart n
              (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) p.1) y i := hx.trans hy.symm
          exact add_left_cancel hxy
        · intro p hp
          simp only [E, Aker, Finset.mem_coe, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_sigma] at hp ⊢
          refine ⟨hp.2, fun i hi => ?_⟩
          have hx := hp.2 i hi
          dsimp only [hashBit] at hx ⊢
          rw [← PEqualNP.Outside.L_lib_439_aux.linPart_eq_seed] at hx ⊢
          rw [← hp.1 i hi]
          exact hx
        · intro p _; rfl
        · intro p _; rfl
      rw [hbi, Finset.card_sigma]
    have hterm : ∀ a : Fin (2 ^ (2 * n)),
        (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)).card * Q =
        2 ^ (n + 1) := by
      intro a
      have heq : (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 => zeroPrefix (a, b) level x)) =
          (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 =>
            ∀ i : Fin (n + 1), i.val ≤ level.val →
              b i = PEqualNP.Outside.L_lib_439_aux.linPart n
                (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) x i)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, zeroPrefix, hashBit]
        refine forall_congr' fun i => imp_congr_right fun _ => ?_
        rw [← PEqualNP.Outside.L_lib_439_aux.linPart_eq_seed]
        constructor
        · intro h
          have h1 := congrArg (· + PEqualNP.Outside.L_lib_439_aux.linPart n
            (PEqualNP.Outside.L_lib_439_aux.bitsOf (2 * n) a) x i) h
          simp only [add_assoc, PEqualNP.Outside.L_lib_439_aux.zmod2_add_self, add_zero, zero_add] at h1
          exact h1
        · intro h
          rw [h, PEqualNP.Outside.L_lib_439_aux.zmod2_add_self]
      rw [heq]
      exact PEqualNP.Outside.L_lib_439_aux.card_b_prefix n level _
    have hAker : Aker.card * Q = 2 ^ (2 * n) :=
      PEqualNP.Outside.L_lib_439_aux.card_ker_linPart n level x y hne
    calc (E x ∩ E y).card * Q * Q
        = (∑ a ∈ Aker, (Finset.univ.filter (fun b : Fin (n + 1) → ZMod 2 =>
            zeroPrefix (a, b) level x)).card * Q) * Q := by rw [hsplit, Finset.sum_mul]
      _ = (∑ _a ∈ Aker, 2 ^ (n + 1)) * Q := by simp_rw [hterm]
      _ = (Aker.card * 2 ^ (n + 1)) * Q := by simp
      _ = (Aker.card * Q) * 2 ^ (n + 1) := by ring
      _ = 2 ^ (2 * n) * 2 ^ (n + 1) := by rw [hAker]
      _ = Fintype.card Seed := hSeed_card.symm
  have hU_disj : Set.PairwiseDisjoint (S : Set (Fin n → ZMod 2)) U := by
    intro x _ y _ hxy
    change Disjoint (U x) (U y)
    rw [Finset.disjoint_left]
    intro draw hdx hdy
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hdx hdy
    exact hdx.2 y (by assumption) hxy.symm hdy.1
  have hU_sub : S.biUnion U ⊆ ISO := by
    intro draw hdraw
    obtain ⟨x, hxS, hxU⟩ := Finset.mem_biUnion.mp hdraw
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hxU
    simp only [ISO, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfilt : S.filter (zeroPrefix draw level) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hyS, hyz⟩
        by_contra hne
        exact hxU.2 y hyS hne hyz
      · rintro rfl
        exact ⟨hxS, hxU.1⟩
    rw [hfilt, Finset.card_singleton]
  have hSumU_le : ∑ x ∈ S, (U x).card ≤ ISO.card := by
    rw [← Finset.card_biUnion hU_disj]
    exact Finset.card_le_card hU_sub
  have hEx_le : ∀ x ∈ S, (E x).card ≤ (U x).card + ∑ y ∈ S.erase x, (E x ∩ E y).card := by
    intro x _
    have hsub : E x ⊆ U x ∪ (S.erase x).biUnion (fun y => E x ∩ E y) := by
      intro draw hdraw
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hdraw
      by_cases hall : ∀ y ∈ S, y ≠ x → ¬ zeroPrefix draw level y
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdraw, hall⟩)
      · push_neg at hall
        obtain ⟨y, hyS, hyne, hyz⟩ := hall
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_erase.mpr ⟨hyne, hyS⟩, ?_⟩)
        exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdraw⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hSumE : ∑ x ∈ S, (E x).card ≤
      (∑ x ∈ S, (U x).card) + ∑ x ∈ S, ∑ y ∈ S.erase x, (E x ∩ E y).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hEx_le
  have hMain_ineq : (∑ x ∈ S, (E x).card) * Q * Q ≤
      ISO.card * Q * Q + (∑ x ∈ S, ∑ y ∈ S.erase x, (E x ∩ E y).card) * Q * Q := by
    have h1 := Nat.mul_le_mul_right (Q * Q) (hSumE.trans (Nat.add_le_add_right hSumU_le _))
    rw [Nat.add_mul] at h1
    simpa [Nat.mul_assoc] using h1
  have hLHS : (∑ x ∈ S, (E x).card) * Q * Q = S.card * Q * Fintype.card Seed := by
    rw [Finset.sum_mul, Finset.sum_mul]
    have h1 : ∀ x ∈ S, (E x).card * Q * Q = Q * Fintype.card Seed := fun x _ => by
      rw [hE_card x, Nat.mul_comm]
    rw [Finset.sum_congr rfl h1]
    simp [Nat.mul_assoc]
  have hRHS2 : (∑ x ∈ S, ∑ y ∈ S.erase x, (E x ∩ E y).card) * Q * Q =
      S.card * (S.card - 1) * Fintype.card Seed := by
    rw [Finset.sum_mul, Finset.sum_mul]
    have h1 : ∀ x ∈ S, (∑ y ∈ S.erase x, (E x ∩ E y).card) * Q * Q =
        (S.card - 1) * Fintype.card Seed := by
      intro x hx
      rw [Finset.sum_mul, Finset.sum_mul]
      have h2 : ∀ y ∈ S.erase x, (E x ∩ E y).card * Q * Q = Fintype.card Seed := fun y hy =>
        hPair_card x y (Finset.mem_erase.mp hy).1.symm
      rw [Finset.sum_congr rfl h2]
      simp [Finset.card_erase_of_mem hx]
    rw [Finset.sum_congr rfl h1]
    simp [Nat.mul_assoc]
  rw [hLHS, hRHS2] at hMain_ineq
  have hQpos : 0 < Q * Q := by
    have : 0 < Q := by dsimp only [Q]; positivity
    exact Nat.mul_pos this this
  have hArith : Q * Q * Fintype.card Seed ≤ 8 * ISO.card * (Q * Q) := by
    have hstep1 : S.card * (Q - (S.card - 1)) * Fintype.card Seed ≤ ISO.card * (Q * Q) := by
      have hsub : S.card * (Q - (S.card - 1)) + S.card * (S.card - 1) = S.card * Q := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hsub2 : S.card * (Q - (S.card - 1)) * Fintype.card Seed +
          S.card * (S.card - 1) * Fintype.card Seed = S.card * Q * Fintype.card Seed := by
        rw [← Nat.add_mul, hsub]
      nlinarith
    have hstep2 : Q * Q ≤ 8 * (S.card * (Q - (S.card - 1))) := by
      have h1 : Q ≤ 4 * S.card := le_of_lt hQ_lt
      have h2 : Q ≤ 2 * (Q - (S.card - 1)) := by omega
      nlinarith
    calc Q * Q * Fintype.card Seed
        ≤ 8 * (S.card * (Q - (S.card - 1))) * Fintype.card Seed :=
          Nat.mul_le_mul_right _ hstep2
      _ = 8 * (S.card * (Q - (S.card - 1)) * Fintype.card Seed) := by ring
      _ ≤ 8 * (ISO.card * (Q * Q)) := Nat.mul_le_mul_left 8 hstep1
      _ = 8 * ISO.card * (Q * Q) := by ring
  exact Nat.le_of_mul_le_mul_right (by rw [Nat.mul_comm]; exact hArith) hQpos

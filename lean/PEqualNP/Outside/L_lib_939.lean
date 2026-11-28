import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_939_aux

abbrev F2 := ZMod 2
abbrev WVec (n : ℕ) := Fin n → F2

def nextN {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def prevN {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

def shiftN {n : ℕ} (hn : 0 < n) (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩

def stepBack {n : ℕ} (hn : 0 < n) (i : Fin n) : ℕ → Fin n
  | 0 => i
  | k + 1 => prevN hn (stepBack hn i k)

lemma nextN_prevN {n : ℕ} (hn : 0 < n) (i : Fin n) : nextN hn (prevN hn i) = i := by
  apply Fin.ext
  dsimp only [nextN, prevN]
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0]
    have h0n : 0 + n - 1 = n - 1 := by omega
    rw [h0n, Nat.mod_eq_of_lt (by omega : n - 1 < n), Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      have : i.val + n - 1 = (i.val - 1) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.sub_add_cancel (by omega : 1 ≤ i.val), Nat.mod_eq_of_lt hi]

lemma prevN_nextN {n : ℕ} (hn : 0 < n) (i : Fin n) : prevN hn (nextN hn i) = i := by
  apply Fin.ext
  dsimp only [nextN, prevN]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self]
    have h0n : 0 + n - 1 = n - 1 := by omega
    rw [h0n, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    omega
  · have hlt : i.val + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : i.val + 1 + n - 1 = i.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma nextN_bijective {n : ℕ} (hn : 0 < n) : Function.Bijective (nextN hn) :=
  ⟨fun _ _ h => by have := congrArg (prevN hn) h; rwa [prevN_nextN, prevN_nextN] at this,
   fun i => ⟨prevN hn i, nextN_prevN hn i⟩⟩

lemma stepBack_eq {n : ℕ} (hn : 0 < n) (i : Fin n) (k : ℕ) (hk : k ≤ n) :
    (stepBack hn i k).val = (i.val + n - k) % n := by
  induction k with
  | zero =>
    simp only [stepBack, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    have hprev := ih (by omega)
    dsimp only [stepBack, prevN]
    rw [hprev]
    have hi := i.isLt
    by_cases hge : k + 1 ≤ i.val
    · have h1 : (i.val + n - k) % n = i.val - k := by
        have : i.val + n - k = (i.val - k) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : (i.val + n - (k + 1)) % n = i.val - (k + 1) := by
        have : i.val + n - (k + 1) = (i.val - (k + 1)) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1, h2]
      have : i.val - k + n - 1 = (i.val - (k + 1)) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · by_cases heq : k = i.val
      · have h1 : (i.val + n - k) % n = 0 := by
          have : i.val + n - k = n := by omega
          rw [this, Nat.mod_self]
        have h2 : (i.val + n - (k + 1)) % n = n - 1 := by
          have : i.val + n - (k + 1) = n - 1 := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [h1, h2]
        have h0n : 0 + n - 1 = n - 1 := by omega
        rw [h0n, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      · have hlt : i.val + n - k < n := by omega
        have hlt2 : i.val + n - (k + 1) < n := by omega
        rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2]
        have : i.val + n - k + n - 1 = (i.val + n - (k + 1)) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]

lemma shiftN_stepBack {n : ℕ} (hn : 0 < n) (i : Fin n) (k : ℕ) (hk : k ≤ n) :
    shiftN hn (stepBack hn i k) k = i := by
  apply Fin.ext
  dsimp only [shiftN]
  rw [stepBack_eq hn i k hk]
  rw [Nat.mod_add_mod]
  have : i.val + n - k + k = i.val + n := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma stepBack_surj {n : ℕ} (hn : 0 < n) (i0 x : Fin n) :
    ∃ k < n, stepBack hn i0 k = x := by
  let k := (i0.val + n - x.val) % n
  have hk : k < n := Nat.mod_lt _ hn
  refine ⟨k, hk, ?_⟩
  apply Fin.ext
  rw [stepBack_eq hn i0 k (le_of_lt hk)]
  have hi0 := i0.isLt
  have hx := x.isLt
  by_cases hle : x.val ≤ i0.val
  · have hkeq : k = i0.val - x.val := by
      dsimp only [k]
      have : i0.val + n - x.val = (i0.val - x.val) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hkeq]
    have : i0.val + n - (i0.val - x.val) = x.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · have hkeq : k = i0.val + n - x.val := by
      dsimp only [k]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hkeq]
    have : i0.val + n - (i0.val + n - x.val) = x.val := by omega
    rw [this, Nat.mod_eq_of_lt hx]

lemma nextN_mod2 {n : ℕ} (hn : 0 < n) (heven : n % 2 = 0) (i : Fin n) :
    (nextN hn i).val % 2 = 1 - i.val % 2 := by
  dsimp only [nextN]
  have hi := i.isLt
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self]; omega
  · have hlt : i.val + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

lemma zmod2_cases (x : F2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma card_sub_eq_pow {n : ℕ} (U : Submodule F2 (WVec n)) [Fintype U] :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  have h := Module.card_eq_pow_finrank (K := F2) (V := U)
  simpa [ZMod.card] using h

lemma count_li_tuples {n d : ℕ} (U : Submodule F2 (WVec n)) [Fintype U] (hU : Module.finrank F2 U = d) :
    ∀ k ≤ d,
      (@Finset.filter (Fin k → U) (fun v => LinearIndependent F2 v) (Classical.decPred _) Finset.univ).card =
      ∏ i ∈ Finset.range k, (2 ^ d - 2 ^ i) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    have heq : Finset.univ.filter (fun v : Fin 0 → U => LinearIndependent F2 v) = Finset.univ := by
      ext v; simp
    rw [heq]
    simp
  | succ k ih =>
    intro hkd
    let S := Finset.univ.filter (fun v : Fin (k + 1) → U => LinearIndependent F2 v)
    let Sprev := Finset.univ.filter (fun v : Fin k → U => LinearIndependent F2 v)
    let fiber : (Fin k → U) → Finset U := fun v =>
      Finset.univ.filter (fun w : U => w ∉ Submodule.span F2 (Set.range v))
    have hbij : S.card = (Sprev.sigma fiber).card := by
      refine Finset.card_bij (fun v _ => ⟨fun i : Fin k => v i.castSucc, v (Fin.last k)⟩) ?_ ?_ ?_
      · intro v hv
        have hli : LinearIndependent F2 v := (Finset.mem_filter.mp hv).2
        rw [Finset.mem_sigma]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli.comp Fin.castSucc (Fin.castSucc_injective k)⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        intro hmem
        have hmem' : v (Fin.last k) ∈ Submodule.span F2 (v '' {i : Fin (k + 1) | i ≠ Fin.last k}) := by
          have hset : Set.range (fun i : Fin k => v i.castSucc) = v '' {i : Fin (k + 1) | i ≠ Fin.last k} := by
            ext x
            simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨i, rfl⟩; exact ⟨i.castSucc, Fin.castSucc_ne_last i, rfl⟩
            · rintro ⟨i, hne, rfl⟩
              exact ⟨i.castPred hne, by simp⟩
          rwa [← hset]
        exact hli.notMem_span_image (by simp) hmem'
      · intro v1 _ v2 _ heq
        have h1 : (fun i : Fin k => v1 i.castSucc) = (fun i : Fin k => v2 i.castSucc) :=
          congrArg Sigma.fst heq
        have h2 : v1 (Fin.last k) = v2 (Fin.last k) := by
          have := congrArg Sigma.snd heq
          simpa using this
        funext i
        exact Fin.lastCases h2 (fun j => congrFun h1 j) i
      · intro p hp
        rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
        have hli' : LinearIndependent F2 p.1 := (Finset.mem_filter.mp hp1).2
        have hnot : p.2 ∉ Submodule.span F2 (Set.range p.1) := (Finset.mem_filter.mp hp2).2
        refine ⟨Fin.snoc p.1 p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [Fintype.linearIndependent_iff]
          intro g hg i
          rw [Fin.sum_univ_castSucc] at hg
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
          have hlast0 : g (Fin.last k) = 0 := by
            by_contra hne
            have h1 : g (Fin.last k) = 1 := by
              rcases zmod2_cases (g (Fin.last k)) with h0 | h1
              · exact (hne h0).elim
              · exact h1
            rw [h1, one_smul] at hg
            have hp2_eq : p.2 = - ∑ j : Fin k, g j.castSucc • p.1 j := eq_neg_of_add_eq_zero_right hg
            apply hnot
            rw [hp2_eq]
            exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun j _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
          rw [hlast0, zero_smul, add_zero] at hg
          have hrest : ∀ j : Fin k, g j.castSucc = 0 := Fintype.linearIndependent_iff.mp hli' _ hg
          exact Fin.lastCases hlast0 hrest i
        · apply Sigma.ext
          · funext j; simp
          · simp
    have hfib : ∀ v ∈ Sprev, (fiber v).card = 2 ^ d - 2 ^ k := by
      intro v hv
      have hli : LinearIndependent F2 v := (Finset.mem_filter.mp hv).2
      let Sp := Submodule.span F2 (Set.range v)
      have hSp_rank : Module.finrank F2 Sp = k := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      have hSp_card : (Finset.univ.filter (fun w : U => w ∈ Sp)).card = 2 ^ k := by
        have h1 : (Finset.univ.filter (fun w : U => w ∈ Sp)).card = Fintype.card Sp := by
          rw [Fintype.card_subtype]
        rw [h1, Module.card_eq_pow_finrank (K := F2) (V := Sp), hSp_rank]
        simp [ZMod.card]
      have hU_card : (Finset.univ : Finset U).card = 2 ^ d := by
        rw [Finset.card_univ, card_sub_eq_pow U, hU]
      have hcompl : (Finset.univ.filter (fun w : U => w ∈ Sp)).card + (fiber v).card = (Finset.univ : Finset U).card := by
        dsimp only [fiber, Sp]
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
        congr 1
        ext w; simp [em]
      omega
    rw [hbij, Finset.card_sigma, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
      ih (by omega), Finset.prod_range_succ]

lemma basis_bound_for_subspace {n d : ℕ} (V : Submodule F2 (WVec n))
    (A : Finset (Submodule F2 (WVec n)))
    (hA : ∀ U ∈ A, U ≤ V ∧ Module.finrank F2 U = d) :
    (∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)) * A.card ≤ (2 ^ d) ^ Module.finrank F2 V := by
  classical
  let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i)
  let basesOf : Submodule F2 (WVec n) → Finset (Fin d → V) := fun U =>
    Finset.univ.filter (fun v : Fin d → V =>
      LinearIndependent F2 (fun i => (v i).val) ∧
      Submodule.span F2 (Set.range (fun i => (v i).val)) = U)
  have hdisj : Set.PairwiseDisjoint (↑A : Set (Submodule F2 (WVec n))) basesOf := by
    intro U1 _ U2 _ hne
    exact Finset.disjoint_left.mpr (fun v h1 h2 =>
      hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2))
  have hfib_ge : ∀ U ∈ A, B ≤ (basesOf U).card := by
    intro U hU
    rcases hA U hU with ⟨hUV, hUrk⟩
    have hcnt := count_li_tuples U hUrk d le_rfl
    dsimp only [B]
    rw [← hcnt]
    let TU := Finset.univ.filter (fun v : Fin d → U => LinearIndependent F2 v)
    have hinj : Set.InjOn (fun (v : Fin d → U) (i : Fin d) => (⟨(v i).val, hUV (v i).2⟩ : V)) (TU : Set (Fin d → U)) := by
      intro v1 _ v2 _ heq
      funext i
      exact Subtype.ext (congrArg (Subtype.val : V → WVec n) (congrFun heq i))
    have hsub : TU.image (fun (v : Fin d → U) (i : Fin d) => (⟨(v i).val, hUV (v i).2⟩ : V)) ⊆ basesOf U := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
      have hliU : LinearIndependent F2 v := (Finset.mem_filter.mp hv).2
      have hliW : LinearIndependent F2 (fun i => (v i).val) :=
        hliU.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hliW, ?_⟩
      have hle : Submodule.span F2 (Set.range (fun i => (v i).val)) ≤ U :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (v i).2)
      have hrk : Module.finrank F2 (Submodule.span F2 (Set.range (fun i => (v i).val))) = Module.finrank F2 U := by
        rw [finrank_span_eq_card hliW, Fintype.card_fin, hUrk]
      exact Submodule.eq_of_le_of_finrank_eq hle hrk
    calc TU.card = (TU.image (fun (v : Fin d → U) (i : Fin d) => (⟨(v i).val, hUV (v i).2⟩ : V))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (basesOf U).card := Finset.card_le_card hsub
  have hsum : B * A.card ≤ (A.biUnion basesOf).card := by
    rw [Finset.card_biUnion hdisj]
    calc B * A.card = A.sum (fun _ => B) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ A.sum (fun U => (basesOf U).card) := Finset.sum_le_sum hfib_ge
  have huniv : (A.biUnion basesOf).card ≤ (2 ^ d) ^ Module.finrank F2 V := by
    calc (A.biUnion basesOf).card ≤ Fintype.card (Fin d → V) := Finset.card_le_univ _
      _ = (Fintype.card V) ^ d := by rw [Fintype.card_fun, Fintype.card_fin]
      _ = (2 ^ Module.finrank F2 V) ^ d := by rw [card_sub_eq_pow V]
      _ = (2 ^ d) ^ Module.finrank F2 V := by rw [← pow_mul, mul_comm, pow_mul]
  exact hsum.trans huniv

def checkH {n : ℕ} (i : Fin n) (b : Fin 4) : F2 :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) then 1 else 0

def runSpace {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Submodule F2 (WVec n) where
  carrier := {x : WVec n | (∀ i ∉ S, x i = 0) ∧ (∀ i : Fin n, i ∈ S → nextN hn i ∈ S → x i = x (nextN hn i))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩; add_mem' := fun hx hy =>
    ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
     fun i h1 h2 => by simp [hx.2 i h1 h2, hy.2 i h1 h2]⟩
  smul_mem' := fun c _ hx =>
    ⟨fun i hi => by simp [hx.1 i hi],
     fun i h1 h2 => by simp [hx.2 i h1 h2]⟩

def checkSpace {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Submodule F2 (WVec n) where
  carrier := {x : WVec n | x ∈ runSpace hn S ∧ ∀ b : Fin 4, (∑ i : Fin n, checkH i b * x i) = 0}
  zero_mem' := ⟨(runSpace hn S).zero_mem, fun _ => by simp⟩; add_mem' := fun {x y} hx hy =>
    ⟨(runSpace hn S).add_mem hx.1 hy.1, fun b => by
      have h1 : (∑ i : Fin n, checkH i b * (x + y) i) =
          (∑ i : Fin n, checkH i b * x i) + (∑ i : Fin n, checkH i b * y i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by simp [mul_add])
      rw [h1, hx.2 b, hy.2 b, add_zero]⟩
  smul_mem' := fun c {x} hx =>
    ⟨(runSpace hn S).smul_mem c hx.1, fun b => by
      have h1 : (∑ i : Fin n, checkH i b * (c • x) i) = c * ∑ i : Fin n, checkH i b * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by simp [smul_eq_mul]; ring)
      rw [h1, hx.2 b, mul_zero]⟩

lemma good_le_checkSpace {n : ℕ} (hn : 0 < n) (U : Submodule F2 (WVec n))
    (hchk : ∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin n, checkH i b * x i) = 0)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextN hn i) = x (nextN hn i) * y i) :
    let S := @Finset.filter (Fin n) (fun i => ∃ x ∈ U, x i ≠ 0) (Classical.decPred _) Finset.univ
    U ≤ checkSpace hn S := by
  intro S x hx
  have hmemS : ∀ i : Fin n, i ∈ S ↔ ∃ y ∈ U, y i ≠ 0 := fun i => by
    dsimp only [S]; simp
  refine ⟨⟨?_, ?_⟩, hchk x hx⟩
  · intro i hi
    by_contra hne
    exact hi ((hmemS i).mpr ⟨x, hx, hne⟩)
  · intro i hi1 hi2
    rcases (hmemS i).mp hi1 with ⟨y1, hy1U, hy1ne⟩
    rcases (hmemS (nextN hn i)).mp hi2 with ⟨y2, hy2U, hy2ne⟩
    have hy1 : y1 i = 1 := (zmod2_cases (y1 i)).resolve_left hy1ne
    have hy2 : y2 (nextN hn i) = 1 := (zmod2_cases (y2 (nextN hn i))).resolve_left hy2ne
    rcases zmod2_cases (x i) with hx1 | hx1 <;> rcases zmod2_cases (x (nextN hn i)) with hx2 | hx2
    · rw [hx1, hx2]
    · have h := hiso x hx y1 hy1U i
      rw [hx1, hx2, hy1] at h; simp at h
    · have h := hiso x hx y2 hy2U i
      rw [hx1, hx2, hy2] at h; simp at h
    · rw [hx1, hx2]

lemma supp_ne_univ_of_finrank_ge_two {n : ℕ} (hn : 0 < n) (U : Submodule F2 (WVec n))
    (hd : 2 ≤ Module.finrank F2 U)
    (hchk : ∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin n, checkH i b * x i) = 0)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextN hn i) = x (nextN hn i) * y i) :
    (@Finset.filter (Fin n) (fun i => ∃ x ∈ U, x i ≠ 0) (Classical.decPred _) Finset.univ) ≠ Finset.univ := by
  intro huniv
  have hle := good_le_checkSpace hn U hchk hiso
  rw [huniv] at hle
  have hU_const : U ≤ Submodule.span F2 {(fun _ : Fin n => (1 : F2))} := by
    intro x hx
    have hstep : ∀ i : Fin n, x i = x (nextN hn i) := fun i =>
      (hle hx).1.2 i (Finset.mem_univ _) (Finset.mem_univ _)
    have hconst : ∀ k : ℕ, x (shiftN hn ⟨0, hn⟩ k) = x ⟨0, hn⟩ := by
      intro k
      induction k with
      | zero => simp [shiftN, Nat.mod_eq_of_lt hn]
      | succ k ih =>
        have hnext : nextN hn (shiftN hn ⟨0, hn⟩ k) = shiftN hn ⟨0, hn⟩ (k + 1) := by
          apply Fin.ext; dsimp only [nextN, shiftN]; rw [Nat.mod_add_mod, add_assoc]
        rw [← hnext, ← hstep, ih]
    have hx_eq : x = x ⟨0, hn⟩ • (fun _ : Fin n => (1 : F2)) := by
      funext i
      have hi : shiftN hn ⟨0, hn⟩ i.val = i := by
        apply Fin.ext; dsimp only [shiftN]; simp [Nat.mod_eq_of_lt i.isLt]
      rw [← hi, hconst i.val]
      simp
    rw [hx_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hrk1 : Module.finrank F2 (Submodule.span F2 {(fun _ : Fin n => (1 : F2))}) ≤ 1 := by
    calc Module.finrank F2 (Submodule.span F2 {(fun _ : Fin n => (1 : F2))})
        ≤ ({(fun _ : Fin n => (1 : F2))} : Finset (WVec n)).card := by
            simpa using finrank_span_le_card ({(fun _ : Fin n => (1 : F2))} : Set (WVec n))
      _ = 1 := Finset.card_singleton _
  have hrkU : Module.finrank F2 U ≤ Module.finrank F2 (Submodule.span F2 {(fun _ : Fin n => (1 : F2))}) :=
    Submodule.finrank_mono hU_const
  exact absurd (hrkU.trans hrk1) (by omega)

def runEnds {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i ∈ S ∧ nextN hn i ∉ S)

lemma finrank_runSpace_le {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (hSne : S ≠ Finset.univ) :
    Module.finrank F2 (runSpace hn S) ≤ (runEnds hn S).card := by
  have hex : ∃ i0 : Fin n, i0 ∉ S := by
    by_contra hall
    push Not at hall
    exact hSne (Finset.eq_univ_iff_forall.mpr hall)
  rcases hex with ⟨i0, hi0⟩
  let evalE : runSpace hn S →ₗ[F2] (runEnds hn S → F2) :=
    { toFun := fun x e => x.val e.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective evalE := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hzeroE : ∀ i ∈ runEnds hn S, x.val i = 0 := fun i hi =>
      congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
    have hback : ∀ k : ℕ, x.val (stepBack hn i0 k) = 0 := by
      intro k
      induction k with
      | zero => exact x.2.1 i0 hi0
      | succ k ih =>
        let u := stepBack hn i0 (k + 1)
        have hnu : nextN hn u = stepBack hn i0 k := nextN_prevN hn (stepBack hn i0 k)
        by_cases huS : u ∈ S
        · by_cases hnuS : nextN hn u ∈ S
          · rw [x.2.2 u huS hnuS, hnu, ih]
          · exact hzeroE u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS, hnuS⟩)
        · exact x.2.1 u huS
    apply Subtype.ext
    funext i
    rcases stepBack_surj hn i0 i with ⟨k, _, rfl⟩
    exact hback k
  calc Module.finrank F2 (runSpace hn S) ≤ Module.finrank F2 (runEnds hn S → F2) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = (runEnds hn S).card := by simp [Fintype.card_coe]

lemma finrank_checkSpace_le_sub_two {t : ℕ} (ht : 4 ≤ t) (S : Finset (Fin (6 * t)))
    (hSne : S ≠ Finset.univ) (b : Fin 2)
    (hwin : ∃ i : Fin (6 * t), ∀ j : Fin 24,
      shiftN (by omega : 0 < 6 * t) i j.val ∈ S ↔ (shiftN (by omega : 0 < 6 * t) i j.val).val % 2 = b.val) :
    Module.finrank F2 (checkSpace (by omega : 0 < 6 * t) S) + 2 ≤ (runEnds (by omega : 0 < 6 * t) S).card := by
  have hn : 0 < 6 * t := by omega
  have heven : (6 * t) % 2 = 0 := by omega
  rcases hwin with ⟨i0, hi0⟩
  have hsingle_mem : ∀ j : ℕ, 1 ≤ j → j ≤ 22 →
      (shiftN hn i0 j).val % 2 = b.val →
      Pi.single (shiftN hn i0 j) (1 : F2) ∈ runSpace hn S := by
    intro j hj1 hj2 hpar
    let u := shiftN hn i0 j
    have huS : u ∈ S := (hi0 ⟨j, by omega⟩).mpr hpar
    have hprev_eq : prevN hn u = shiftN hn i0 (j - 1) := by
      have : nextN hn (shiftN hn i0 (j - 1)) = u := by
        apply Fin.ext; dsimp only [nextN, shiftN, u]
        rw [Nat.mod_add_mod, show i0.val + (j - 1) + 1 = i0.val + j by omega]
      rw [← this, prevN_nextN]
    have hnext_eq : nextN hn u = shiftN hn i0 (j + 1) := by
      apply Fin.ext; dsimp only [nextN, shiftN, u]
      rw [Nat.mod_add_mod, add_assoc]
    have hprev_not : prevN hn u ∉ S := by
      rw [hprev_eq]
      intro hmem
      have hp : (shiftN hn i0 (j - 1)).val % 2 = b.val := (hi0 ⟨j - 1, by omega⟩).mp hmem
      have hnp := nextN_mod2 hn heven (prevN hn u)
      rw [nextN_prevN, hprev_eq] at hnp
      dsimp only [u] at hnp
      omega
    have hnext_not : nextN hn u ∉ S := by
      rw [hnext_eq]
      intro hmem
      have hp : (shiftN hn i0 (j + 1)).val % 2 = b.val := (hi0 ⟨j + 1, by omega⟩).mp hmem
      have hnp := nextN_mod2 hn heven u
      rw [hnext_eq] at hnp
      dsimp only [u] at hnp
      omega
    change Pi.single u (1 : F2) ∈ runSpace hn S
    refine ⟨?_, ?_⟩
    · intro i hi
      have hne : i ≠ u := fun h => hi (h ▸ huS)
      simp [Pi.single_eq_of_ne hne]
    · intro i hi1 hi2
      have hne1 : i ≠ u := fun h => hnext_not (h ▸ hi2)
      have hne2 : nextN hn i ≠ u := fun h => hprev_not (by rw [← h, prevN_nextN]; exact hi1)
      simp [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2]
  have hex_mod6 : ∀ r : ℕ, r < 6 → ∃ j : ℕ, 2 ≤ j ∧ j ≤ 7 ∧ (shiftN hn i0 j).val % 6 = r := by
    intro r hr
    let j := 2 + (r + 6 - (i0.val + 2) % 6) % 6
    refine ⟨j, by omega, by omega, ?_⟩
    dsimp only [shiftN]
    have hmod : ((i0.val + j) % (6 * t)) % 6 = (i0.val + j) % 6 := Nat.mod_mod_of_dvd _ (dvd_mul_right 6 t)
    rw [hmod]
    dsimp only [j]
    omega
  rcases hex_mod6 b.val (by omega) with ⟨j0, hj0a, hj0b, hj0m⟩
  rcases hex_mod6 (b.val + 2) (by omega) with ⟨j1, hj1a, hj1b, hj1m⟩
  let u0 := shiftN hn i0 j0
  let u1 := shiftN hn i0 j1
  have hu0_par : u0.val % 2 = b.val := by have := b.isLt; omega
  have hu1_par : u1.val % 2 = b.val := by have := b.isLt; omega
  have hu0_mem : Pi.single u0 (1 : F2) ∈ runSpace hn S := hsingle_mem j0 (by omega) (by omega) hu0_par
  have hu1_mem : Pi.single u1 (1 : F2) ∈ runSpace hn S := hsingle_mem j1 (by omega) (by omega) hu1_par
  let Φ : runSpace hn S →ₗ[F2] (Fin 4 → F2) :=
    { toFun := fun x c => ∑ i : Fin (6 * t), checkH i c * x.val i
      map_add' := fun x y => by
        funext c
        dsimp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by simp [mul_add])
      map_smul' := fun r x => by
        funext c
        dsimp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by simp [smul_eq_mul]; ring) }
  have hPhi_single : ∀ (u : Fin (6 * t)) (hu : Pi.single u (1 : F2) ∈ runSpace hn S) (c : Fin 4),
      Φ ⟨Pi.single u 1, hu⟩ c = checkH u c := by
    intro u hu c
    dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single u]
    · simp
    · intro i _ hne; simp [Pi.single_eq_of_ne hne]
    · intro h; exact (h (Finset.mem_univ u)).elim
  let v0 : Fin 4 → F2 := Φ ⟨Pi.single u0 1, hu0_mem⟩
  let v1 : Fin 4 → F2 := Φ ⟨Pi.single u1 1, hu1_mem⟩
  let c0 : Fin 4 := ⟨2 * b.val, by omega⟩
  let c1 : Fin 4 := ⟨2 * b.val + 1, by omega⟩
  have hv0c0 : v0 c0 = 1 := by
    dsimp only [v0]; rw [hPhi_single]; dsimp only [checkH, c0]
    have hb := b.isLt; have h1 : u0.val % 2 = (2 * b.val) / 2 := by omega
    have h2 : u0.val / 2 % 3 = (2 * b.val) % 2 := by omega
    simp [h1, h2]
  have hv0c1 : v0 c1 = 0 := by
    dsimp only [v0]; rw [hPhi_single]; dsimp only [checkH, c1]
    have hb := b.isLt
    split_ifs with hc
    · omega
    · rfl
  have hv1c0 : v1 c0 = 0 := by
    dsimp only [v1]; rw [hPhi_single]; dsimp only [checkH, c0]
    have hb := b.isLt
    split_ifs with hc
    · omega
    · rfl
  have hv1c1 : v1 c1 = 1 := by
    dsimp only [v1]; rw [hPhi_single]; dsimp only [checkH, c1]
    have hb := b.isLt; have h1 : u1.val % 2 = (2 * b.val + 1) / 2 := by omega
    have h2 : u1.val / 2 % 3 = (2 * b.val + 1) % 2 := by omega
    simp [h1, h2]
  have hli_range : LinearIndependent F2 (fun k : Fin 2 =>
      (⟨if k = 0 then v0 else v1, by
        split_ifs
        · exact ⟨⟨Pi.single u0 1, hu0_mem⟩, rfl⟩
        · exact ⟨⟨Pi.single u1 1, hu1_mem⟩, rfl⟩⟩ : LinearMap.range Φ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h0 := congrFun (congrArg Subtype.val hg) c0
    have h1 := congrFun (congrArg Subtype.val hg) c1
    simp only [Fin.sum_univ_two, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff,
      Submodule.coe_add, Submodule.coe_smul_of_tower, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hv0c0, hv1c0, hv0c1, hv1c1, mul_one, mul_zero, add_zero, zero_add,
      Submodule.coe_zero, Pi.zero_apply] at h0 h1
    fin_cases k
    · exact h0
    · exact h1
  have hrank_range : 2 ≤ Module.finrank F2 (LinearMap.range Φ) := by
    have h := hli_range.fintype_card_le_finrank
    simpa using h
  have hker_eq : Module.finrank F2 (LinearMap.ker Φ) = Module.finrank F2 (checkSpace hn S) := by
    let e : LinearMap.ker Φ ≃ₗ[F2] checkSpace hn S :=
      { toFun := fun x => ⟨x.1.1, x.1.2, fun c => congrFun (LinearMap.mem_ker.mp x.2) c⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, LinearMap.mem_ker.mpr (funext x.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hle := finrank_runSpace_le hn S hSne
  omega

lemma card_rise_eq_card_fall {n : ℕ} (hn : 0 < n) (g : Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin n => g i = true ∧ g (nextN hn i) = false)).card =
    (Finset.univ.filter (fun i : Fin n => g i = false ∧ g (nextN hn i) = true)).card := by
  have hsum : (∑ i : Fin n, ((if g i then (1 : ℤ) else 0) - (if g (nextN hn i) then (1 : ℤ) else 0))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hbij : (∑ i : Fin n, if g (nextN hn i) then (1 : ℤ) else 0) =
        ∑ i : Fin n, if g i then (1 : ℤ) else 0 := by
      refine Finset.sum_bij (fun i _ => nextN hn i) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => (nextN_bijective hn).1 h)
        (fun i _ => ⟨prevN hn i, Finset.mem_univ _, nextN_prevN hn i⟩)
        (fun _ _ => rfl)
    rw [hbij, sub_self]
  have hrew : ∀ i : Fin n,
      ((if g i then (1 : ℤ) else 0) - (if g (nextN hn i) then (1 : ℤ) else 0)) =
      (if g i = true ∧ g (nextN hn i) = false then (1 : ℤ) else 0) -
      (if g i = false ∧ g (nextN hn i) = true then (1 : ℤ) else 0) := by
    intro i; cases g i <;> cases g (nextN hn i) <;> decide
  rw [Finset.sum_congr rfl (fun i _ => hrew i), Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_boole] at hsum
  omega

def phaseBit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Bool :=
  decide (i ∈ S) == decide (i.val % 2 = 0)

def phaseStarts {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (target : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => phaseBit S (prevN hn i) ≠ target ∧ phaseBit S i = target)

lemma phaseStarts_card_eq {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    (phaseStarts hn S true).card = (phaseStarts hn S false).card := by
  have h1 : (phaseStarts hn S true).card =
      (Finset.univ.filter (fun i : Fin n => phaseBit S i = false ∧ phaseBit S (nextN hn i) = true)).card := by
    refine Finset.card_bij (fun i _ => prevN hn i) ?_ ?_ ?_
    · intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨hpre, hcur⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, by rwa [nextN_prevN]⟩
      cases h : phaseBit S (prevN hn i)
      · rfl
      · exact (hpre h).elim
    · intro a _ b _ h; have := congrArg (nextN hn) h; rwa [nextN_prevN, nextN_prevN] at this
    · intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨h1, h2⟩
      refine ⟨nextN hn i, ?_, prevN_nextN hn i⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h2⟩
      rw [prevN_nextN, h1]; decide
  have h2 : (phaseStarts hn S false).card =
      (Finset.univ.filter (fun i : Fin n => phaseBit S i = true ∧ phaseBit S (nextN hn i) = false)).card := by
    refine Finset.card_bij (fun i _ => prevN hn i) ?_ ?_ ?_
    · intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨hpre, hcur⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, by rwa [nextN_prevN]⟩
      cases h : phaseBit S (prevN hn i)
      · exact (hpre h).elim
      · rfl
    · intro a _ b _ h; have := congrArg (nextN hn) h; rwa [nextN_prevN, nextN_prevN] at this
    · intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨h1, h2⟩
      refine ⟨nextN hn i, ?_, prevN_nextN hn i⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h2⟩
      rw [prevN_nextN, h1]; decide
  rw [h1, h2, card_rise_eq_card_fall hn (phaseBit S)]

lemma runEnds_add_phaseStarts {n : ℕ} (hn : 0 < n) (heven : n % 2 = 0)
    (S : Finset (Fin n)) (target : Bool) :
    2 * (runEnds hn S).card + 2 * (phaseStarts hn S target).card = n := by
  have hpar : ∀ i : Fin n,
      (phaseBit S i = phaseBit S (nextN hn i)) ↔ (decide (i ∈ S) ≠ decide (nextN hn i ∈ S)) := by
    intro i
    have hne : decide ((nextN hn i).val % 2 = 0) ≠ decide (i.val % 2 = 0) := by
      have h := nextN_mod2 hn heven i
      have hmod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hmod with h0 | h1
      · simp [h0, h]
      · have h0 : (nextN hn i).val % 2 = 0 := by omega
        simp [h0, h1]
    dsimp only [phaseBit]
    cases decide (i ∈ S) <;> cases decide (nextN hn i ∈ S) <;>
      cases h1 : decide (i.val % 2 = 0) <;> cases h2 : decide ((nextN hn i).val % 2 = 0) <;>
      simp_all
  have hpart : (Finset.univ.filter (fun i : Fin n => phaseBit S i = phaseBit S (nextN hn i))).card +
      (Finset.univ.filter (fun i : Fin n => phaseBit S i ≠ phaseBit S (nextN hn i))).card = n := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
    have : Finset.univ.filter (fun i : Fin n => phaseBit S i = phaseBit S (nextN hn i)) ∪
        Finset.univ.filter (fun i : Fin n => phaseBit S i ≠ phaseBit S (nextN hn i)) = Finset.univ := by
      ext i; simp [em]
    rw [this]; simp
  have hsame : (Finset.univ.filter (fun i : Fin n => phaseBit S i = phaseBit S (nextN hn i))).card =
      2 * (runEnds hn S).card := by
    have heq : Finset.univ.filter (fun i : Fin n => phaseBit S i = phaseBit S (nextN hn i)) =
        Finset.univ.filter (fun i : Fin n => decide (i ∈ S) = true ∧ decide (nextN hn i ∈ S) = false) ∪
        Finset.univ.filter (fun i : Fin n => decide (i ∈ S) = false ∧ decide (nextN hn i ∈ S) = true) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hpar i]
      cases decide (i ∈ S) <;> cases decide (nextN hn i ∈ S) <;> decide
    have hdisj : Disjoint
        (Finset.univ.filter (fun i : Fin n => decide (i ∈ S) = true ∧ decide (nextN hn i ∈ S) = false))
        (Finset.univ.filter (fun i : Fin n => decide (i ∈ S) = false ∧ decide (nextN hn i ∈ S) = true)) :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => Bool.false_ne_true (h2.1.symm.trans h1.1))
    rw [heq, Finset.card_union_of_disjoint hdisj, ← card_rise_eq_card_fall hn (fun i => decide (i ∈ S)), ← two_mul]
    have hre : Finset.univ.filter (fun i : Fin n => decide (i ∈ S) = true ∧ decide (nextN hn i ∈ S) = false) =
        runEnds hn S := by
      ext i; simp [runEnds]
    rw [hre]
  have hdiff : (Finset.univ.filter (fun i : Fin n => phaseBit S i ≠ phaseBit S (nextN hn i))).card =
      2 * (phaseStarts hn S target).card := by
    have heq : Finset.univ.filter (fun i : Fin n => phaseBit S i ≠ phaseBit S (nextN hn i)) =
        Finset.univ.filter (fun i : Fin n => phaseBit S i = true ∧ phaseBit S (nextN hn i) = false) ∪
        Finset.univ.filter (fun i : Fin n => phaseBit S i = false ∧ phaseBit S (nextN hn i) = true) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      cases phaseBit S i <;> cases phaseBit S (nextN hn i) <;> decide
    have hdisj : Disjoint
        (Finset.univ.filter (fun i : Fin n => phaseBit S i = true ∧ phaseBit S (nextN hn i) = false))
        (Finset.univ.filter (fun i : Fin n => phaseBit S i = false ∧ phaseBit S (nextN hn i) = true)) :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => Bool.false_ne_true (h2.1.symm.trans h1.1))
    rw [heq, Finset.card_union_of_disjoint hdisj, ← card_rise_eq_card_fall hn (phaseBit S), ← two_mul]
    have hst : (phaseStarts hn S false).card =
        (Finset.univ.filter (fun i : Fin n => phaseBit S i = true ∧ phaseBit S (nextN hn i) = false)).card := by
      refine Finset.card_bij (fun i _ => prevN hn i) ?_ ?_ ?_
      · intro i hi
        rcases (Finset.mem_filter.mp hi).2 with ⟨hpre, hcur⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, by rwa [nextN_prevN]⟩
        cases h : phaseBit S (prevN hn i)
        · exact (hpre h).elim
        · rfl
      · intro x _ y _ h; have := congrArg (nextN hn) h; rwa [nextN_prevN, nextN_prevN] at this
      · intro i hi
        rcases (Finset.mem_filter.mp hi).2 with ⟨h1, h2⟩
        refine ⟨nextN hn i, ?_, prevN_nextN hn i⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, h2⟩
        rw [prevN_nextN, h1]; decide
    cases target
    · rw [hst]
    · rw [phaseStarts_card_eq, hst]
  omega

lemma phaseStarts_pos_of_mixed {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (hmix : ∀ b : Fin 2, ∃ i ∈ S, i.val % 2 = b.val) (target : Bool) :
    1 ≤ (phaseStarts hn S target).card := by
  by_contra h0
  have hempty : phaseStarts hn S target = ∅ := Finset.card_eq_zero.mp (by omega)
  have hempty_other : phaseStarts hn S (!target) = ∅ := by
    have heq := phaseStarts_card_eq hn S
    cases target <;> simp only [Bool.not_false, Bool.not_true] at * <;>
      exact Finset.card_eq_zero.mp (by omega)
  have hconst : ∀ i : Fin n, phaseBit S i = phaseBit S (prevN hn i) := by
    intro i
    by_contra hne
    by_cases ht : phaseBit S i = target
    · have hm : i ∈ phaseStarts hn S target :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [← ht, ne_comm], ht⟩
      rw [hempty] at hm; simp at hm
    · have hnt : phaseBit S i = !target := by
        cases h : phaseBit S i <;> cases target <;> simp_all
      have hm : i ∈ phaseStarts hn S (!target) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [← hnt, ne_comm], hnt⟩
      rw [hempty_other] at hm; simp at hm
  have hall : ∀ k : ℕ, phaseBit S (stepBack hn ⟨0, hn⟩ k) = phaseBit S ⟨0, hn⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      dsimp only [stepBack]
      rw [← hconst, ih]
  have hall' : ∀ i : Fin n, phaseBit S i = phaseBit S ⟨0, hn⟩ := by
    intro i
    rcases stepBack_surj hn ⟨0, hn⟩ i with ⟨k, _, rfl⟩
    exact hall k
  cases hval : phaseBit S ⟨0, hn⟩
  · rcases hmix 0 with ⟨i, hiS, hipar⟩
    have hi := hall' i
    rw [hval] at hi
    dsimp only [phaseBit] at hi
    simp [hiS, hipar] at hi
  · rcases hmix 1 with ⟨i, hiS, hipar⟩
    have hi := hall' i
    rw [hval] at hi
    dsimp only [phaseBit] at hi
    simp [hiS, hipar] at hi

lemma window_iff_phaseBit {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (b : Fin 2) :
    (∃ i : Fin n, ∀ j : Fin 24, shiftN hn i j.val ∈ S ↔ (shiftN hn i j.val).val % 2 = b.val) ↔
    ∃ i : Fin n, ∀ j : Fin 24, phaseBit S (shiftN hn i j.val) = decide (b.val = 0) := by
  refine exists_congr (fun i => forall_congr' (fun j => ?_))
  dsimp only [phaseBit]
  have hb := b.isLt
  have hmod : (shiftN hn i j.val).val % 2 = 0 ∨ (shiftN hn i j.val).val % 2 = 1 := by omega
  by_cases hS : shiftN hn i j.val ∈ S <;> rcases hmod with h0 | h1 <;> fin_cases b <;>
    simp_all

lemma no_window_cover {n : ℕ} (hn24 : 24 ≤ n) (S : Finset (Fin n)) (target : Bool)
    (hnowin : ¬ ∃ i : Fin n, ∀ j : Fin 24, phaseBit S (shiftN (by omega : 0 < n) i j.val) = target) :
    ∀ x : Fin n, phaseBit S x = target →
      ∃ i ∈ phaseStarts (by omega : 0 < n) S target,
        (x.val + n - i.val) % n < 23 ∧
        ∀ r ≤ (x.val + n - i.val) % n, phaseBit S (shiftN (by omega : 0 < n) i r) = target := by
  have hn : 0 < n := by omega
  intro x hx
  have hex : ∃ m : ℕ, m < 24 ∧ phaseBit S (stepBack hn x m) ≠ target := by
    by_contra hall
    push Not at hall
    apply hnowin
    refine ⟨stepBack hn x 23, fun j => ?_⟩
    have hshift : shiftN hn (stepBack hn x 23) j.val = stepBack hn x (23 - j.val) := by
      apply Fin.ext
      dsimp only [shiftN]
      rw [stepBack_eq hn x 23 (by omega), stepBack_eq hn x (23 - j.val) (by omega), Nat.mod_add_mod]
      have hj := j.isLt
      have : x.val + n - 23 + j.val = x.val + n - (23 - j.val) := by omega
      rw [this]
    rw [hshift]
    exact hall (23 - j.val) (by omega)
  classical
  let m0 := Nat.find hex
  have hm0_spec : m0 < 24 ∧ phaseBit S (stepBack hn x m0) ≠ target := Nat.find_spec hex
  have hm0_pos : 1 ≤ m0 := by
    by_contra h0
    have hm00 : m0 = 0 := by omega
    rw [hm00] at hm0_spec
    exact hm0_spec.2 hx
  let i := stepBack hn x (m0 - 1)
  have hi_eq : phaseBit S i = target := by
    by_contra hne
    exact Nat.find_min hex (show m0 - 1 < m0 by omega) ⟨by omega, hne⟩
  have hprev_ne : phaseBit S (prevN hn i) ≠ target := by
    have : prevN hn i = stepBack hn x m0 := by
      dsimp only [i]
      conv_rhs => rw [show m0 = (m0 - 1) + 1 by omega]
      rfl
    rw [this]; exact hm0_spec.2
  have hi_mem : i ∈ phaseStarts hn S target :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprev_ne, hi_eq⟩
  have hdist : (x.val + n - i.val) % n = m0 - 1 := by
    have his : i.val = (x.val + n - (m0 - 1)) % n := stepBack_eq hn x (m0 - 1) (by omega)
    rw [his]
    have hxlt := x.isLt
    by_cases hge : m0 - 1 ≤ x.val
    · have h1 : (x.val + n - (m0 - 1)) % n = x.val - (m0 - 1) := by
        have : x.val + n - (m0 - 1) = (x.val - (m0 - 1)) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      have : x.val + n - (x.val - (m0 - 1)) = (m0 - 1) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have h1 : (x.val + n - (m0 - 1)) % n = x.val + n - (m0 - 1) := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      have : x.val + n - (x.val + n - (m0 - 1)) = m0 - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  refine ⟨i, hi_mem, by omega, ?_⟩
  intro r hr
  rw [hdist] at hr
  have hshift : shiftN hn i r = stepBack hn x (m0 - 1 - r) := by
    apply Fin.ext
    dsimp only [shiftN, i]
    rw [stepBack_eq hn x (m0 - 1) (by omega), stepBack_eq hn x (m0 - 1 - r) (by omega), Nat.mod_add_mod]
    have : x.val + n - (m0 - 1) + r = x.val + n - (m0 - 1 - r) := by omega
    rw [this]
  rw [hshift]
  by_contra hne
  exact Nat.find_min hex (show m0 - 1 - r < m0 by omega) ⟨by omega, hne⟩

lemma both_no_window_j_ge {n : ℕ} (hn24 : 24 ≤ n) (S : Finset (Fin n))
    (h0 : ¬ ∃ i : Fin n, ∀ j : Fin 24, phaseBit S (shiftN (by omega : 0 < n) i j.val) = true)
    (h1 : ¬ ∃ i : Fin n, ∀ j : Fin 24, phaseBit S (shiftN (by omega : 0 < n) i j.val) = false) :
    n / 48 ≤ (phaseStarts (by omega : 0 < n) S true).card := by
  have hn : 0 < n := by omega
  let cov : Bool → Finset (Fin n) := fun target =>
    (phaseStarts hn S target).biUnion (fun i => (Finset.range 23).image (fun r => shiftN hn i r))
  have huniv : (Finset.univ : Finset (Fin n)) ⊆ cov true ∪ cov false := by
    intro x _
    cases hx : phaseBit S x
    · refine Finset.mem_union_right _ ?_
      rcases no_window_cover hn24 S false h1 x hx with ⟨i, hi, hlt, _⟩
      refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨(x.val + n - i.val) % n, Finset.mem_range.mpr hlt, ?_⟩⟩
      apply Fin.ext
      dsimp only [shiftN]
      rw [Nat.add_mod_mod]
      have : i.val + (x.val + n - i.val) = x.val + n := by have := i.isLt; omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
    · refine Finset.mem_union_left _ ?_
      rcases no_window_cover hn24 S true h0 x hx with ⟨i, hi, hlt, _⟩
      refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨(x.val + n - i.val) % n, Finset.mem_range.mpr hlt, ?_⟩⟩
      apply Fin.ext
      dsimp only [shiftN]
      rw [Nat.add_mod_mod]
      have : i.val + (x.val + n - i.val) = x.val + n := by have := i.isLt; omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  have hcov_le : ∀ target : Bool, (cov target).card ≤ 23 * (phaseStarts hn S target).card := by
    intro target
    calc (cov target).card
        ≤ (phaseStarts hn S target).sum (fun i => ((Finset.range 23).image (fun r => shiftN hn i r)).card) :=
            Finset.card_biUnion_le
      _ ≤ (phaseStarts hn S target).sum (fun _ => 23) :=
            Finset.sum_le_sum (fun i _ => (Finset.card_image_le).trans (by simp))
      _ = 23 * (phaseStarts hn S target).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have htot : n ≤ 23 * (phaseStarts hn S true).card + 23 * (phaseStarts hn S false).card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (cov true ∪ cov false).card := Finset.card_le_card huniv
      _ ≤ (cov true).card + (cov false).card := Finset.card_union_le _ _
      _ ≤ 23 * (phaseStarts hn S true).card + 23 * (phaseStarts hn S false).card :=
          Nat.add_le_add (hcov_le true) (hcov_le false)
  rw [← phaseStarts_card_eq hn S] at htot
  omega

lemma card_no_window_family_le {n : ℕ} (hn : 0 < n) (hn24 : 24 ≤ n) (target : Bool) (j : ℕ) :
    (@Finset.filter (Finset (Fin n)) (fun S =>
      (phaseStarts hn S target).card = j ∧
      ¬ ∃ i : Fin n, ∀ k : Fin 24, phaseBit S (shiftN hn i k.val) = target)
      (Classical.decPred _) Finset.univ).card ≤ Nat.choose n j * 24 ^ j := by
  classical
  let Fam : Finset (Finset (Fin n)) := @Finset.filter (Finset (Fin n)) (fun S =>
    (phaseStarts hn S target).card = j ∧
    ¬ ∃ i : Fin n, ∀ k : Fin 24, phaseBit S (shiftN hn i k.val) = target)
    (Classical.decPred _) Finset.univ
  have hmemF : ∀ S : Finset (Fin n), S ∈ Fam ↔
      (phaseStarts hn S target).card = j ∧
      ¬ ∃ i : Fin n, ∀ k : Fin 24, phaseBit S (shiftN hn i k.val) = target := fun S => by
    dsimp only [Fam]; simp
  change Fam.card ≤ Nat.choose n j * 24 ^ j
  let Cod := ((Finset.univ : Finset (Fin n)).powersetCard j) ×ˢ (Finset.univ : Finset (Fin j → Fin 24))
  have hCod_card : Cod.card = Nat.choose n j * 24 ^ j := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← hCod_card]
  have hlen : ∀ (S : Finset (Fin n)), S ∈ Fam → ∀ i : Fin n,
      ∃ k : Fin 24, phaseBit S (shiftN hn i k.val) ≠ target := by
    intro S hS i
    have hnowin := ((hmemF S).mp hS).2
    push Not at hnowin
    exact hnowin i
  have hex : ∀ (S : Finset (Fin n)), S ∈ Fam → ∀ i : Fin n,
      ∃ m : ℕ, m < 24 ∧ phaseBit S (shiftN hn i m) ≠ target := by
    intro S hS i
    rcases hlen S hS i with ⟨k, hk⟩
    exact ⟨k.val, k.isLt, hk⟩
  let runLen : (S : Finset (Fin n)) → S ∈ Fam → Fin n → Fin 24 := fun S hS i =>
    ⟨Nat.find (hex S hS i), (Nat.find_spec (hex S hS i)).1⟩
  have hrunLen_lt : ∀ (S : Finset (Fin n)) (hS : S ∈ Fam) (i : Fin n) (r : ℕ),
      r < (runLen S hS i).val → phaseBit S (shiftN hn i r) = target := by
    intro S hS i r hr
    by_contra hne
    exact Nat.find_min (hex S hS i) hr ⟨by omega, hne⟩
  have hrunLen_ne : ∀ (S : Finset (Fin n)) (hS : S ∈ Fam) (i : Fin n),
      phaseBit S (shiftN hn i (runLen S hS i).val) ≠ target := fun S hS i =>
    (Nat.find_spec (hex S hS i)).2
  have hchar : ∀ (S : Finset (Fin n)) (hS : S ∈ Fam) (x : Fin n),
      phaseBit S x = target ↔
      ∃ i ∈ phaseStarts hn S target, (x.val + n - i.val) % n < (runLen S hS i).val := by
    intro S hS x
    constructor
    · intro hx
      rcases no_window_cover hn24 S target ((hmemF S).mp hS).2 x hx with ⟨i, hi, _, hall⟩
      refine ⟨i, hi, ?_⟩
      by_contra hge
      have hle : (runLen S hS i).val ≤ (x.val + n - i.val) % n := not_lt.mp hge
      exact hrunLen_ne S hS i (hall (runLen S hS i).val hle)
    · rintro ⟨i, _, hlt⟩
      have h1 := hrunLen_lt S hS i ((x.val + n - i.val) % n) hlt
      have hshift : shiftN hn i ((x.val + n - i.val) % n) = x := by
        apply Fin.ext; dsimp only [shiftN]
        rw [Nat.add_mod_mod]
        have : i.val + (x.val + n - i.val) = x.val + n := by have := i.isLt; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
      rwa [hshift] at h1
  let enc : (S : Finset (Fin n)) → Finset (Fin n) × (Fin j → Fin 24) := fun S =>
    if hS : S ∈ Fam then
      (phaseStarts hn S target,
        fun r => runLen S hS ((phaseStarts hn S target).orderEmbOfFin ((hmemF S).mp hS).1 r))
    else (∅, fun _ => 0)
  have hsub : Fam.image enc ⊆ Cod := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨S, hS, rfl⟩
    dsimp only [enc]
    simp only [hS, ↓reduceDIte]
    refine Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ((hmemF S).mp hS).1⟩,
      Finset.mem_univ _⟩
  have hinj : Set.InjOn enc (Fam : Set (Finset (Fin n))) := by
    intro S1 hS1 S2 hS2 heq
    have hS1' : S1 ∈ Fam := Finset.mem_coe.mp hS1
    have hS2' : S2 ∈ Fam := Finset.mem_coe.mp hS2
    dsimp only [enc] at heq
    simp only [hS1', hS2', ↓reduceDIte] at heq
    rcases Prod.mk.inj heq with ⟨hst_eq, hfn_eq⟩
    have hlen_eq : ∀ i ∈ phaseStarts hn S1 target, runLen S1 hS1' i = runLen S2 hS2' i := by
      intro i hi
      let e1 := (phaseStarts hn S1 target).orderEmbOfFin ((hmemF S1).mp hS1').1
      let e2 := (phaseStarts hn S2 target).orderEmbOfFin ((hmemF S2).mp hS2').1
      have hrange1 : Set.range e1 = (phaseStarts hn S1 target : Set (Fin n)) := Finset.range_orderEmbOfFin _ _
      have hi1 : i ∈ Set.range e1 := by rw [hrange1]; exact hi
      rcases hi1 with ⟨r, rfl⟩
      have he12 : e1 r = e2 r := by
        have : ∀ (A B : Finset (Fin n)) (hA : A.card = j) (hB : B.card = j), A = B →
            A.orderEmbOfFin hA r = B.orderEmbOfFin hB r := by
          intro A B hA hB hAB; subst hAB; rfl
        exact this _ _ _ _ hst_eq
      have hfr := congrFun hfn_eq r
      rw [hfr, he12]
    have hp_eq : ∀ x : Fin n, phaseBit S1 x = phaseBit S2 x := by
      intro x
      have hiff : phaseBit S1 x = target ↔ phaseBit S2 x = target := by
        rw [hchar S1 hS1' x, hchar S2 hS2' x]
        constructor
        · rintro ⟨i, hi, hlt⟩
          refine ⟨i, hst_eq ▸ hi, ?_⟩
          rwa [← hlen_eq i hi]
        · rintro ⟨i, hi, hlt⟩
          have hi1 : i ∈ phaseStarts hn S1 target := hst_eq.symm ▸ hi
          refine ⟨i, hi1, ?_⟩
          rwa [hlen_eq i hi1]
      cases h1 : phaseBit S1 x <;> cases h2 : phaseBit S2 x <;> cases target <;>
        simp [h1, h2] at hiff ⊢
    ext x
    have hx := hp_eq x
    dsimp only [phaseBit] at hx
    by_cases h1 : x ∈ S1 <;> by_cases h2 : x ∈ S2 <;> by_cases hp : x.val % 2 = 0 <;>
      simp [h1, h2, hp] at hx ⊢
  calc Fam.card = (Fam.image enc).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Cod.card := Finset.card_le_card hsub

lemma sum_Icc_choose_le_binom (n k : ℕ) (x : ℝ) (hx : 0 ≤ x) (hkn : k ≤ n) :
    (∑ j ∈ Finset.Icc 1 k, (Nat.choose n j : ℝ) * x ^ j) ≤ (1 + x) ^ n - 1 := by
  have hexp : (1 + x) ^ n = ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * x ^ j := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun j _ => by simp [mul_comm])
  have hsplit : (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * x ^ j) =
      1 + ∑ j ∈ Finset.Icc 1 n, (Nat.choose n j : ℝ) * x ^ j := by
    have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    simp
  have hsub : Finset.Icc 1 k ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_right hkn
  have hle : (∑ j ∈ Finset.Icc 1 k, (Nat.choose n j : ℝ) * x ^ j) ≤
      ∑ j ∈ Finset.Icc 1 n, (Nat.choose n j : ℝ) * x ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
  linarith

lemma main_proof (t d : ℕ) (ht : 4 ≤ t) (hd : 2 ≤ d) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let F := ZMod 2
    let n := 6 * t
    let a := 3 * t
    let W := Fin n → F
    letI : Fintype (Submodule F W) := Fintype.ofFinite _
    let next := fun i : Fin n =>
      (⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
    let h := fun (i : Fin n) (b : Fin 4) =>
      if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : F) else 0
    let good := fun U : Submodule F W =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    let supp := fun U : Submodule F W =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let spaces := (Finset.univ : Finset (Submodule F W)).filter good
    let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
    let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
    let B := ∏ i ∈ Finset.range d, (2 ^ d - 2 ^ i : ℕ)
    let s := (2 : ℝ) ^ d
    let move := fun (i : Fin n) (j : Fin 24) =>
      (⟨(i.val + j.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
    let window := fun (S : Finset (Fin n)) (b : Fin 2) =>
      ∃ i : Fin n, ∀ j : Fin 24, move i j ∈ S ↔ (move i j).val % 2 = b.val
    let bad := mixed.filter (fun U => ∃ b : Fin 2, ¬ window (supp U) b)
    (B : ℝ) * (bad.card : ℝ) ≤
      2 * s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) + (2 : ℝ) ^ n * s ^ (a - n / 48) := by
  intro F n a W next h good supp spaces layer mixed B s move window bad
  classical
  have hn : 0 < n := by dsimp only [n]; omega
  have heven : n % 2 = 0 := by dsimp only [n]; omega
  have hn24 : 24 ≤ n := by dsimp only [n]; omega
  have hs_pos : (0 : ℝ) < s := by dsimp only [s]; positivity
  have hs_ge1 : (1 : ℝ) ≤ s := by
    dsimp only [s]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hh_eq : ∀ i b, h i b = checkH i b := fun i b => by
    dsimp only [h, checkH]
    by_cases hc : i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2) <;> simp [hc]
  have hgood_chk : ∀ U : Submodule F W, good U →
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i : Fin n, checkH i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (nextN hn i) = x (nextN hn i) * y i) := by
    intro U hU
    refine ⟨fun x hx b => ?_, hU.2⟩
    simpa only [← hh_eq] using hU.1 x hx b
  have hsupp_eq : ∀ U : Submodule F W,
      supp U = @Finset.filter (Fin n) (fun i => ∃ x ∈ U, x i ≠ 0) (Classical.decPred _) Finset.univ := fun U => by
    ext i; dsimp only [supp]; simp
  have hwin_iff : ∀ (S : Finset (Fin n)) (b : Fin 2),
      window S b ↔ ∃ i : Fin n, ∀ j : Fin 24, phaseBit S (shiftN hn i j.val) = decide (b.val = 0) :=
    fun S b => window_iff_phaseBit hn S b
  have hmem_spaces : ∀ U : Submodule F W, U ∈ spaces ↔ good U := fun U => by dsimp only [spaces]; simp
  have hmem_layer : ∀ U : Submodule F W, U ∈ layer ↔ U ∈ spaces ∧ Module.finrank F U = d := fun U => by
    dsimp only [layer]; simp
  have hmem_mixed : ∀ U : Submodule F W, U ∈ mixed ↔ U ∈ layer ∧ ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val := fun U => by
    dsimp only [mixed]; simp
  have hmem_bad : ∀ U : Submodule F W, U ∈ bad ↔ U ∈ mixed ∧ ∃ b : Fin 2, ¬ window (supp U) b := fun U => by
    dsimp only [bad]; simp
  let bad0 := bad.filter (fun U => ¬ window (supp U) 0 ∧ window (supp U) 1)
  let bad1 := bad.filter (fun U => window (supp U) 0 ∧ ¬ window (supp U) 1)
  let badBoth := bad.filter (fun U => ¬ window (supp U) 0 ∧ ¬ window (supp U) 1)
  have hbad_sub : bad ⊆ bad0 ∪ bad1 ∪ badBoth := by
    intro U hU
    have hnot : ∃ b : Fin 2, ¬ window (supp U) b := ((hmem_bad U).mp hU).2
    by_cases hw0 : window (supp U) 0
    · by_cases hw1 : window (supp U) 1
      · exfalso
        rcases hnot with ⟨b, hb⟩
        fin_cases b
        · exact hb hw0
        · exact hb hw1
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hU, hw0, hw1⟩))
    · by_cases hw1 : window (supp U) 1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hU, hw0, hw1⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hU, hw0, hw1⟩)
  have hbad_card : (bad.card : ℝ) ≤ (bad0.card : ℝ) + (bad1.card : ℝ) + (badBoth.card : ℝ) := by
    have hnat : bad.card ≤ bad0.card + bad1.card + badBoth.card := by
      calc bad.card ≤ (bad0 ∪ bad1 ∪ badBoth).card := Finset.card_le_card hbad_sub
        _ ≤ (bad0 ∪ bad1).card + badBoth.card := Finset.card_union_le _ _
        _ ≤ bad0.card + bad1.card + badBoth.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    exact_mod_cast hnat
  have hone_side : ∀ (bMiss bHit : Fin 2), bMiss ≠ bHit →
      let sub := bad.filter (fun U => ¬ window (supp U) bMiss ∧ window (supp U) bHit)
      (B : ℝ) * (sub.card : ℝ) ≤ s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) := by
    intro bMiss bHit _ sub
    let target : Bool := decide (bMiss.val = 0)
    let jOf : Submodule F W → ℕ := fun U => (phaseStarts hn (supp U) target).card
    have hj_mem : ∀ U ∈ sub, jOf U ∈ Finset.Icc 1 (a - 2) := by
      intro U hU
      have hUbad : U ∈ bad := (Finset.mem_filter.mp hU).1
      have hUmix : U ∈ mixed := ((hmem_bad U).mp hUbad).1
      have hUlay : U ∈ layer := ((hmem_mixed U).mp hUmix).1
      have hUsp : U ∈ spaces := ((hmem_layer U).mp hUlay).1
      have hgood : good U := (hmem_spaces U).mp hUsp
      have hUrk : Module.finrank F U = d := ((hmem_layer U).mp hUlay).2
      have hmix : ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val := ((hmem_mixed U).mp hUmix).2
      have hwinHit : window (supp U) bHit := (Finset.mem_filter.mp hU).2.2
      have hSne : supp U ≠ Finset.univ := by
        rw [hsupp_eq U]
        exact supp_ne_univ_of_finrank_ge_two hn U (by rw [hUrk]; exact hd) (hgood_chk U hgood).1 (hgood_chk U hgood).2
      have hle_chk : U ≤ checkSpace hn (supp U) := by
        rw [hsupp_eq U]
        exact good_le_checkSpace hn U (hgood_chk U hgood).1 (hgood_chk U hgood).2
      have hrk_le : Module.finrank F U ≤ Module.finrank F (checkSpace hn (supp U)) :=
        Submodule.finrank_mono hle_chk
      have hsub2 := finrank_checkSpace_le_sub_two ht (supp U) hSne bHit hwinHit
      have hadd := runEnds_add_phaseStarts hn heven (supp U) target
      have hj1 : 1 ≤ jOf U := phaseStarts_pos_of_mixed hn (supp U) hmix target
      refine Finset.mem_Icc.mpr ⟨hj1, ?_⟩
      dsimp only [jOf, a, n] at *
      omega
    have hsplit_j : sub.card = ∑ j ∈ Finset.Icc 1 (a - 2), (sub.filter (fun U => jOf U = j)).card :=
      Finset.card_eq_sum_card_fiberwise hj_mem
    have hterm_j : ∀ j ∈ Finset.Icc 1 (a - 2),
        (B : ℝ) * ((sub.filter (fun U => jOf U = j)).card : ℝ) ≤
        s ^ (a - 2) * (Nat.choose n j : ℝ) * (24 / s) ^ j := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hja : j ≤ a - 2 := (Finset.mem_Icc.mp hj).2
      let Fam : Finset (Finset (Fin n)) := Finset.univ.filter (fun S =>
        (phaseStarts hn S target).card = j ∧
        ¬ ∃ i : Fin n, ∀ k : Fin 24, phaseBit S (shiftN hn i k.val) = target)
      have hmaps : ∀ U ∈ sub.filter (fun U => jOf U = j), supp U ∈ Fam := by
        intro U hU
        rcases Finset.mem_filter.mp hU with ⟨hUsub, hjU⟩
        have hnowin : ¬ window (supp U) bMiss := (Finset.mem_filter.mp hUsub).2.1
        rw [hwin_iff (supp U) bMiss] at hnowin
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjU, hnowin⟩
      have hsplit_S : (sub.filter (fun U => jOf U = j)).card =
          ∑ S ∈ Fam, ((sub.filter (fun U => jOf U = j)).filter (fun U => supp U = S)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have hfib_S : ∀ S ∈ Fam,
          B * (((sub.filter (fun U => jOf U = j)).filter (fun U => supp U = S)).card) ≤
          (2 ^ d) ^ (a - 2 - j) := by
        intro S hS
        let Fset := (sub.filter (fun U => jOf U = j)).filter (fun U => supp U = S)
        by_cases hne : Fset.Nonempty
        · rcases hne with ⟨U0, hU0⟩
          have hU0sub : U0 ∈ sub := (Finset.mem_filter.mp (Finset.mem_filter.mp hU0).1).1
          have hU0S : supp U0 = S := (Finset.mem_filter.mp hU0).2
          have hU0bad : U0 ∈ bad := (Finset.mem_filter.mp hU0sub).1
          have hU0mix : U0 ∈ mixed := ((hmem_bad U0).mp hU0bad).1
          have hU0lay : U0 ∈ layer := ((hmem_mixed U0).mp hU0mix).1
          have hU0sp : U0 ∈ spaces := ((hmem_layer U0).mp hU0lay).1
          have hgood0 : good U0 := (hmem_spaces U0).mp hU0sp
          have hUrk0 : Module.finrank F U0 = d := ((hmem_layer U0).mp hU0lay).2
          have hwinHit0 : window S bHit := hU0S ▸ (Finset.mem_filter.mp hU0sub).2.2
          have hSne : S ≠ Finset.univ := by
            rw [← hU0S, hsupp_eq U0]
            exact supp_ne_univ_of_finrank_ge_two hn U0 (by rw [hUrk0]; exact hd) (hgood_chk U0 hgood0).1 (hgood_chk U0 hgood0).2
          have hbb := basis_bound_for_subspace (checkSpace hn S) Fset (fun U hU => by
            have hUsub : U ∈ sub := (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1
            have hUS : supp U = S := (Finset.mem_filter.mp hU).2
            have hUbad : U ∈ bad := (Finset.mem_filter.mp hUsub).1
            have hUmix : U ∈ mixed := ((hmem_bad U).mp hUbad).1
            have hUlay : U ∈ layer := ((hmem_mixed U).mp hUmix).1
            have hUsp : U ∈ spaces := ((hmem_layer U).mp hUlay).1
            have hgood : good U := (hmem_spaces U).mp hUsp
            refine ⟨?_, ((hmem_layer U).mp hUlay).2⟩
            rw [← hUS, hsupp_eq U]
            exact good_le_checkSpace hn U (hgood_chk U hgood).1 (hgood_chk U hgood).2)
          have hsub2 := finrank_checkSpace_le_sub_two ht S hSne bHit hwinHit0
          have hadd := runEnds_add_phaseStarts hn heven S target
          have hjS : (phaseStarts hn S target).card = j := (Finset.mem_filter.mp hS).2.1
          have hrk_le : Module.finrank F2 (checkSpace hn S) ≤ a - 2 - j := by
            dsimp only [a, n] at *; omega
          exact hbb.trans (Nat.pow_le_pow_right (by positivity) hrk_le)
        · change B * Fset.card ≤ _
          rw [Finset.not_nonempty_iff_eq_empty.mp hne]
          simp
      have hcard_Fam : Fam.card ≤ Nat.choose n j * 24 ^ j := by
        have hfeq : Fam = @Finset.filter (Finset (Fin n)) (fun S =>
            (phaseStarts hn S target).card = j ∧
            ¬ ∃ i : Fin n, ∀ k : Fin 24, phaseBit S (shiftN hn i k.val) = target)
            (Classical.decPred _) Finset.univ := by
          ext S; dsimp only [Fam]; simp
        rw [hfeq]
        exact card_no_window_family_le hn hn24 target j
      have hnat_j : B * (sub.filter (fun U => jOf U = j)).card ≤
          (Nat.choose n j * 24 ^ j) * (2 ^ d) ^ (a - 2 - j) := by
        rw [hsplit_S, Finset.mul_sum]
        calc (∑ S ∈ Fam, B * ((sub.filter (fun U => jOf U = j)).filter (fun U => supp U = S)).card)
            ≤ ∑ _S ∈ Fam, (2 ^ d) ^ (a - 2 - j) := Finset.sum_le_sum hfib_S
          _ = Fam.card * (2 ^ d) ^ (a - 2 - j) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (Nat.choose n j * 24 ^ j) * (2 ^ d) ^ (a - 2 - j) :=
              Nat.mul_le_mul_right _ hcard_Fam
      have hreal_j : (B : ℝ) * ((sub.filter (fun U => jOf U = j)).card : ℝ) ≤
          ((Nat.choose n j : ℝ) * (24 : ℝ) ^ j) * s ^ (a - 2 - j) := by
        have hcast : ((B * (sub.filter (fun U => jOf U = j)).card : ℕ) : ℝ) ≤
            (((Nat.choose n j * 24 ^ j) * (2 ^ d) ^ (a - 2 - j) : ℕ) : ℝ) := by
          exact_mod_cast hnat_j
        push_cast at hcast
        simpa [s] using hcast
      have hpow_eq : s ^ (a - 2 - j) = s ^ (a - 2) / s ^ j := by
        rw [eq_div_iff (pow_ne_zero j hs_pos.ne'), ← pow_add, Nat.sub_add_cancel hja]
      calc (B : ℝ) * ((sub.filter (fun U => jOf U = j)).card : ℝ)
          ≤ ((Nat.choose n j : ℝ) * (24 : ℝ) ^ j) * (s ^ (a - 2) / s ^ j) := by rwa [← hpow_eq]
        _ = s ^ (a - 2) * (Nat.choose n j : ℝ) * (24 / s) ^ j := by rw [div_pow]; ring
    calc (B : ℝ) * (sub.card : ℝ)
        = ∑ j ∈ Finset.Icc 1 (a - 2), (B : ℝ) * ((sub.filter (fun U => jOf U = j)).card : ℝ) := by
            rw [hsplit_j, Nat.cast_sum, Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.Icc 1 (a - 2), s ^ (a - 2) * (Nat.choose n j : ℝ) * (24 / s) ^ j :=
            Finset.sum_le_sum hterm_j
      _ = s ^ (a - 2) * ∑ j ∈ Finset.Icc 1 (a - 2), (Nat.choose n j : ℝ) * (24 / s) ^ j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_Icc_choose_le_binom n (a - 2) (24 / s) (by positivity) (by dsimp only [a, n]; omega)
  have hbound0 : (B : ℝ) * (bad0.card : ℝ) ≤ s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) :=
    hone_side 0 1 (by decide)
  have hbound1 : (B : ℝ) * (bad1.card : ℝ) ≤ s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) := by
    have heq : bad1 = bad.filter (fun U => ¬ window (supp U) 1 ∧ window (supp U) 0) := by
      ext U; simp only [bad1, Finset.mem_filter]; tauto
    rw [heq]
    exact hone_side 1 0 (by decide)
  have hboundBoth : (B : ℝ) * (badBoth.card : ℝ) ≤ (2 : ℝ) ^ n * s ^ (a - n / 48) := by
    have hsplit : badBoth.card =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), (badBoth.filter (fun U => supp U = S)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    have hfib : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
        B * (badBoth.filter (fun U => supp U = S)).card ≤ (2 ^ d) ^ (a - n / 48) := by
      intro S _
      let Fset := badBoth.filter (fun U => supp U = S)
      by_cases hne : Fset.Nonempty
      · rcases hne with ⟨U0, hU0⟩
        have hU0b : U0 ∈ badBoth := (Finset.mem_filter.mp hU0).1
        have hU0S : supp U0 = S := (Finset.mem_filter.mp hU0).2
        have hU0bad : U0 ∈ bad := (Finset.mem_filter.mp hU0b).1
        have hU0mix : U0 ∈ mixed := ((hmem_bad U0).mp hU0bad).1
        have hU0lay : U0 ∈ layer := ((hmem_mixed U0).mp hU0mix).1
        have hU0sp : U0 ∈ spaces := ((hmem_layer U0).mp hU0lay).1
        have hgood0 : good U0 := (hmem_spaces U0).mp hU0sp
        have hUrk0 : Module.finrank F U0 = d := ((hmem_layer U0).mp hU0lay).2
        have hSne : S ≠ Finset.univ := by
          rw [← hU0S, hsupp_eq U0]
          exact supp_ne_univ_of_finrank_ge_two hn U0 (by rw [hUrk0]; exact hd) (hgood_chk U0 hgood0).1 (hgood_chk U0 hgood0).2
        have hnw0 : ¬ window S 0 := hU0S ▸ (Finset.mem_filter.mp hU0b).2.1
        have hnw1 : ¬ window S 1 := hU0S ▸ (Finset.mem_filter.mp hU0b).2.2
        rw [hwin_iff S 0] at hnw0
        rw [hwin_iff S 1] at hnw1
        simp only [Fin.val_zero, decide_true] at hnw0
        simp only [Fin.val_one, one_ne_zero, decide_false] at hnw1
        have hjge : n / 48 ≤ (phaseStarts hn S true).card := both_no_window_j_ge hn24 S hnw0 hnw1
        have hadd := runEnds_add_phaseStarts hn heven S true
        have hbb := basis_bound_for_subspace (runSpace hn S) Fset (fun U hU => by
          have hUb : U ∈ badBoth := (Finset.mem_filter.mp hU).1
          have hUS : supp U = S := (Finset.mem_filter.mp hU).2
          have hUbad : U ∈ bad := (Finset.mem_filter.mp hUb).1
          have hUmix : U ∈ mixed := ((hmem_bad U).mp hUbad).1
          have hUlay : U ∈ layer := ((hmem_mixed U).mp hUmix).1
          have hUsp : U ∈ spaces := ((hmem_layer U).mp hUlay).1
          have hgood : good U := (hmem_spaces U).mp hUsp
          have hchk : U ≤ checkSpace hn S := by
            rw [← hUS, hsupp_eq U]
            exact good_le_checkSpace hn U (hgood_chk U hgood).1 (hgood_chk U hgood).2
          exact ⟨fun x hx => (hchk hx).1, ((hmem_layer U).mp hUlay).2⟩)
        have hrk_le : Module.finrank F2 (runSpace hn S) ≤ a - n / 48 := by
          have h1 := finrank_runSpace_le hn S hSne
          dsimp only [a, n] at *; omega
        exact hbb.trans (Nat.pow_le_pow_right (by positivity) hrk_le)
      · change B * Fset.card ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
    have hnat : B * badBoth.card ≤ 2 ^ n * (2 ^ d) ^ (a - n / 48) := by
      rw [hsplit, Finset.mul_sum]
      calc (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), B * (badBoth.filter (fun U => supp U = S)).card)
          ≤ ∑ _S ∈ (Finset.univ : Finset (Finset (Fin n))), (2 ^ d) ^ (a - n / 48) := Finset.sum_le_sum hfib
        _ = (Finset.univ : Finset (Finset (Fin n))).card * (2 ^ d) ^ (a - n / 48) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = 2 ^ n * (2 ^ d) ^ (a - n / 48) := by simp [Fintype.card_finset, Fintype.card_fin]
    have hcast : ((B * badBoth.card : ℕ) : ℝ) ≤ ((2 ^ n * (2 ^ d) ^ (a - n / 48) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    simpa [s] using hcast
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
  calc (B : ℝ) * (bad.card : ℝ)
      ≤ (B : ℝ) * ((bad0.card : ℝ) + (bad1.card : ℝ) + (badBoth.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hbad_card hBnn
    _ = (B : ℝ) * (bad0.card : ℝ) + (B : ℝ) * (bad1.card : ℝ) + (B : ℝ) * (badBoth.card : ℝ) := by ring
    _ ≤ s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) + s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) +
        (2 : ℝ) ^ n * s ^ (a - n / 48) := by linarith
    _ = 2 * s ^ (a - 2) * ((1 + 24 / s) ^ n - 1) + (2 : ℝ) ^ n * s ^ (a - n / 48) := by ring

end PEqualNP.Outside.L_lib_939_aux

theorem PEqualNP.Outside.L_lib_939 :
∀ (t d : ℕ), 4 ≤ t → 2 ≤ d →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let layer := spaces.filter (fun U : Submodule F W => Module.finrank F U = d)
  let mixed := layer.filter (fun U => ∀ b : Fin 2, ∃ i ∈ supp U, i.val % 2 = b.val)
  let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ)
  let s := (2 : ℝ)^d
  let move := fun (i : Fin n) (j : Fin 24) =>
    (⟨(i.val+j.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let window := fun (S : Finset (Fin n)) (b : Fin 2) =>
    ∃ i : Fin n, ∀ j : Fin 24, move i j ∈ S ↔ (move i j).val % 2 = b.val
  let bad := mixed.filter (fun U => ∃ b : Fin 2, ¬ window (supp U) b)
  (B : ℝ)*(bad.card : ℝ) ≤
    2*s^(a-2)*((1+24/s)^n-1) + (2 : ℝ)^n*s^(a-n/48) := by
  exact PEqualNP.Outside.L_lib_939_aux.main_proof

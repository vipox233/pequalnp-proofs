import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_pcx_339

-- ============================================================================
-- Part A: Alternating-cycle one-pass streaming for a pair of matchings
-- ============================================================================

private theorem orbit_period_exists {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ k) x0 = x0 := by
  have hnot : ¬ Function.Injective (fun k : ℕ => (σ ^ k) x0) := fun hinj => by
    have := Finite.of_injective _ hinj
    exact not_finite ℕ
  rw [Function.Injective] at hnot
  push Not at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨b - a, by omega, ?_⟩
    have h1 : (σ ^ a) ((σ ^ (b - a)) x0) = (σ ^ a) x0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
      exact hab.symm
    exact (σ ^ a).injective h1
  · refine ⟨a - b, by omega, ?_⟩
    have h1 : (σ ^ b) ((σ ^ (a - b)) x0) = (σ ^ b) x0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]
      exact hab
    exact (σ ^ b).injective h1

private noncomputable def orbitList {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) : List (Fin n) :=
  let L := Nat.find (orbit_period_exists σ x0)
  (List.range L).map (fun t => (σ ^ t) x0)

private theorem orbitList_spec {n : ℕ} (σ : Equiv.Perm (Fin n)) (x0 : Fin n) :
    let orb := orbitList σ x0
    0 < orb.length ∧
    orb.Nodup ∧
    x0 ∈ orb ∧
    (∀ y ∈ orb, σ y ∈ orb) ∧
    (∀ y ∈ orb, σ.symm y ∈ orb) ∧
    ∀ idx (h : idx < orb.length),
      σ (orb[idx]) = orb[(idx + 1) % orb.length]'(Nat.mod_lt _ (by omega)) := by
  unfold orbitList
  have hex := orbit_period_exists σ x0
  set L := Nat.find (orbit_period_exists σ x0)
  have hL_spec : 0 < L ∧ (σ ^ L) x0 = x0 := Nat.find_spec (orbit_period_exists σ x0)
  have hL_min : ∀ m < L, 0 < m → (σ ^ m) x0 ≠ x0 := fun m hm hm0 => by
    have := Nat.find_min (orbit_period_exists σ x0) hm
    push Not at this
    exact this hm0
  have hlen : ((List.range L).map (fun t => (σ ^ t) x0)).length = L := by simp
  have hnodup : ((List.range L).map (fun t => (σ ^ t) x0)).Nodup := by
    rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro a ha b hb heq
    rw [List.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (σ ^ (b - a)) x0 = x0 := by
        apply (σ ^ a).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
        exact heq.symm
      exact hL_min (b - a) (by omega) (by omega) h1
    · have h1 : (σ ^ (a - b)) x0 = x0 := by
        apply (σ ^ b).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]
        exact heq
      exact hL_min (a - b) (by omega) (by omega) h1
  have hnext : ∀ idx (h : idx < L),
      σ ((σ ^ idx) x0) = (σ ^ ((idx + 1) % L)) x0 := by
    intro idx hidx
    have hstep : σ ((σ ^ idx) x0) = (σ ^ (idx + 1)) x0 := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hstep]
    by_cases hlt : idx + 1 < L
    · rw [Nat.mod_eq_of_lt hlt]
    · have heqL : idx + 1 = L := by omega
      rw [heqL, Nat.mod_self, hL_spec.2]; rfl
  refine ⟨by rw [hlen]; exact hL_spec.1, hnodup, ?_, ?_, ?_, ?_⟩
  · rw [List.mem_map]; exact ⟨0, List.mem_range.mpr hL_spec.1, rfl⟩
  · intro y hy
    rw [List.mem_map] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    rw [List.mem_range] at ht
    exact ⟨(t + 1) % L, List.mem_range.mpr (Nat.mod_lt _ hL_spec.1), (hnext t ht).symm⟩
  · intro y hy
    rw [List.mem_map] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    rw [List.mem_range] at ht
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨L - 1, List.mem_range.mpr (by omega), ?_⟩
      apply σ.injective
      rw [Equiv.apply_symm_apply, hnext (L - 1) (by omega)]
      have : (L - 1 + 1) % L = 0 := by
        have : L - 1 + 1 = L := by omega
        rw [this, Nat.mod_self]
      rw [this]
    · refine ⟨t - 1, List.mem_range.mpr (by omega), ?_⟩
      apply σ.injective
      rw [Equiv.apply_symm_apply, hnext (t - 1) (by omega)]
      have : (t - 1 + 1) % L = t := by
        have : t - 1 + 1 = t := by omega
        rw [this, Nat.mod_eq_of_lt ht]
      rw [this]
  · intro idx h
    have hidx : idx < L := by rw [← hlen]; exact h
    simp only [List.getElem_map, List.getElem_range]
    simpa [hlen] using hnext idx hidx

private theorem decomp_cycles {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ (rem : Finset (Fin n)), (∀ x ∈ rem, σ x ∈ rem) →
      ∃ blocks : List (List (Fin n)),
        (∀ B ∈ blocks, 0 < B.length ∧ B.Nodup ∧
          (∀ y ∈ B, σ y ∈ B) ∧ (∀ y ∈ B, σ.symm y ∈ B) ∧
          ∀ idx (h : idx < B.length), σ B[idx] = B[(idx + 1) % B.length]'(Nat.mod_lt _ (by omega))) ∧
        blocks.flatten.Nodup ∧
        (∀ x, x ∈ blocks.flatten ↔ x ∈ rem) := by
  intro rem
  induction hcard : rem.card using Nat.strong_induction_on generalizing rem with
  | ind m ih =>
    intro hclosed
    by_cases hemp : rem = ∅
    · subst hemp
      refine ⟨[], ?_, List.nodup_nil, fun _ => by simp⟩
      intro _ h
      cases h
    · have hne : rem.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      let x0 := hne.choose
      have hx0 : x0 ∈ rem := hne.choose_spec
      let orb := orbitList σ x0
      have horb := orbitList_spec σ x0
      have horb_sub : ∀ y ∈ orb, y ∈ rem := by
        intro y hy
        unfold orb orbitList at hy
        rw [List.mem_map] at hy
        obtain ⟨t, ht, rfl⟩ := hy
        clear ht
        induction t with
        | zero => exact hx0
        | succ t' iht =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hclosed _ iht
      let rem' := rem \ orb.toFinset
      have hlt : rem'.card < m := by
        rw [← hcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, fun heq => ?_⟩
        have hx0_in : x0 ∈ rem' := by rw [heq]; exact hx0
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hx0_in
        exact hx0_in.2 horb.2.2.1
      have hclosed' : ∀ x ∈ rem', σ x ∈ rem' := by
        intro x hx
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hx ⊢
        refine ⟨hclosed x hx.1, fun hmem => hx.2 ?_⟩
        have := horb.2.2.2.2.1 (σ x) hmem
        simpa using this
      obtain ⟨rest, hrest_ok, hrest_nd, hrest_mem⟩ := ih rem'.card hlt rem' rfl hclosed'
      refine ⟨orb :: rest, ?_, ?_, ?_⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hmem
        · exact ⟨horb.1, horb.2.1, horb.2.2.2.1, horb.2.2.2.2.1, horb.2.2.2.2.2⟩
        · exact hrest_ok B hmem
      · rw [List.flatten_cons, List.nodup_append]
        refine ⟨horb.2.1, hrest_nd, fun a ha b hb heq => ?_⟩
        subst heq
        have hb' := (hrest_mem a).mp hb
        simp only [rem', Finset.mem_sdiff, List.mem_toFinset] at hb'
        exact hb'.2 ha
      · intro x
        simp only [List.flatten_cons, List.mem_append, hrest_mem, rem', Finset.mem_sdiff, List.mem_toFinset]
        by_cases hx : x ∈ orb
        · simp [hx, horb_sub x hx]
        · simp [hx]

private inductive StepTag where
  | start
  | evenMid
  | oddMid
  | oddEnd
  deriving DecidableEq

private abbrev SState (n : ℕ) := Bool × Bool × Fin (n + 1) × Fin (n + 1)

private noncomputable def stateEquiv (n : ℕ) : SState n ≃ Fin (4 * (n + 1) ^ 2) :=
  Fintype.equivFinOfCardEq (by
    simp only [SState, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring)

private def neOne (a b : Bool) : ℕ := if a ≠ b then 1 else 0

private def incFin {n : ℕ} (c : Fin (n + 1)) (d : ℕ) : Fin (n + 1) :=
  ⟨min (c.val + d) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private def stepS {n : ℕ} (tag : StepTag) (st : SState n) (bit : Bool) : SState n :=
  let (bStart, bPrev, c1, c2) := st
  match tag with
  | .start   => (bit, bit, c1, c2)
  | .evenMid => (bStart, bit, c1, incFin c2 (neOne bit bPrev))
  | .oddMid  => (bStart, bit, incFin c1 (neOne bPrev bit), c2)
  | .oddEnd  => (bStart, bit,
                  incFin c1 (neOne bPrev bit),
                  incFin c2 (neOne bStart bit))

private def stepNat (tag : StepTag) (st : Bool × Bool × ℕ × ℕ) (bit : Bool) : Bool × Bool × ℕ × ℕ :=
  let (bStart, bPrev, d1, d2) := st
  match tag with
  | .start   => (bit, bit, d1, d2)
  | .evenMid => (bStart, bit, d1, d2 + neOne bit bPrev)
  | .oddMid  => (bStart, bit, d1 + neOne bPrev bit, d2)
  | .oddEnd  => (bStart, bit,
                  d1 + neOne bPrev bit,
                  d2 + neOne bStart bit)

private lemma stepNat_mono_one (tag : StepTag) (st : Bool × Bool × ℕ × ℕ) (bit : Bool) :
    st.2.2.1 ≤ (stepNat tag st bit).2.2.1 ∧ st.2.2.2 ≤ (stepNat tag st bit).2.2.2 := by
  rcases st with ⟨bs, bp, d1, d2⟩
  cases tag <;> simp [stepNat]

private lemma foldl_stepNat_mono {α : Type*} (x : α → Bool) :
    ∀ (l : List (α × StepTag)) (st : Bool × Bool × ℕ × ℕ),
      st.2.2.1 ≤ (l.foldl (fun s p => stepNat p.2 s (x p.1)) st).2.2.1 ∧
      st.2.2.2 ≤ (l.foldl (fun s p => stepNat p.2 s (x p.1)) st).2.2.2
  | [], st => ⟨le_rfl, le_rfl⟩
  | p :: rest, st => by
    have h1 := stepNat_mono_one p.2 st (x p.1)
    have h2 := foldl_stepNat_mono x rest (stepNat p.2 st (x p.1))
    exact ⟨le_trans h1.1 h2.1, le_trans h1.2 h2.2⟩

private lemma foldl_stepS_eq_stepNat {n : ℕ} {α : Type*} (x : α → Bool) :
    ∀ (l : List (α × StepTag)) (st : SState n),
      let rN := l.foldl (fun s p => stepNat p.2 s (x p.1)) (st.1, st.2.1, st.2.2.1.val, st.2.2.2.val)
      rN.2.2.1 ≤ n → rN.2.2.2 ≤ n →
      let rS := l.foldl (fun s p => stepS p.2 s (x p.1)) st
      rS.1 = rN.1 ∧ rS.2.1 = rN.2.1 ∧ rS.2.2.1.val = rN.2.2.1 ∧ rS.2.2.2.val = rN.2.2.2
  | [], st, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | (v, tag) :: rest, st, h1, h2 => by
    rcases st with ⟨bs, bp, c1, c2⟩
    have hm := foldl_stepNat_mono x rest (stepNat tag (bs, bp, c1.val, c2.val) (x v))
    have hd1 : (stepNat tag (bs, bp, c1.val, c2.val) (x v)).2.2.1 ≤ n := le_trans hm.1 h1
    have hd2 : (stepNat tag (bs, bp, c1.val, c2.val) (x v)).2.2.2 ≤ n := le_trans hm.2 h2
    have hstep_eq :
        ((stepS tag (bs, bp, c1, c2) (x v)).1,
         (stepS tag (bs, bp, c1, c2) (x v)).2.1,
         (stepS tag (bs, bp, c1, c2) (x v)).2.2.1.val,
         (stepS tag (bs, bp, c1, c2) (x v)).2.2.2.val) =
        stepNat tag (bs, bp, c1.val, c2.val) (x v) := by
      cases tag <;> simp only [stepS, stepNat, incFin, Prod.mk.injEq, true_and] at hd1 hd2 ⊢
      · exact Nat.min_eq_left hd2
      · exact ⟨Nat.min_eq_left hd1, trivial⟩
      · exact ⟨Nat.min_eq_left hd1, Nat.min_eq_left hd2⟩
    simp only [List.foldl_cons] at h1 h2 ⊢
    rw [← hstep_eq] at h1 h2 ⊢
    exact foldl_stepS_eq_stepNat x rest (stepS tag (bs, bp, c1, c2) (x v)) h1 h2

private lemma foldl_conj {α β γ : Type*} (e : α ≃ β) (f : γ → α → α) :
    ∀ (l : List γ) (s : α),
      l.foldl (fun st k => e (f k (e.symm st))) (e s) = e (l.foldl (fun st k => f k st) s)
  | [], _ => rfl
  | a :: rest, s => by
    simp only [List.foldl_cons, Equiv.symm_apply_apply]
    exact foldl_conj e f rest (f a s)

private def altTagTail {n : ℕ} (π₁ : Equiv.Perm (Fin n)) :
    List (Fin n) → List ((Bool × Fin n) × StepTag)
  | [] => []
  | [b] => [((false, b), .evenMid), ((true, π₁ b), .oddEnd)]
  | b :: c :: rest =>
      ((false, b), .evenMid) :: ((true, π₁ b), .oddMid) :: altTagTail π₁ (c :: rest)

private def altTag {n : ℕ} (π₁ : Equiv.Perm (Fin n)) :
    List (Fin n) → List ((Bool × Fin n) × StepTag)
  | [] => []
  | [a] => [((false, a), .start), ((true, π₁ a), .oddEnd)]
  | a :: c :: rest =>
      ((false, a), .start) :: ((true, π₁ a), .oddMid) :: altTagTail π₁ (c :: rest)

private lemma altTagTail_fst {n : ℕ} (π₁ : Equiv.Perm (Fin n)) :
    ∀ l : List (Fin n),
      (altTagTail π₁ l).map Prod.fst = l.flatMap (fun i => [(false, i), (true, π₁ i)])
  | [] => rfl
  | [_] => rfl
  | _ :: c :: rest => by
      simp only [altTagTail, List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        altTagTail_fst π₁ (c :: rest)]

private lemma altTag_fst {n : ℕ} (π₁ : Equiv.Perm (Fin n)) :
    ∀ l : List (Fin n),
      (altTag π₁ l).map Prod.fst = l.flatMap (fun i => [(false, i), (true, π₁ i)])
  | [] => rfl
  | [_] => rfl
  | _ :: c :: rest => by
      simp only [altTag, List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        altTagTail_fst π₁ (c :: rest)]

private def mis {n : ℕ} (x : (Bool × Fin n) → Bool) (π : Equiv.Perm (Fin n)) (l : List (Fin n)) : ℕ :=
  l.countP (fun i => decide (x (false, i) ≠ x (true, π i)))

private lemma mis_cons {n : ℕ} (x : (Bool × Fin n) → Bool) (π : Equiv.Perm (Fin n))
    (a : Fin n) (l : List (Fin n)) :
    mis x π (a :: l) = neOne (x (false, a)) (x (true, π a)) + mis x π l := by
  unfold mis neOne
  rw [List.countP_cons]
  by_cases h : x (false, a) ≠ x (true, π a)
  · simp [h]; omega
  · simp [h]

private lemma mis_append {n : ℕ} (x : (Bool × Fin n) → Bool) (π : Equiv.Perm (Fin n))
    (l1 l2 : List (Fin n)) :
    mis x π (l1 ++ l2) = mis x π l1 + mis x π l2 := by
  unfold mis
  exact List.countP_append

private lemma countP_eq_card_filter_toFinset {α : Type*} [DecidableEq α] (p : α → Bool) :
    ∀ l : List α, l.Nodup → l.countP p = (l.toFinset.filter (fun a => p a = true)).card
  | [], _ => by simp
  | a :: rest, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨ha, hrest⟩
    rw [List.countP_cons, countP_eq_card_filter_toFinset p rest hrest, List.toFinset_cons,
      Finset.filter_insert]
    have hnot : a ∉ rest.toFinset.filter (fun x => p x = true) := by
      intro hm
      exact ha (List.mem_toFinset.mp (Finset.mem_filter.mp hm).1)
    cases hp : p a
    · simp
    · simp only [↓reduceIte, Finset.card_insert_of_notMem hnot]

private def IsChain {n : ℕ} (σ : Equiv.Perm (Fin n)) (prev head : Fin n) : List (Fin n) → Prop
  | [] => False
  | [b] => σ prev = b ∧ σ b = head
  | b :: c :: rest => σ prev = b ∧ IsChain σ b head (c :: rest)

private lemma isChain_of_drop {n : ℕ} (σ : Equiv.Perm (Fin n)) (B : List (Fin n))
    (hB0 : 0 < B.length)
    (hcyc : ∀ idx (h : idx < B.length), σ B[idx] = B[(idx + 1) % B.length]'(Nat.mod_lt _ hB0)) :
    ∀ m k (hk : k + 1 < B.length), B.length - (k + 1) = m →
      IsChain σ (B[k]'(by omega)) (B[0]'hB0) (B.drop (k + 1)) := by
  intro m
  induction m with
  | zero => intro k hk hm; omega
  | succ m' ih =>
    intro k hk hm
    have hdrop1 : B.drop (k + 1) = B[k + 1]'hk :: B.drop (k + 2) :=
      List.drop_eq_getElem_cons hk
    rw [hdrop1]
    have hstep1 : σ (B[k]'(by omega)) = B[k + 1]'hk := by
      have h := hcyc k (by omega)
      simpa [Nat.mod_eq_of_lt hk] using h
    by_cases hlt2 : k + 2 < B.length
    · have hdrop2 : B.drop (k + 2) = B[k + 2]'hlt2 :: B.drop (k + 3) :=
        List.drop_eq_getElem_cons hlt2
      rw [hdrop2]
      refine ⟨hstep1, ?_⟩
      have hih := ih (k + 1) hlt2 (by omega)
      rwa [hdrop2] at hih
    · have heq : k + 2 = B.length := by omega
      have hdrop2 : B.drop (k + 2) = [] := List.drop_eq_nil_iff.mpr (by omega)
      rw [hdrop2]
      refine ⟨hstep1, ?_⟩
      have h := hcyc (k + 1) hk
      have hmod : (k + 1 + 1) % B.length = 0 := by
        have : k + 1 + 1 = B.length := by omega
        rw [this, Nat.mod_self]
      simpa [hmod] using h

private lemma mis_nil {n : ℕ} (x : (Bool × Fin n) → Bool) (π : Equiv.Perm (Fin n)) :
    mis x π [] = 0 := rfl

private lemma foldl_altTagTail {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n))
    (x : (Bool × Fin n) → Bool) :
    ∀ (l : List (Fin n)) (prev head : Fin n) (d1 d2 : ℕ),
      IsChain (π₁.trans π₂.symm) prev head l →
      ((altTagTail π₁ l).foldl (fun st p => stepNat p.2 st (x p.1))
        (x (false, head), x (true, π₁ prev), d1, d2)).2.2.1 = d1 + mis x π₁ l ∧
      ((altTagTail π₁ l).foldl (fun st p => stepNat p.2 st (x p.1))
        (x (false, head), x (true, π₁ prev), d1, d2)).2.2.2 =
        d2 + mis x π₂ l + neOne (x (false, head)) (x (true, π₂ head))
  | [], _, _, _, _, h => False.elim h
  | [b], prev, head, d1, d2, ⟨h1, h2⟩ => by
    have hπ1 : π₂ b = π₁ prev := by have := congrArg π₂ h1; simpa using this.symm
    have hπ2 : π₂ head = π₁ b := by have := congrArg π₂ h2; simpa using this.symm
    simp only [altTagTail, List.foldl_cons, List.foldl_nil, stepNat, mis_cons, mis_nil]
    rw [← hπ1, ← hπ2]
    exact ⟨by omega, by omega⟩
  | b :: c :: rest, prev, head, d1, d2, ⟨h1, hrest⟩ => by
    have hπ1 : π₂ b = π₁ prev := by have := congrArg π₂ h1; simpa using this.symm
    change ((altTagTail π₁ (c :: rest)).foldl (fun st p => stepNat p.2 st (x p.1))
        (x (false, head), x (true, π₁ b), d1 + neOne (x (false, b)) (x (true, π₁ b)),
          d2 + neOne (x (false, b)) (x (true, π₁ prev)))).2.2.1 = _ ∧
      ((altTagTail π₁ (c :: rest)).foldl (fun st p => stepNat p.2 st (x p.1))
        (x (false, head), x (true, π₁ b), d1 + neOne (x (false, b)) (x (true, π₁ b)),
          d2 + neOne (x (false, b)) (x (true, π₁ prev)))).2.2.2 = _
    rw [← hπ1]
    rcases foldl_altTagTail π₁ π₂ x (c :: rest) b head
      (d1 + neOne (x (false, b)) (x (true, π₁ b)))
      (d2 + neOne (x (false, b)) (x (true, π₂ b))) hrest with ⟨hih1, hih2⟩
    rw [hih1, hih2, mis_cons x π₁ b (c :: rest), mis_cons x π₂ b (c :: rest)]
    exact ⟨by omega, by omega⟩

private lemma foldl_altTag {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n))
    (x : (Bool × Fin n) → Bool) (B : List (Fin n)) (hB0 : 0 < B.length)
    (hcyc : ∀ idx (h : idx < B.length),
      (π₁.trans π₂.symm) B[idx] = B[(idx + 1) % B.length]'(Nat.mod_lt _ hB0))
    (bs bp : Bool) (d1 d2 : ℕ) :
    ((altTag π₁ B).foldl (fun st p => stepNat p.2 st (x p.1)) (bs, bp, d1, d2)).2.2.1 =
      d1 + mis x π₁ B ∧
    ((altTag π₁ B).foldl (fun st p => stepNat p.2 st (x p.1)) (bs, bp, d1, d2)).2.2.2 =
      d2 + mis x π₂ B := by
  cases B with
  | nil => simp at hB0
  | cons a rest =>
    cases rest with
    | nil =>
      have h0 : (π₁.trans π₂.symm) a = a := by
        have hc := hcyc 0 (by simp)
        simpa using hc
      have hπ : π₂ a = π₁ a := by have := congrArg π₂ h0; simpa using this.symm
      simp only [altTag, List.foldl_cons, List.foldl_nil, stepNat, mis_cons, mis_nil]
      rw [hπ]
      exact ⟨by omega, by omega⟩
    | cons c rest' =>
      have hch : IsChain (π₁.trans π₂.symm) a a (c :: rest') := by
        have h := isChain_of_drop (π₁.trans π₂.symm) (a :: c :: rest') hB0 hcyc
          ((a :: c :: rest').length - 1) 0 (by simp) rfl
        simpa using h
      change ((altTagTail π₁ (c :: rest')).foldl (fun st p => stepNat p.2 st (x p.1))
          (x (false, a), x (true, π₁ a), d1 + neOne (x (false, a)) (x (true, π₁ a)), d2)).2.2.1 = _ ∧
        ((altTagTail π₁ (c :: rest')).foldl (fun st p => stepNat p.2 st (x p.1))
          (x (false, a), x (true, π₁ a), d1 + neOne (x (false, a)) (x (true, π₁ a)), d2)).2.2.2 = _
      rcases foldl_altTagTail π₁ π₂ x (c :: rest') a a
        (d1 + neOne (x (false, a)) (x (true, π₁ a))) d2 hch with ⟨hih1, hih2⟩
      rw [hih1, hih2, mis_cons x π₁ a (c :: rest'), mis_cons x π₂ a (c :: rest')]
      exact ⟨by omega, by omega⟩

private lemma foldl_blocks {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n))
    (x : (Bool × Fin n) → Bool) :
    ∀ (blocks : List (List (Fin n))),
      (∀ B ∈ blocks, ∃ hB0 : 0 < B.length,
        ∀ idx (h : idx < B.length),
          (π₁.trans π₂.symm) B[idx] = B[(idx + 1) % B.length]'(Nat.mod_lt _ hB0)) →
      ∀ (bs bp : Bool) (d1 d2 : ℕ),
      (((blocks.map (altTag π₁)).flatten).foldl
        (fun st p => stepNat p.2 st (x p.1)) (bs, bp, d1, d2)).2.2.1 =
        d1 + mis x π₁ blocks.flatten ∧
      (((blocks.map (altTag π₁)).flatten).foldl
        (fun st p => stepNat p.2 st (x p.1)) (bs, bp, d1, d2)).2.2.2 =
        d2 + mis x π₂ blocks.flatten
  | [], _, _, _, _, _ => by simp [mis]
  | B :: rest, hok, bs, bp, d1, d2 => by
    obtain ⟨hB0, hcyc⟩ := hok B (List.mem_cons_self ..)
    have hrest : ∀ B' ∈ rest, ∃ hB'0 : 0 < B'.length,
        ∀ idx (h : idx < B'.length),
          (π₁.trans π₂.symm) B'[idx] = B'[(idx + 1) % B'.length]'(Nat.mod_lt _ hB'0) :=
      fun B' hB' => hok B' (List.mem_cons_of_mem B hB')
    simp only [List.map_cons, List.flatten_cons, List.foldl_append, mis_append]
    set s1 := (altTag π₁ B).foldl (fun st p => stepNat p.2 st (x p.1)) (bs, bp, d1, d2)
    rcases foldl_altTag π₁ π₂ x B hB0 hcyc bs bp d1 d2 with ⟨h1a, h1b⟩
    have h2 := foldl_blocks π₁ π₂ x rest hrest s1.1 s1.2.1 s1.2.2.1 s1.2.2.2
    have hs1_eq : (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2) = s1 := rfl
    rw [hs1_eq] at h2
    rcases h2 with ⟨h2a, h2b⟩
    rw [h2a, h2b]
    change s1.2.2.1 + mis x π₁ rest.flatten = _ ∧ s1.2.2.2 + mis x π₂ rest.flatten = _
    have hs1a : s1.2.2.1 = d1 + mis x π₁ B := h1a
    have hs1b : s1.2.2.2 = d2 + mis x π₂ B := h1b
    exact ⟨by omega, by omega⟩

private lemma pair_stream_exists {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) :
    ∃ (order : Fin (2 * n) ≃ Bool × Fin n)
      (tagAt : Fin (2 * n) → StepTag),
      ∀ x : (Bool × Fin n) → Bool,
        let st := (List.finRange (2 * n)).foldl
          (fun st k => stepS (tagAt k) st (x (order k)))
          (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩)
        st.2.2.1.val = (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π₁ i))).card ∧
        st.2.2.2.val = (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π₂ i))).card := by
  let σ : Equiv.Perm (Fin n) := π₁.trans π₂.symm
  obtain ⟨blocks, hblocks_ok, hflat_nd, hflat_mem⟩ :=
    decomp_cycles σ Finset.univ (fun _ _ => Finset.mem_univ _)
  let vertsTag : List ((Bool × Fin n) × StepTag) := (blocks.map (altTag π₁)).flatten
  let verts : List (Bool × Fin n) := vertsTag.map Prod.fst
  have hverts_eq : verts = blocks.flatten.flatMap (fun i => [(false, i), (true, π₁ i)]) := by
    have haux : ∀ bs : List (List (Fin n)),
        ((bs.map (altTag π₁)).flatten).map Prod.fst =
        bs.flatten.flatMap (fun i => [(false, i), (true, π₁ i)]) := by
      intro bs
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        simp only [List.map_cons, List.flatten_cons, List.map_append, List.flatMap_append,
          altTag_fst, ih]
    exact haux blocks
  have hflat_len : blocks.flatten.length = n := by
    have h1 := List.toFinset_card_of_nodup hflat_nd
    have h2 : blocks.flatten.toFinset = Finset.univ := by
      ext i; simp [hflat_mem]
    rw [h2, Finset.card_univ, Fintype.card_fin] at h1
    exact h1.symm
  have hverts_len : verts.length = 2 * n := by
    rw [hverts_eq]
    have haux : ∀ l : List (Fin n),
        (l.flatMap (fun i => [(false, i), (true, π₁ i)])).length = 2 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a ls ih => simp [ih]; omega
    rw [haux, hflat_len]
  have hvt_len : vertsTag.length = 2 * n := by
    have h : verts.length = vertsTag.length := List.length_map ..
    omega
  have hverts_nd : verts.Nodup := by
    rw [hverts_eq]
    have haux : ∀ l : List (Fin n), l.Nodup →
        (l.flatMap (fun i => [(false, i), (true, π₁ i)])).Nodup := by
      intro l hl
      induction l with
      | nil => simp
      | cons a ls ih =>
        have ha : a ∉ ls := (List.nodup_cons.mp hl).1
        have hls : ls.Nodup := (List.nodup_cons.mp hl).2
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
        refine ⟨?_, ?_, ih hls⟩
        · intro hmem
          simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hF, _⟩ | ⟨i, hi, ⟨_, hEq⟩ | ⟨hF, _⟩⟩
          · exact Bool.false_ne_true hF
          · subst hEq; exact ha hi
          · exact Bool.false_ne_true hF
        · simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
            not_exists, not_and]
          intro i hi hmem
          rcases hmem with ⟨htrue, _⟩ | ⟨_, hMeq⟩
          · exact Bool.false_ne_true.symm htrue
          · exact ha (π₁.injective hMeq ▸ hi)
    exact haux _ hflat_nd
  have hverts_mem : ∀ v : Bool × Fin n, v ∈ verts := by
    intro v
    rw [hverts_eq, List.mem_flatMap]
    rcases v with ⟨b, idx⟩
    cases b
    · exact ⟨idx, (hflat_mem idx).mpr (Finset.mem_univ _), by simp⟩
    · exact ⟨π₁.symm idx, (hflat_mem _).mpr (Finset.mem_univ _), by simp⟩
  let toV : Fin (2 * n) → Bool × Fin n := fun k => verts[k.val]'(by rw [hverts_len]; exact k.isLt)
  have htoV_bij : Function.Bijective toV := by
    constructor
    · intro k1 k2 heq
      exact Fin.ext ((List.Nodup.getElem_inj_iff hverts_nd).mp heq)
    · intro v
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp (hverts_mem v)
      exact ⟨⟨k, by rw [← hverts_len]; exact hk⟩, hget⟩
  let order : Fin (2 * n) ≃ Bool × Fin n := Equiv.ofBijective toV htoV_bij
  let tagAt : Fin (2 * n) → StepTag := fun k => (vertsTag[k.val]'(by rw [hvt_len]; exact k.isLt)).2
  refine ⟨order, tagAt, fun x => ?_⟩
  have hmap_eq : (List.finRange (2 * n)).map (fun k => (order k, tagAt k)) = vertsTag := by
    apply List.ext_getElem
    · simp [hvt_len]
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_finRange]
      apply Prod.ext
      · simp [order, toV, verts]
      · simp [tagAt]
  have hfold_eq :
      (List.finRange (2 * n)).foldl (fun st k => stepS (tagAt k) st (x (order k)))
        (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩) =
      vertsTag.foldl (fun st p => stepS p.2 st (x p.1))
        (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩) := by
    rw [← hmap_eq, List.foldl_map]
  rw [hfold_eq]
  have hnat := foldl_blocks π₁ π₂ x blocks
    (fun B hB => ⟨(hblocks_ok B hB).1, (hblocks_ok B hB).2.2.2.2⟩) false false 0 0
  have hmis_card : ∀ π : Equiv.Perm (Fin n),
      mis x π blocks.flatten =
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π i))).card := by
    intro π
    unfold mis
    rw [countP_eq_card_filter_toFinset _ _ hflat_nd]
    have htf : blocks.flatten.toFinset = Finset.univ := by ext i; simp [hflat_mem]
    have hfeq : Finset.univ.filter (fun i : Fin n => decide (x (false, i) ≠ x (true, π i)) = true) =
        Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π i)) := by
      ext i; simp
    rw [htf, hfeq]
  have hcard_le : ∀ π : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π i))).card ≤ n := by
    intro π
    calc (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π i))).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  have hd1_eq : (vertsTag.foldl (fun st p => stepNat p.2 st (x p.1)) (false, false, 0, 0)).2.2.1 =
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π₁ i))).card := by
    have h := hnat.1
    rw [zero_add, hmis_card] at h
    exact h
  have hd2_eq : (vertsTag.foldl (fun st p => stepNat p.2 st (x p.1)) (false, false, 0, 0)).2.2.2 =
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, π₂ i))).card := by
    have h := hnat.2
    rw [zero_add, hmis_card] at h
    exact h
  have hsim := foldl_stepS_eq_stepNat x vertsTag
    (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩)
    (by rw [hd1_eq]; exact hcard_le π₁)
    (by rw [hd2_eq]; exact hcard_le π₂)
  exact ⟨hsim.2.2.1.trans hd1_eq, hsim.2.2.2.trans hd2_eq⟩

-- ============================================================================
-- Part B: Weight-to-seed allocation (weights → feasible)
-- ============================================================================

private lemma card_filter_getElem_eq_countP {α : Type*} [DecidableEq α] :
    ∀ (L : List α) (a : α),
      (Finset.univ.filter (fun k : Fin L.length => L[k.val] = a)).card =
      L.countP (fun y => decide (y = a))
  | [], _ => by simp
  | x :: xs, a => by
    rw [List.countP_cons]
    let e : Fin (xs.length + 1) ≃ Option (Fin xs.length) := finSuccEquiv xs.length
    let fOpt : Option (Fin xs.length) → α := fun o => o.elim x (fun j => xs[j.val])
    have hbij : (Finset.univ.filter (fun k : Fin (x :: xs).length => (x :: xs)[k.val] = a)).card =
        (Finset.univ.filter (fun o : Option (Fin xs.length) => fOpt o = a)).card := by
      refine Finset.card_bij (fun k _ => e k) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        cases k using Fin.cases with
        | zero =>
          simp only [e, finSuccEquiv_zero, fOpt, Option.elim_none]
          simpa using hk
        | succ j =>
          simp only [e, finSuccEquiv_succ, fOpt, Option.elim_some]
          simpa using hk
      · intro k1 _ k2 _ h; exact e.injective h
      · intro o ho
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
        refine ⟨e.symm o, ?_, e.apply_symm_apply o⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases o with
        | none =>
          simp only [e, finSuccEquiv_symm_none]
          simpa [fOpt] using ho
        | some j =>
          simp only [e, finSuccEquiv_symm_some]
          simpa [fOpt] using ho
    rw [hbij]
    have hopt : (Finset.univ.filter (fun o : Option (Fin xs.length) => fOpt o = a)).card =
        (Finset.univ.filter (fun j : Fin xs.length => xs[j.val] = a)).card +
        (if x = a then 1 else 0) := by
      let S := Finset.univ.filter (fun o : Option (Fin xs.length) => fOpt o = a)
      let S1 := (Finset.univ.filter (fun j : Fin xs.length => xs[j.val] = a)).map
        ⟨some, Option.some_injective _⟩
      have hcard1 : S1.card = (Finset.univ.filter (fun j : Fin xs.length => xs[j.val] = a)).card :=
        Finset.card_map _
      by_cases hxa : x = a
      · have hSeq : S = insert none S1 := by
          ext o; cases o <;> simp [S, S1, fOpt, hxa]
        have hnot : (none : Option (Fin xs.length)) ∉ S1 := by simp [S1]
        rw [show S.card = (insert none S1).card by rw [hSeq],
          Finset.card_insert_of_notMem hnot, hcard1, ite_eq_left hxa]
      · have hSeq : S = S1 := by
          ext o; cases o <;> simp [S, S1, fOpt, hxa]
        rw [show S.card = S1.card by rw [hSeq], hcard1, ite_eq_right hxa, Nat.add_zero]
    rw [hopt, card_filter_getElem_eq_countP xs a]
    by_cases hxa : x = a <;> simp [hxa]

private lemma countP_flatMap_replicate_some {α : Type*} [DecidableEq α] (w : α → ℕ) :
    ∀ (l : List α),
      (l.flatMap (fun h => List.replicate (w h) (some h))).countP (fun y => decide (y = none)) = 0 ∧
      (∀ h, l.Nodup →
        (l.flatMap (fun h' => List.replicate (w h') (some h'))).countP (fun y => decide (y = some h)) =
          if h ∈ l then w h else 0)
  | [] => ⟨by simp, fun _ _ => by simp⟩
  | a :: rest => by
    have ih := countP_flatMap_replicate_some w rest
    constructor
    · simp only [List.flatMap_cons, List.countP_append, ih.1, Nat.add_zero, List.countP_replicate]
      simp
    · intro h hnd
      rcases List.nodup_cons.mp hnd with ⟨ha, hrest⟩
      simp only [List.flatMap_cons, List.countP_append, ih.2 h hrest, List.countP_replicate]
      by_cases hha : h = a
      · subst hha
        simp [ha]
      · simp [hha, Ne.symm hha]

private lemma length_flatMap_replicate {α : Type*} (w : α → ℕ) :
    ∀ (l : List α),
      (l.flatMap (fun h => List.replicate (w h) (some h))).length = (l.map w).sum
  | [] => rfl
  | a :: rest => by
    simp only [List.flatMap_cons, List.length_append, List.length_replicate,
      List.map_cons, List.sum_cons, length_flatMap_replicate w rest]

private lemma list_sum_map_nodup {α : Type*} [DecidableEq α] (w : α → ℕ) :
    ∀ l : List α, l.Nodup → (l.map w).sum = ∑ h ∈ l.toFinset, w h
  | [], _ => by simp
  | a :: rest, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨ha, hrest⟩
    have ha' : a ∉ rest.toFinset := by simpa using ha
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert ha',
      list_sum_map_nodup w rest hrest]

private lemma list_sum_map_finRange (d : ℕ) (w : Fin d → ℕ) :
    ((List.finRange d).map w).sum = ∑ h : Fin d, w h := by
  rw [list_sum_map_nodup w (List.finRange d) (List.nodup_finRange d), List.toFinset_finRange]

private lemma seed_allocation {d R u : ℕ} (hd : 0 < d) (huR : u ≤ R)
    (w : Fin d → ℕ) (hw_sum : (∑ h : Fin d, w h) = R - u) :
    ∃ (active : Fin R → Bool) (choose : Fin R → Fin d),
      (Finset.univ.filter (fun s : Fin R => active s = false)).card = u ∧
      ∀ h : Fin d, (Finset.univ.filter (fun s : Fin R => active s = true ∧ choose s = h)).card = w h := by
  let L : List (Option (Fin d)) :=
    ((List.finRange d).flatMap (fun h => List.replicate (w h) (some h))) ++ List.replicate u none
  have hL_len : L.length = R := by
    simp only [L, List.length_append, List.length_replicate, length_flatMap_replicate,
      list_sum_map_finRange, hw_sum]
    omega
  let getL : Fin R → Option (Fin d) := fun s => L[s.val]'(by rw [hL_len]; exact s.isLt)
  let active : Fin R → Bool := fun s => (getL s).isSome
  let choose : Fin R → Fin d := fun s => (getL s).getD ⟨0, hd⟩
  have hcount_getL : ∀ o : Option (Fin d),
      (Finset.univ.filter (fun s : Fin R => getL s = o)).card =
      L.countP (fun y => decide (y = o)) := by
    intro o
    let e : Fin R ≃ Fin L.length := finCongr hL_len.symm
    have hbij : (Finset.univ.filter (fun s : Fin R => getL s = o)).card =
        (Finset.univ.filter (fun k : Fin L.length => L[k.val] = o)).card := by
      refine Finset.card_bij (fun s _ => e s) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        simpa [getL, e] using hs
      · intro s1 _ s2 _ h; exact e.injective h
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨e.symm k, ?_, e.apply_symm_apply k⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [getL, e] using hk
    exact hbij.trans (card_filter_getElem_eq_countP L o)
  refine ⟨active, choose, ?_, ?_⟩
  · have hfilt : Finset.univ.filter (fun s : Fin R => active s = false) =
        Finset.univ.filter (fun s : Fin R => getL s = none) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, active]
      cases getL s <;> simp
    rw [hfilt, hcount_getL]
    simp only [L, List.countP_append, (countP_flatMap_replicate_some w (List.finRange d)).1,
      zero_add, List.countP_replicate, decide_true, ↓reduceIte]
  · intro h
    have hfilt : Finset.univ.filter (fun s : Fin R => active s = true ∧ choose s = h) =
        Finset.univ.filter (fun s : Fin R => getL s = some h) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, active, choose]
      cases getL s <;> simp
    rw [hfilt, hcount_getL]
    simp only [L, List.countP_append,
      (countP_flatMap_replicate_some w (List.finRange d)).2 h (List.nodup_finRange d),
      List.mem_finRange, ↓reduceIte, List.countP_replicate]
    simp

private theorem forward_direction
    (n r d R u v : ℕ) (_hr2 : 2 ≤ r) (hd : 0 < d) (_hR : 0 < R) (huR : u ≤ R)
    (M : Fin r → Equiv.Perm (Fin n)) (menu : Fin d → Fin r × Fin r) :
    let V := Bool × Fin n
    let X := V → Bool
    let test := fun (x : X) (j : Fin r) =>
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      decide (16 * Nat.dist (2*D) n ≤ n)
    let cap := 4*(n+1)^2
    let feasible := ∃ (choose : Fin R → Fin d) (decode : Fin R → Bool → Bool → Bool)
      (order : Fin d → (Fin (2*n) ≃ V)) (init : Fin R → Fin cap)
      (step : Fin R → Fin (2*n) → Fin cap → Bool → Fin cap) (out : Fin R → Fin cap → Bool),
      ∀ x : X,
        let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
          (fun st k => step seed k st (x (order (choose seed) k))) (init seed))
        (∀ seed : Fin R, answer seed = decode seed (test x (menu (choose seed)).1)
          (test x (menu (choose seed)).2)) ∧
        ((∀ j : Fin r, test x j = true) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = false)).card ≤ u) ∧
        ((∃ j : Fin r, test x j = false) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = true)).card ≤ v)
    let weights := ∃ w : Fin d → ℕ, (∑ h : Fin d, w h) = R-u ∧
      ∀ j : Fin r, (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) ≤ v
    weights → feasible := by
  intro V X test cap feasible weights ⟨w, hw_sum, hw_cov⟩
  obtain ⟨active, choose, hcard_false, hcard_h⟩ := seed_allocation hd huR w hw_sum
  have hpair : ∀ h : Fin d,
      ∃ (ord : Fin (2 * n) ≃ V) (tagAt : Fin (2 * n) → StepTag),
        ∀ x : X,
          let st := (List.finRange (2 * n)).foldl
            (fun st k => stepS (tagAt k) st (x (ord k)))
            (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩)
          st.2.2.1.val = (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M (menu h).1 i))).card ∧
          st.2.2.2.val = (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M (menu h).2 i))).card :=
    fun h => pair_stream_exists (M (menu h).1) (M (menu h).2)
  choose order tagAt hpair_spec using hpair
  let e : SState n ≃ Fin cap := stateEquiv n
  let initS : SState n := (false, false, ⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩)
  let decode : Fin R → Bool → Bool → Bool := fun seed b1 b2 => if active seed then b1 && b2 else false
  let init : Fin R → Fin cap := fun _ => e initS
  let step : Fin R → Fin (2 * n) → Fin cap → Bool → Fin cap :=
    fun seed k st bit => e (stepS (tagAt (choose seed) k) (e.symm st) bit)
  let out : Fin R → Fin cap → Bool := fun seed st =>
    if active seed then
      let s := e.symm st
      decide (16 * Nat.dist (2 * s.2.2.1.val) n ≤ n) &&
      decide (16 * Nat.dist (2 * s.2.2.2.val) n ≤ n)
    else false
  refine ⟨choose, decode, order, init, step, out, fun x => ?_⟩
  intro answer
  have hans : ∀ seed : Fin R,
      answer seed = decode seed (test x (menu (choose seed)).1) (test x (menu (choose seed)).2) := by
    intro seed
    dsimp only [answer, out, init, step, decode]
    by_cases ha : active seed = true
    · simp only [ha, ↓reduceIte]
      have hfold := foldl_conj e
        (fun k st => stepS (tagAt (choose seed) k) st (x (order (choose seed) k)))
        (List.finRange (2 * n)) initS
      rw [hfold, Equiv.symm_apply_apply]
      have hsp := hpair_spec (choose seed) x
      dsimp only [initS] at hsp ⊢
      rw [hsp.1, hsp.2]
    · have haf : active seed = false := Bool.eq_false_iff.mpr ha
      simp [haf]
  refine ⟨hans, ?_, ?_⟩
  · intro hall
    have hsub : Finset.univ.filter (fun seed : Fin R => answer seed = false) ⊆
        Finset.univ.filter (fun seed : Fin R => active seed = false) := by
      intro seed hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [hans seed] at hs
      dsimp only [decode] at hs
      rw [hall (menu (choose seed)).1, hall (menu (choose seed)).2] at hs
      cases ha : active seed
      · rfl
      · simp [ha] at hs
    calc (Finset.univ.filter (fun seed : Fin R => answer seed = false)).card
        ≤ (Finset.univ.filter (fun seed : Fin R => active seed = false)).card :=
          Finset.card_le_card hsub
      _ = u := hcard_false
  · rintro ⟨j, hj⟩
    let Uncov : Finset (Fin d) := Finset.univ.filter (fun h : Fin d => ¬(j = (menu h).1 ∨ j = (menu h).2))
    have hsub : Finset.univ.filter (fun seed : Fin R => answer seed = true) ⊆
        Finset.univ.filter (fun seed : Fin R => active seed = true ∧ choose seed ∈ Uncov) := by
      intro seed hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Uncov] at hs ⊢
      rw [hans seed] at hs
      dsimp only [decode] at hs
      cases ha : active seed
      · simp [ha] at hs
      · simp only [ha, ↓reduceIte, Bool.and_eq_true] at hs
        refine ⟨rfl, ?_⟩
        rintro (h1 | h2)
        · rw [← h1, hj] at hs; exact Bool.false_ne_true hs.1
        · rw [← h2, hj] at hs; exact Bool.false_ne_true hs.2
    have hcard_uncov :
        (Finset.univ.filter (fun seed : Fin R => active seed = true ∧ choose seed ∈ Uncov)).card =
        ∑ h ∈ Uncov, w h := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := choose)
        (s := Finset.univ.filter (fun seed : Fin R => active seed = true ∧ choose seed ∈ Uncov))
        (t := Uncov) (fun seed hs => (Finset.mem_filter.mp hs).2.2)
      rw [hfib]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [← hcard_h h]
      congr 1
      ext seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨ha, rfl⟩
      · rintro ⟨ha, rfl⟩; exact ⟨⟨ha, hh⟩, rfl⟩
    have hsum_eq : (∑ h ∈ Uncov, w h) =
        ∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2)]
      have hz : (∑ h ∈ Finset.univ.filter (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2),
          if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) = 0 :=
        Finset.sum_eq_zero fun h hh => by simp [(Finset.mem_filter.mp hh).2]
      have hnz : (∑ h ∈ Uncov, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) =
          ∑ h ∈ Uncov, w h :=
        Finset.sum_congr rfl fun h hh => by simp [(Finset.mem_filter.mp hh).2]
      change (∑ h ∈ Uncov, w h) =
        (∑ h ∈ Finset.univ.filter (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2),
          if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) +
        (∑ h ∈ Uncov, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h)
      rw [hz, zero_add, hnz]
    calc (Finset.univ.filter (fun seed : Fin R => answer seed = true)).card
        ≤ (Finset.univ.filter (fun seed : Fin R => active seed = true ∧ choose seed ∈ Uncov)).card :=
          Finset.card_le_card hsub
      _ = ∑ h ∈ Uncov, w h := hcard_uncov
      _ = ∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h := hsum_eq
      _ ≤ v := hw_cov j

-- ============================================================================
-- Part C: Singleton restriction / all-pass & singleton-fail words (from L_pcx_300)
-- ============================================================================

private def sgn (b : Bool) : Int := if b then -1 else 1

private lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> decide

private lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> decide

private lemma sgn_ne_eq (a b : Bool) : (if a ≠ b then (1 : Int) else -1) = -(sgn a * sgn b) := by
  cases a <;> cases b <;> decide

private lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> decide

private lemma sum_prod4_zero {n : Nat} (u1 u2 v1 v2 : Fin n)
    (hvu1 : v1 ≠ u1) (hvu2 : v1 ≠ u2) (hvv2 : v1 ≠ v2) :
    (∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) = 0 := by
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun a i => if i = v1 then !a i else a i
  have hinv : ∀ a, flip (flip a) = a := by
    intro a; funext i
    dsimp only [flip]
    by_cases hi : i = v1
    · simp [hi]
    · simp [hi]
  have hbij : Function.Bijective flip :=
    ⟨fun a b h => by have := congrArg flip h; rwa [hinv, hinv] at this, fun a => ⟨flip a, hinv a⟩⟩
  have hneg : ∀ a : Fin n → Bool,
      sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2) =
      -(sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) := by
    intro a
    dsimp only [flip]
    have h1 : u1 ≠ v1 := Ne.symm hvu1
    have h2 : u2 ≠ v1 := Ne.symm hvu2
    have h3 : v2 ≠ v1 := Ne.symm hvv2
    simp only [h1, h2, h3, ↓reduceIte, sgn_not]
    ring
  have hsum_eq : (∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) =
      ∑ a : Fin n → Bool, sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2) := by
    symm
    exact Fintype.sum_bijective flip hbij _ _ (fun _ => rfl)
  have hsum_neg : (∑ a : Fin n → Bool, sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2)) =
      -(∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) := by
    simp only [hneg, Finset.sum_neg_distrib]
  linarith

private lemma second_moment_perm {n : Nat} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) :
    let Move := Finset.univ.filter (fun i : Fin n => π i ≠ i)
    (∑ a : Fin n → Bool, (∑ i ∈ Move, -(sgn (mask (π i)) * sgn (a i) * sgn (a (π i)))) ^ 2) ≤
      (2 * n : Int) * (2 ^ n : Int) := by
  intro Move
  have hexp : ∀ a : Fin n → Bool,
      (∑ i ∈ Move, -(sgn (mask (π i)) * sgn (a i) * sgn (a (π i)))) ^ 2 =
      ∑ u ∈ Move, ∑ v ∈ Move,
        (sgn (mask (π u)) * sgn (mask (π v))) * (sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
    intro a
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : (∑ u ∈ Move, ∑ a : Fin n → Bool, ∑ v ∈ Move,
      (sgn (mask (π u)) * sgn (mask (π v))) * (sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))) =
      ∑ u ∈ Move, ∑ v ∈ Move,
        (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ u ∈ Move,
      (∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))) ≤
      2 * (2 ^ n : Int) := by
    intro u hu
    let S2 : Finset (Fin n) := Move.filter (fun v => v = u ∨ v = π u)
    have hrest : ∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) =
        ∑ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun v hv hvnot => ?_
      have hne : ¬(v = u ∨ v = π u) := by
        intro h; exact hvnot (Finset.mem_filter.mpr ⟨hv, h⟩)
      have hvu : v ≠ u := fun h => hne (Or.inl h)
      have hvpu : v ≠ π u := fun h => hne (Or.inr h)
      have hvpv : v ≠ π v := Ne.symm (Finset.mem_filter.mp hv).2
      rw [sum_prod4_zero u (π u) v (π v) hvu hvpu hvpv, mul_zero]
    rw [hrest]
    have hterm : ∀ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) ≤ (2 ^ n : Int) := by
      intro v _
      have habs : |(sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))| ≤ (2 ^ n : Int) := by
        rw [abs_mul, abs_mul, abs_sgn, abs_sgn, mul_one, one_mul]
        calc |∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))|
            ≤ ∑ a : Fin n → Bool, |sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ _a : Fin n → Bool, (1 : Int) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              simp only [abs_mul, abs_sgn, mul_one]
          _ = (2 ^ n : Int) := by
              simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
      exact le_trans (le_abs_self _) habs
    have hS2_card : S2.card ≤ 2 := by
      have hsub : S2 ⊆ ({u, π u} : Finset (Fin n)) := by
        intro v hv
        rcases (Finset.mem_filter.mp hv).2 with rfl | rfl <;> simp
      calc S2.card ≤ ({u, π u} : Finset (Fin n)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    calc ∑ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))
        ≤ ∑ _v ∈ S2, (2 ^ n : Int) := Finset.sum_le_sum hterm
      _ = (S2.card : Int) * (2 ^ n : Int) := by simp
      _ ≤ 2 * (2 ^ n : Int) := by
          have h2p : (0 : Int) ≤ (2 ^ n : Int) := by positivity
          have hc : (S2.card : Int) ≤ 2 := by exact_mod_cast hS2_card
          nlinarith
  have hM_card : Move.card ≤ n := by
    have := Finset.card_le_univ Move
    simpa [Fintype.card_fin] using this
  calc ∑ u ∈ Move, ∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))
      ≤ ∑ _u ∈ Move, (2 * (2 ^ n : Int)) := Finset.sum_le_sum hinner
    _ = (Move.card : Int) * (2 * (2 ^ n : Int)) := by simp
    _ ≤ (n : Int) * (2 * (2 ^ n : Int)) := by
        have h2p : (0 : Int) ≤ 2 * (2 ^ n : Int) := by positivity
        have hc : (Move.card : Int) ≤ (n : Int) := by exact_mod_cast hM_card
        nlinarith
    _ = (2 * n : Int) * (2 ^ n : Int) := by ring

private lemma nat_dist_eq_abs_int (a b : Nat) : (Nat.dist a b : Int) = |(a : Int) - (b : Int)| := by
  rw [Nat.dist]
  by_cases h : a ≤ b
  · have h1 : a - b = 0 := Nat.sub_eq_zero_of_le h
    rw [h1, zero_add, Int.ofNat_sub h, abs_of_nonpos (by omega)]
    ring
  · have h2 : b - a = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [h2, add_zero, Int.ofNat_sub (by omega), abs_of_nonneg (by omega)]

private lemma card_filter_imbalance {n : Nat} (p : Fin n → Bool) :
    (2 * (Finset.univ.filter (fun i : Fin n => p i = true)).card : Int) - (n : Int) =
      ∑ i : Fin n, if p i = true then (1 : Int) else -1 := by
  let P := Finset.univ.filter (fun i : Fin n => p i = true)
  let Q := Finset.univ.filter (fun i : Fin n => p i ≠ true)
  have hsplit : (∑ i : Fin n, if p i = true then (1 : Int) else -1) =
      (∑ i ∈ P, if p i = true then (1 : Int) else -1) + (∑ i ∈ Q, if p i = true then (1 : Int) else -1) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => p i = true)]
  have hP : (∑ i ∈ P, if p i = true then (1 : Int) else -1) = (P.card : Int) := by
    calc (∑ i ∈ P, if p i = true then (1 : Int) else -1)
        = ∑ _i ∈ P, (1 : Int) := Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      _ = (P.card : Int) := by simp
  have hQ : (∑ i ∈ Q, if p i = true then (1 : Int) else -1) = -(Q.card : Int) := by
    calc (∑ i ∈ Q, if p i = true then (1 : Int) else -1)
        = ∑ _i ∈ Q, (-1 : Int) := Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      _ = -(Q.card : Int) := by simp
  have hcard : P.card + Q.card = n := by
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : P ∪ Q = Finset.univ := by
      ext i
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (em (p i = true))
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  rw [hsplit, hP, hQ]
  change (2 * (P.card : Int)) - (n : Int) = (P.card : Int) + -(Q.card : Int)
  omega

private lemma card_filter_diff_le {n : Nat} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (B : Finset (Fin n)) (hagree : ∀ i : Fin n, i ∉ B → (p i ↔ q i)) :
    ((Finset.univ.filter p).card : Int) - ((Finset.univ.filter q).card : Int) ≤ (B.card : Int) ∧
    ((Finset.univ.filter q).card : Int) - ((Finset.univ.filter p).card : Int) ≤ (B.card : Int) := by
  have hsub1 : Finset.univ.filter p ⊆ Finset.univ.filter q ∪ B := by
    intro i hi
    by_cases hB : i ∈ B
    · exact Finset.mem_union_right _ hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hagree i hB).mp (Finset.mem_filter.mp hi).2⟩)
  have hsub2 : Finset.univ.filter q ⊆ Finset.univ.filter p ∪ B := by
    intro i hi
    by_cases hB : i ∈ B
    · exact Finset.mem_union_right _ hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hagree i hB).mpr (Finset.mem_filter.mp hi).2⟩)
  have h1 : (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card + B.card :=
    le_trans (Finset.card_le_card hsub1) (Finset.card_union_le _ _)
  have h2 : (Finset.univ.filter q).card ≤ (Finset.univ.filter p).card + B.card :=
    le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _)
  omega

private lemma singleton_restrict (n r : Nat) (M : Fin r → Equiv.Perm (Fin n)) (target : Fin r) (T : Finset (Fin n))
    (hrn : 8192 * r < n) (hTn : 128 * T.card ≤ n)
    (hfix : ∀ j : Fin r, j ≠ target →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M target i)).card ≤ n) :
    let V := Bool × Fin n
    let dist := fun (x : V → Bool) (j : Fin r) =>
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card
    let central := fun D : Nat => 16 * Nat.dist (2 * D) n ≤ n
    ∃ base : V → Bool, ∀ x : V → Bool,
      (∀ i : Fin n, i ∉ T →
        x (false, i) = base (false, i) ∧ x (true, M target i) = base (true, M target i)) →
      dist x target = 17 * n / 32 + (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card ∧
      (∀ j : Fin r, j ≠ target → central (dist x j)) ∧
      ((∀ j : Fin r, central (dist x j)) ↔ ∀ i ∈ T, x (false, i) = x (true, M target i)) := by
  intro V dist central
  have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h0 => by have := target.isLt; omega)
  have hn_big : 8192 < n := by omega
  have hTc_card : 17 * n / 32 ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hTc_card
  let mask : Fin n → Bool := fun i => decide (i ∈ S)
  let π : Fin r → Equiv.Perm (Fin n) := fun j => (M j).trans (M target).symm
  let Move : Fin r → Finset (Fin n) := fun j => Finset.univ.filter (fun i : Fin n => π j i ≠ i)
  let Y : Fin r → (Fin n → Bool) → Int := fun j a =>
    ∑ i ∈ Move j, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))
  let Others : Finset (Fin r) := Finset.univ.erase target
  have hsum_all : (∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2) ≤
      (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ Others, ∑ a : Fin n → Bool, (Y j a) ^ 2
        ≤ ∑ _j ∈ Others, ((2 * n : Int) * (2 ^ n : Int)) :=
          Finset.sum_le_sum fun j _ => second_moment_perm (π j) mask
      _ = (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) := by simp
  have hO_card : Others.card < r := by
    have h1 : Others.card = r - 1 := by
      simp [Others, Finset.card_erase_of_mem (Finset.mem_univ target), Fintype.card_fin]
    omega
  have hex_a : ∃ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 ≤ (2 * r * n : Int) := by
    by_contra hnone
    push Not at hnone
    have hgt : (2 ^ n : Int) * ((2 * r * n : Int)) < ∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 := by
      have hcard_a : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
      calc (2 ^ n : Int) * (2 * r * n : Int)
          = ∑ _a : Fin n → Bool, (2 * r * n : Int) := by simp [hcard_a]
        _ < ∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => hnone a
    have hle2 : (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) ≤ (2 ^ n : Int) * (2 * r * n : Int) := by
      have hO : (Others.card : Int) ≤ (r : Int) := by exact_mod_cast le_of_lt hO_card
      have h2np : (0 : Int) ≤ (2 * n : Int) * (2 ^ n : Int) := by positivity
      calc (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int))
          ≤ (r : Int) * ((2 * n : Int) * (2 ^ n : Int)) := mul_le_mul_of_nonneg_right hO h2np
        _ = (2 ^ n : Int) * (2 * r * n : Int) := by ring
    linarith
  rcases hex_a with ⟨a, ha_bound⟩
  let base : V → Bool := fun p =>
    match p with
    | (false, i) => a i
    | (true, k) => xor (a ((M target).symm k)) (mask ((M target).symm k))
  refine ⟨base, fun x hagree => ?_⟩
  have hdist_target : dist x target = 17 * n / 32 + (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card := by
    let F := Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M target i))
    let FT := T.filter (fun i : Fin n => x (false, i) ≠ x (true, M target i))
    have hF_eq : F = S ∪ FT := by
      ext i
      simp only [F, FT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hiT : i ∈ T
      · have hiS : i ∉ S := fun h => (Finset.mem_sdiff.mp (hS_sub h)).2 hiT
        simp [hiT, hiS]
      · rcases hagree i hiT with ⟨h1, h2⟩
        have hbase_ne : (base (false, i) ≠ base (true, M target i)) ↔ i ∈ S := by
          dsimp only [base, mask]
          simp only [Equiv.symm_apply_apply]
          cases a i <;> by_cases hS : i ∈ S <;> simp [hS]
        rw [h1, h2, hbase_ne]
        simp [hiT]
    have hdisj : Disjoint S FT := by
      rw [Finset.disjoint_left]
      intro i hiS hiFT
      exact (Finset.mem_sdiff.mp (hS_sub hiS)).2 (Finset.mem_filter.mp hiFT).1
    change F.card = 17 * n / 32 + FT.card
    rw [hF_eq, Finset.card_union_of_disjoint hdisj, hS_card]
  have hother : ∀ j : Fin r, j ≠ target → central (dist x j) := by
    intro j hj
    have hjO : j ∈ Others := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hY_sq : (Y j a) ^ 2 ≤ (2 * r * n : Int) := by
      have hsingle : (Y j a) ^ 2 ≤ ∑ j' ∈ Others, (Y j' a) ^ 2 :=
        Finset.single_le_sum (fun j' _ => sq_nonneg (Y j' a)) hjO
      exact le_trans hsingle ha_bound
    have h64Y : 64 * |Y j a| < (n : Int) := by
      have hsq_lt : (64 * |Y j a|) ^ 2 < (n : Int) ^ 2 := by
        have h1 : (64 * |Y j a|) ^ 2 = 4096 * (Y j a) ^ 2 := by rw [mul_pow, sq_abs]; ring
        have h2 : (8192 * r : Int) < (n : Int) := by exact_mod_cast hrn
        have hn0 : (0 : Int) < (n : Int) := by omega
        nlinarith
      nlinarith [abs_nonneg (Y j a)]
    let Fix := Finset.univ.filter (fun i : Fin n => M j i = M target i)
    have hFix_eq : Fix = Finset.univ.filter (fun i : Fin n => ¬(π j i ≠ i)) := by
      ext i
      simp only [Fix, π, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Equiv.trans_apply]
      constructor
      · intro h; rw [h, Equiv.symm_apply_apply]
      · intro h; have := congrArg (M target) h; simpa using this
    have hbase_imb : |(2 * dist base j : Int) - (n : Int)| ≤ (Fix.card : Int) + |Y j a| := by
      have hcard_eq : (2 * dist base j : Int) - (n : Int) =
          ∑ i : Fin n, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i))) := by
        have h1 := card_filter_imbalance (fun i : Fin n => decide (base (false, i) ≠ base (true, M j i)))
        have hf : Finset.univ.filter (fun i : Fin n => decide (base (false, i) ≠ base (true, M j i)) = true) =
            Finset.univ.filter (fun i : Fin n => base (false, i) ≠ base (true, M j i)) := by
          ext i; simp
        rw [hf] at h1
        change (2 * (Finset.univ.filter (fun i : Fin n => base (false, i) ≠ base (true, M j i))).card : Int) - (n : Int) = _
        rw [h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [decide_eq_true_eq, sgn_ne_eq]
        dsimp only [base, π]
        simp only [Equiv.trans_apply, sgn_xor]
        ring
      rw [hcard_eq]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => π j i ≠ i)]
      have hM_def : (∑ i ∈ Finset.univ.filter (fun i : Fin n => π j i ≠ i),
          -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))) = Y j a := rfl
      rw [hM_def, ← hFix_eq]
      have hF_abs : |∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))| ≤ (Fix.card : Int) := by
        calc |∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))|
            ≤ ∑ i ∈ Fix, |-(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ _i ∈ Fix, (1 : Int) := Finset.sum_congr rfl fun i _ => by simp [abs_neg, abs_mul, abs_sgn]
          _ = (Fix.card : Int) := by simp
      have htri := abs_add_le (Y j a) (∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i))))
      linarith
    let B : Finset (Fin n) := T ∪ T.map (π j).symm.toEmbedding
    have hB_card : B.card ≤ 2 * T.card := by
      calc B.card ≤ T.card + (T.map (π j).symm.toEmbedding).card := Finset.card_union_le _ _
        _ = T.card + T.card := by rw [Finset.card_map]
        _ = 2 * T.card := by omega
    have hdiff := card_filter_diff_le
      (fun i : Fin n => x (false, i) ≠ x (true, M j i))
      (fun i : Fin n => base (false, i) ≠ base (true, M j i)) B (by
        intro i hiB
        have hiT : i ∉ T := fun h => hiB (Finset.mem_union_left _ h)
        have hpiT : π j i ∉ T := by
          intro h
          apply hiB
          apply Finset.mem_union_right
          rw [Finset.mem_map]
          exact ⟨π j i, h, by simp⟩
        have h1 : x (false, i) = base (false, i) := (hagree i hiT).1
        have h2 : x (true, M j i) = base (true, M j i) := by
          have h2' := (hagree (π j i) hpiT).2
          have hMpi : M target (π j i) = M j i := by simp [π]
          rwa [hMpi] at h2'
        rw [h1, h2])
    have hdist_diff : |(dist x j : Int) - (dist base j : Int)| ≤ (2 * T.card : Int) := by
      have hB_I : (B.card : Int) ≤ (2 * T.card : Int) := by exact_mod_cast hB_card
      rw [abs_le]
      exact ⟨by linarith [hdiff.2], by linarith [hdiff.1]⟩
    have hx_imb : |(2 * dist x j : Int) - (n : Int)| ≤ (Fix.card : Int) + |Y j a| + (4 * T.card : Int) := by
      have hsplit : (2 * dist x j : Int) - (n : Int) =
          ((2 * dist base j : Int) - (n : Int)) + 2 * ((dist x j : Int) - (dist base j : Int)) := by ring
      rw [hsplit]
      calc |((2 * dist base j : Int) - (n : Int)) + 2 * ((dist x j : Int) - (dist base j : Int))|
          ≤ |(2 * dist base j : Int) - (n : Int)| + |2 * ((dist x j : Int) - (dist base j : Int))| := abs_add_le _ _
        _ = |(2 * dist base j : Int) - (n : Int)| + 2 * |(dist x j : Int) - (dist base j : Int)| := by
            rw [abs_mul, abs_of_pos (by decide : (0 : Int) < 2)]
        _ ≤ ((Fix.card : Int) + |Y j a|) + 2 * (2 * T.card : Int) := by linarith
        _ = (Fix.card : Int) + |Y j a| + (4 * T.card : Int) := by ring
    have hFix_le : 128 * (Fix.card : Int) ≤ (n : Int) := by exact_mod_cast hfix j hj
    have hT_le : 128 * (T.card : Int) ≤ (n : Int) := by exact_mod_cast hTn
    have hcent_I : (16 * Nat.dist (2 * dist x j) n : Int) ≤ (n : Int) := by
      rw [nat_dist_eq_abs_int]
      push_cast
      linarith
    exact_mod_cast hcent_I
  refine ⟨hdist_target, hother, ?_⟩
  constructor
  · intro hall i hiT
    have hct : central (dist x target) := hall target
    rw [hdist_target] at hct
    dsimp only [central] at hct
    set d := (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card
    have hd0 : d = 0 := by
      by_contra hne
      have hd1 : 1 ≤ d := by omega
      have hge : n ≤ 2 * (17 * n / 32 + d) := by omega
      have hdist_val : Nat.dist (2 * (17 * n / 32 + d)) n = 2 * (17 * n / 32 + d) - n := by
        rw [Nat.dist, Nat.sub_eq_zero_of_le hge, add_zero]
      rw [hdist_val] at hct
      omega
    by_contra hne_i
    have hmem : i ∈ T.filter (fun i => x (false, i) ≠ x (true, M target i)) :=
      Finset.mem_filter.mpr ⟨hiT, hne_i⟩
    have hpos : 0 < d := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  · intro heq j
    by_cases hj : j = target
    · subst hj
      rw [hdist_target]
      have hd0 : (T.filter (fun i => x (false, i) ≠ x (true, M j i))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hiT hne
        exact hne (heq i hiT)
      rw [hd0, add_zero]
      dsimp only [central]
      have hge : n ≤ 2 * (17 * n / 32) := by omega
      have hdist_val : Nat.dist (2 * (17 * n / 32)) n = 2 * (17 * n / 32) - n := by
        rw [Nat.dist, Nat.sub_eq_zero_of_le hge, add_zero]
      rw [hdist_val]
      omega
    · exact hother j hj

private lemma exists_pass_and_singleton_fail
    (n r : ℕ) (hr2 : 2 ≤ r) (M : Fin r → Equiv.Perm (Fin n))
    (hrn : 8192 * r < n)
    (hfix : ∀ j l : Fin r, j ≠ l →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (target : Fin r) :
    let V := Bool × Fin n
    let test := fun (x : V → Bool) (j : Fin r) =>
      let D := (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card
      decide (16 * Nat.dist (2 * D) n ≤ n)
    (∃ xPass : V → Bool, ∀ j : Fin r, test xPass j = true) ∧
    (∃ xFail : V → Bool, test xFail target = false ∧ ∀ j : Fin r, j ≠ target → test xFail j = true) := by
  intro V test
  have hn_pos : 0 < n := by omega
  let i0 : Fin n := ⟨0, hn_pos⟩
  let T : Finset (Fin n) := {i0}
  have hTn : 128 * T.card ≤ n := by
    simp only [T, Finset.card_singleton]
    omega
  obtain ⟨base, hbase⟩ := singleton_restrict n r M target T hrn hTn (fun j hj => hfix j target hj)
  let xPass : V → Bool := fun v => if v = (false, i0) then base (true, M target i0) else base v
  let xFail : V → Bool := fun v => if v = (false, i0) then !(base (true, M target i0)) else base v
  have hPass_agree : ∀ i : Fin n, i ∉ T →
      xPass (false, i) = base (false, i) ∧ xPass (true, M target i) = base (true, M target i) := by
    intro i hi
    have hne : i ≠ i0 := by simpa [T] using hi
    refine ⟨?_, ?_⟩
    · exact ite_eq_right (fun h => hne (congrArg Prod.snd h))
    · exact ite_eq_right (fun h => Bool.noConfusion (congrArg Prod.fst h))
  have hFail_agree : ∀ i : Fin n, i ∉ T →
      xFail (false, i) = base (false, i) ∧ xFail (true, M target i) = base (true, M target i) := by
    intro i hi
    have hne : i ≠ i0 := by simpa [T] using hi
    refine ⟨?_, ?_⟩
    · exact ite_eq_right (fun h => hne (congrArg Prod.snd h))
    · exact ite_eq_right (fun h => Bool.noConfusion (congrArg Prod.fst h))
  constructor
  · refine ⟨xPass, fun j => ?_⟩
    have hp := (hbase xPass hPass_agree).2.2.mpr (by
      intro i hi
      have heq : i = i0 := by simpa [T] using hi
      subst heq
      have h1 : xPass (false, i0) = base (true, M target i0) := ite_eq_left rfl
      have h2 : xPass (true, M target i0) = base (true, M target i0) :=
        ite_eq_right (fun h => Bool.noConfusion (congrArg Prod.fst h))
      rw [h1, h2])
    dsimp only [test]
    exact decide_eq_true (hp j)
  · refine ⟨xFail, ?_, ?_⟩
    · have hf := hbase xFail hFail_agree
      dsimp only [test]
      rw [decide_eq_false_iff_not]
      intro hct
      have hall : ∀ j : Fin r,
          16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => xFail (false, i) ≠ xFail (true, M j i))).card) n ≤ n := by
        intro j
        by_cases hj : j = target
        · subst hj; exact hct
        · exact hf.2.1 j hj
      have heq := hf.2.2.mp hall i0 (Finset.mem_singleton_self i0)
      have h1 : xFail (false, i0) = !(base (true, M target i0)) := ite_eq_left rfl
      have h2 : xFail (true, M target i0) = base (true, M target i0) :=
        ite_eq_right (fun h => Bool.noConfusion (congrArg Prod.fst h))
      rw [h1, h2] at heq
      cases hb : base (true, M target i0) <;> rw [hb] at heq <;> exact Bool.noConfusion heq
    · intro j hj
      dsimp only [test]
      exact decide_eq_true ((hbase xFail hFail_agree).2.1 j hj)

-- ============================================================================
-- Part D: Converse direction (feasible → weights)
-- ============================================================================

private theorem backward_direction
    (n r d R u v : ℕ) (hr2 : 2 ≤ r) (_hd : 0 < d) (_hR : 0 < R) (huR : u ≤ R)
    (M : Fin r → Equiv.Perm (Fin n)) (menu : Fin d → Fin r × Fin r)
    (hrn : 8192 * r < n)
    (hfix : ∀ j l : Fin r, j ≠ l →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) :
    let V := Bool × Fin n
    let X := V → Bool
    let test := fun (x : X) (j : Fin r) =>
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      decide (16 * Nat.dist (2*D) n ≤ n)
    let cap := 4*(n+1)^2
    let feasible := ∃ (choose : Fin R → Fin d) (decode : Fin R → Bool → Bool → Bool)
      (order : Fin d → (Fin (2*n) ≃ V)) (init : Fin R → Fin cap)
      (step : Fin R → Fin (2*n) → Fin cap → Bool → Fin cap) (out : Fin R → Fin cap → Bool),
      ∀ x : X,
        let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
          (fun st k => step seed k st (x (order (choose seed) k))) (init seed))
        (∀ seed : Fin R, answer seed = decode seed (test x (menu (choose seed)).1)
          (test x (menu (choose seed)).2)) ∧
        ((∀ j : Fin r, test x j = true) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = false)).card ≤ u) ∧
        ((∃ j : Fin r, test x j = false) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = true)).card ≤ v)
    let weights := ∃ w : Fin d → ℕ, (∑ h : Fin d, w h) = R-u ∧
      ∀ j : Fin r, (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) ≤ v
    feasible → weights := by
  intro V X test cap feasible weights ⟨choose, decode, order, init, step, out, hspec⟩
  let t0 : Fin r := ⟨0, by omega⟩
  obtain ⟨⟨x0, hx0_raw⟩, _⟩ := exists_pass_and_singleton_fail n r hr2 M hrn hfix t0
  have hx0 : ∀ j : Fin r, test x0 j = true := hx0_raw
  let A : Finset (Fin R) := Finset.univ.filter (fun seed : Fin R => decode seed true true = true)
  let B : Finset (Fin R) := Finset.univ.filter (fun seed : Fin R => decode seed true true = false)
  have hB_le : B.card ≤ u := by
    have hsp0 := hspec x0
    dsimp only at hsp0
    have hfilt : B = Finset.univ.filter (fun seed : Fin R =>
        out seed ((List.finRange (2 * n)).foldl
          (fun st k => step seed k st (x0 (order (choose seed) k))) (init seed)) = false) := by
      ext seed
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hsp0.1 seed, hx0 (menu (choose seed)).1, hx0 (menu (choose seed)).2]
    rw [hfilt]
    exact hsp0.2.1 hx0
  have hAB_sum : A.card + B.card = R := by
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro seed hA hB
      have h1 := (Finset.mem_filter.mp hA).2
      have h2 := (Finset.mem_filter.mp hB).2
      rw [h1] at h2
      exact Bool.noConfusion h2
    have hunion : A ∪ B = Finset.univ := by
      ext seed
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases decode seed true true <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hRu_le : R - u ≤ A.card := by omega
  obtain ⟨A', hA'_sub, hA'_card⟩ := Finset.exists_subset_card_eq hRu_le
  let w : Fin d → ℕ := fun h => (A'.filter (fun seed : Fin R => choose seed = h)).card
  refine ⟨w, ?_, ?_⟩
  · have hfib := Finset.card_eq_sum_card_fiberwise (f := choose) (s := A') (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [← hfib, hA'_card]
  · intro j
    obtain ⟨_, ⟨xj, hxj_fail_raw, hxj_other_raw⟩⟩ := exists_pass_and_singleton_fail n r hr2 M hrn hfix j
    have hxj_fail : test xj j = false := hxj_fail_raw
    have hxj_other : ∀ l : Fin r, l ≠ j → test xj l = true := hxj_other_raw
    have hspj := hspec xj
    dsimp only at hspj
    have hpass_le : (Finset.univ.filter (fun seed : Fin R =>
        out seed ((List.finRange (2 * n)).foldl
          (fun st k => step seed k st (xj (order (choose seed) k))) (init seed)) = true)).card ≤ v :=
      hspj.2.2 ⟨j, hxj_fail⟩
    let Uncov : Finset (Fin d) := Finset.univ.filter (fun h : Fin d => ¬(j = (menu h).1 ∨ j = (menu h).2))
    have hsum_eq : (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) =
        ∑ h ∈ Uncov, w h := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2)]
      have hz : (∑ h ∈ Finset.univ.filter (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2),
          if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) = 0 :=
        Finset.sum_eq_zero fun h hh => by simp [(Finset.mem_filter.mp hh).2]
      have hnz : (∑ h ∈ Uncov, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) =
          ∑ h ∈ Uncov, w h :=
        Finset.sum_congr rfl fun h hh => by simp [(Finset.mem_filter.mp hh).2]
      change (∑ h ∈ Finset.univ.filter (fun h : Fin d => j = (menu h).1 ∨ j = (menu h).2),
          if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) +
        (∑ h ∈ Uncov, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) =
        ∑ h ∈ Uncov, w h
      rw [hz, zero_add, hnz]
    have hfib_uncov : (A'.filter (fun seed : Fin R => choose seed ∈ Uncov)).card =
        ∑ h ∈ Uncov, w h := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := choose)
        (s := A'.filter (fun seed : Fin R => choose seed ∈ Uncov)) (t := Uncov)
        (fun seed hs => (Finset.mem_filter.mp hs).2)
      rw [hfib]
      refine Finset.sum_congr rfl fun h hh => ?_
      dsimp only [w]
      congr 1
      ext seed
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hA', _⟩, rfl⟩; exact ⟨hA', rfl⟩
      · rintro ⟨hA', rfl⟩; exact ⟨⟨hA', hh⟩, rfl⟩
    have hsub : A'.filter (fun seed : Fin R => choose seed ∈ Uncov) ⊆
        Finset.univ.filter (fun seed : Fin R =>
          out seed ((List.finRange (2 * n)).foldl
            (fun st k => step seed k st (xj (order (choose seed) k))) (init seed)) = true) := by
      intro seed hs
      rcases Finset.mem_filter.mp hs with ⟨hA'm, hU⟩
      have hAm : decode seed true true = true := (Finset.mem_filter.mp (hA'_sub hA'm)).2
      have hnot : ¬(j = (menu (choose seed)).1 ∨ j = (menu (choose seed)).2) :=
        (Finset.mem_filter.mp hU).2
      have hne1 : (menu (choose seed)).1 ≠ j := fun h => hnot (Or.inl h.symm)
      have hne2 : (menu (choose seed)).2 ≠ j := fun h => hnot (Or.inr h.symm)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hspj.1 seed, hxj_other _ hne1, hxj_other _ hne2, hAm]
    calc (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h)
        = ∑ h ∈ Uncov, w h := hsum_eq
      _ = (A'.filter (fun seed : Fin R => choose seed ∈ Uncov)).card := hfib_uncov.symm
      _ ≤ (Finset.univ.filter (fun seed : Fin R =>
            out seed ((List.finRange (2 * n)).foldl
              (fun st k => step seed k st (xj (order (choose seed) k))) (init seed)) = true)).card :=
          Finset.card_le_card hsub
      _ ≤ v := hpass_le

end PEqualNP.Outside.L_pcx_339

theorem PEqualNP.Outside.L_pcx_339 :
    ∀ (n r d R u v : ℕ), 2 ≤ r → 0 < d → 0 < R → u ≤ R →
  ∀ (M : Fin r → Equiv.Perm (Fin n)) (menu : Fin d → Fin r × Fin r),
    let V := Bool × Fin n
    let X := V → Bool
    let test := fun (x : X) (j : Fin r) =>
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      decide (16 * Nat.dist (2*D) n ≤ n)
    let cap := 4*(n+1)^2
    let feasible := ∃ (choose : Fin R → Fin d) (decode : Fin R → Bool → Bool → Bool)
      (order : Fin d → (Fin (2*n) ≃ V)) (init : Fin R → Fin cap)
      (step : Fin R → Fin (2*n) → Fin cap → Bool → Fin cap) (out : Fin R → Fin cap → Bool),
      ∀ x : X,
        let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
          (fun st k => step seed k st (x (order (choose seed) k))) (init seed))
        (∀ seed : Fin R, answer seed = decode seed (test x (menu (choose seed)).1)
          (test x (menu (choose seed)).2)) ∧
        ((∀ j : Fin r, test x j = true) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = false)).card ≤ u) ∧
        ((∃ j : Fin r, test x j = false) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = true)).card ≤ v)
    let weights := ∃ w : Fin d → ℕ, (∑ h : Fin d, w h) = R-u ∧
      ∀ j : Fin r, (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) ≤ v
    (weights → feasible) ∧ (8192*r < n →
      (∀ j l : Fin r, j ≠ l →
        128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
      feasible → weights) := by
  intro n r d R u v hr2 hd hR huR M menu
  exact ⟨PEqualNP.Outside.L_pcx_339.forward_direction n r d R u v hr2 hd hR huR M menu,
    fun hrn hfix => PEqualNP.Outside.L_pcx_339.backward_direction n r d R u v hr2 hd hR huR M menu hrn hfix⟩

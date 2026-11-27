import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_338_aux

abbrev RawType (n : ℕ) (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

def blockParity {m : ℕ} (f : Fin m → Bool) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin m)).filter (fun j => f j = true)).card)

def parity {n : ℕ} {w : Fin n → ℕ} (y : RawType n w → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

def liftAx {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (A : PEqualNP.ProofComplexity.Clause (RawType n w)) : Prop :=
  ∃ C ∈ F, ∃ y : RawType n w → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (RawType n w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
      (fun b => (b, !(y b)))

def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def trace {V : Type} (ask : List Bool → V) (p : List Bool) : List V :=
  List.ofFn (fun j : Fin p.length => ask (p.take j.val))

lemma blockParity_update_not {m : ℕ} (f : Fin m → Bool) (j : Fin m) :
    blockParity (Function.update f j true) = !(blockParity (Function.update f j false)) := by
  unfold blockParity
  let s0 := (Finset.univ : Finset (Fin m)).filter (fun t => Function.update f j false t = true)
  let s1 := (Finset.univ : Finset (Fin m)).filter (fun t => Function.update f j true t = true)
  have hj0 : j ∉ s0 := by
    simp [s0]
  have hs1 : s1 = insert j s0 := by
    ext t
    simp only [s1, s0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : t = j
    · subst h; simp
    · simp [h]
  have hcard : s1.card = s0.card + 1 := by
    rw [hs1, Finset.card_insert_of_notMem hj0]
  change decide (Odd s1.card) = !decide (Odd s0.card)
  rw [hcard]
  by_cases ho : Odd s0.card
  · have hno : ¬ Odd (s0.card + 1) := by
      rcases ho with ⟨k, hk⟩
      intro ⟨l, hl⟩
      omega
    simp [ho, hno]
  · have ho1 : Odd (s0.card + 1) := by
      rw [Nat.not_odd_iff_even] at ho
      rcases ho with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    simp [ho, ho1]

lemma blockParity_prefix_xor {m : ℕ} (f : Fin m → Bool) :
    ∀ (k : ℕ) (hk : k ≤ m),
      decide (Odd ((Finset.univ : Finset (Fin m)).filter (fun j => j.val < k ∧ f j = true)).card) =
        (List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩)).foldl xor false := by
  intro k hk
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have ih' := ih (by omega)
    let s0 := (Finset.univ : Finset (Fin m)).filter (fun j => j.val < k ∧ f j = true)
    let s1 := (Finset.univ : Finset (Fin m)).filter (fun j => j.val < k + 1 ∧ f j = true)
    have hfold :
        (List.ofFn (fun j : Fin (k + 1) => f ⟨j.val, by omega⟩)).foldl xor false =
          xor ((List.ofFn (fun j : Fin k => f ⟨j.val, by omega⟩)).foldl xor false)
            (f ⟨k, by omega⟩) := by
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
      rfl
    rw [hfold, ← ih']
    change decide (Odd s1.card) = xor (decide (Odd s0.card)) (f ⟨k, by omega⟩)
    cases hfk : f ⟨k, by omega⟩
    · have heq : s1 = s0 := by
        ext j
        simp only [s1, s0, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          by_contra hge
          have hjk : j = ⟨k, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hjk, hfk] at h2
          exact Bool.noConfusion h2
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      rw [heq]
      simp
    · have hj0 : (⟨k, by omega⟩ : Fin m) ∉ s0 := by
        simp only [s0, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        exact Nat.lt_irrefl k h.1
      have hs1 : s1 = insert ⟨k, by omega⟩ s0 := by
        ext j
        simp only [s1, s0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hjk : j.val = k
          · left; exact Fin.ext hjk
          · right; exact ⟨by omega, h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨by dsimp only; omega, hfk⟩
          · exact ⟨by omega, h2⟩
      have hcard : s1.card = s0.card + 1 := by
        rw [hs1, Finset.card_insert_of_notMem hj0]
      rw [hcard]
      by_cases ho : Odd s0.card
      · have hno : ¬ Odd (s0.card + 1) := by rcases ho with ⟨t, ht⟩; intro ⟨u, hu⟩; omega
        simp [ho, hno]
      · have ho1 : Odd (s0.card + 1) := by
          rw [Nat.not_odd_iff_even] at ho; rcases ho with ⟨t, ht⟩; exact ⟨t, by omega⟩
        simp [ho, ho1]

lemma shape_leaf : shape {[]} ∅ := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro p b h
    simp only [Finset.mem_singleton] at h
    have := congrArg List.length h
    simp at this
  · intro p hp
    exact absurd hp (Finset.notMem_empty _)

lemma shape_combine {N0 J0 N1 J1 : Finset (List Bool)}
    (h0 : shape N0 J0) (h1 : shape N1 J1) :
    shape (insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)))
      (insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·))) := by
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left; rfl
    · right; left; exact ⟨q, h0.2.1 hq, rfl⟩
    · right; right; exact ⟨q, h1.2.1 hq, rfl⟩
  · intro p b hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with hnil | ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
    · have := congrArg List.length hnil; simp at this
    · cases p with
      | nil => left; rfl
      | cons d rest =>
        simp only [List.cons_append, List.cons.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        right; left; exact ⟨rest, h0.2.2.1 rest b hq, rfl⟩
    · cases p with
      | nil => left; rfl
      | cons d rest =>
        simp only [List.cons_append, List.cons.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        right; right; exact ⟨rest, h1.2.2.1 rest b hq, rfl⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · constructor
      · right; left; exact ⟨[], h0.1, rfl⟩
      · right; right; exact ⟨[], h1.1, rfl⟩
    · constructor
      · right; left; exact ⟨q ++ [false], (h0.2.2.2 q hq).1, rfl⟩
      · right; left; exact ⟨q ++ [true], (h0.2.2.2 q hq).2, rfl⟩
    · constructor
      · right; right; exact ⟨q ++ [false], (h1.2.2.2 q hq).1, rfl⟩
      · right; right; exact ⟨q ++ [true], (h1.2.2.2 q hq).2, rfl⟩

lemma sdiff_combine (N0 J0 N1 J1 : Finset (List Bool)) :
    insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·)) \
      insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·)) =
    (N0 \ J0).image (false :: ·) ∪ (N1 \ J1).image (true :: ·) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩, hnot⟩
    · exact absurd (Or.inl rfl) hnot
    · left; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inl ⟨q, hqJ, rfl⟩))⟩, rfl⟩
    · right; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inr ⟨q, hqJ, rfl⟩))⟩, rfl⟩
  · rintro (⟨q, ⟨hqN, hqJ⟩, rfl⟩ | ⟨q, ⟨hqN, hqJ⟩, rfl⟩)
    · refine ⟨Or.inr (Or.inl ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', hq', hEq⟩ | ⟨q', _, hEq⟩)
      · cases h
      · exact hqJ ((List.cons.inj hEq).2 ▸ hq')
      · exact Bool.noConfusion (List.cons.inj hEq).1
    · refine ⟨Or.inr (Or.inr ⟨q, hqN, rfl⟩), ?_⟩
      rintro (h | ⟨q', _, hEq⟩ | ⟨q', hq', hEq⟩)
      · cases h
      · exact Bool.noConfusion (List.cons.inj hEq).1
      · exact hqJ ((List.cons.inj hEq).2 ▸ hq')

lemma disjoint_cons_images (S0 S1 : Finset (List Bool)) :
    Disjoint (S0.image (false :: ·)) (S1.image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro p h0 h1
  obtain ⟨q0, _, rfl⟩ := Finset.mem_image.mp h0
  obtain ⟨q1, _, hEq⟩ := Finset.mem_image.mp h1
  exact Bool.noConfusion (List.cons.inj hEq).1

lemma trace_cons {V : Type} (i : V) (ql qr : List Bool → V) (b : Bool) (p : List Bool) :
    trace (fun l => match l with | [] => i | false :: t => ql t | true :: t => qr t) (b :: p) =
      i :: trace (if b then qr else ql) p := by
  apply List.ext_getElem
  · simp [trace]
  · intro idx h1 h2
    cases idx with
    | zero =>
      simp [trace]
    | succ idx =>
      cases b <;> simp [trace]

inductive RTree (Raw : Type) where
  | leaf
  | node (v : Raw) (l r : RTree Raw)

def rheight {Raw : Type} : RTree Raw → ℕ
  | .leaf => 0
  | .node _ l r => 1 + max (rheight l) (rheight r)

def rleaves {Raw : Type} : RTree Raw → ℕ
  | .leaf => 1
  | .node _ l r => rleaves l + rleaves r

def Falsifies {V : Type} (ρ : V → Option Bool) (C : PEqualNP.ProofComplexity.Clause V) : Prop :=
  ∀ lit ∈ C, ρ lit.1 = some (!lit.2)

def RSound {n : ℕ} {w : Fin n → ℕ} (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (ρ : RawType n w → Option Bool) : RTree (RawType n w) → Prop
  | .leaf => ∃ A, liftAx F A ∧ Falsifies ρ A
  | .node v l r =>
      RSound F (Function.update ρ v (some false)) l ∧
      RSound F (Function.update ρ v (some true)) r


def joinRank (a b : ℕ) := if a=b then a+1 else max a b
lemma jr_mono {a b c d : ℕ} (ac : a≤c) (bd : b≤d) : joinRank a b ≤ joinRank c d := by
  unfold joinRank; split_ifs <;> omega
lemma jr_flip (a b : ℕ) : joinRank a b=joinRank b a := by unfold joinRank; split_ifs <;> omega
lemma jr_shift (a b k : ℕ) : joinRank (a+k) (b+k)=joinRank a b+k := by unfold joinRank; split_ifs <;> omega
def rr {V : Type} : RTree V → ℕ
  | .leaf => 0
  | .node _ l r => joinRank (rr l) (rr r)
def RankLaw (N J : Finset (List Bool)) (fee r : List Bool→ℕ) :=
  (∀ p∈N\J,r p=0) ∧ ∀ p∈J,r p=fee p+joinRank (r (p++[false])) (r (p++[true]))
def Budget (N J : Finset (List Bool)) (fee : List Bool→ℕ) (k : ℕ) :=
  ∃ r, RankLaw N J fee r ∧ r [] ≤ k
lemma budgetLeaf (fee : List Bool→ℕ) (k : ℕ) : Budget {[]} ∅ fee k :=
  ⟨fun _=>0,⟨fun _ _=>rfl,by simp⟩,Nat.zero_le _⟩
lemma budget_mono {N J f k l} (h : Budget N J f k) (e : k≤l) : Budget N J f l := by
  obtain ⟨r,law,ok⟩ := h
  exact ⟨r,law,ok.trans e⟩
def fork {α : Type} (root : α) (l r : List Bool→α) : List Bool→α
  | [] => root
  | false::p => l p
  | true::p => r p
lemma budget_merge {N0 J0 N1 J1 : Finset (List Bool)} (f : List Bool→ℕ) {k l : ℕ}
    (hl : Budget N0 J0 (fun p=>f (false::p)) k) (hr : Budget N1 J1 (fun p=>f (true::p)) l) :
    Budget (insert [] (N0.image (false::·) ∪ N1.image (true::·)))
      (insert [] (J0.image (false::·) ∪ J1.image (true::·))) f (f []+joinRank k l) := by
  classical
  obtain ⟨L,hL,bL⟩ := hl; obtain ⟨R,hR,bR⟩ := hr
  refine ⟨fork (f []+joinRank (L []) (R [])) L R,⟨?_,?_⟩,Nat.add_le_add_left (jr_mono bL bR) _⟩
  · intro p hp
    rw [sdiff_combine] at hp
    rcases Finset.mem_union.mp hp with h|h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h; exact hL.1 a ha
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h; exact hR.1 a ha
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hp
    rcases hp with rfl|⟨p,h,rfl⟩|⟨p,h,rfl⟩
    · rfl
    · exact hL.2 p h
    · exact hR.2 p h

lemma extract_rtree_aux {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (RawType n w))
    (H : ℕ)
    (rank : List Bool→ℕ) (law : RankLaw N J (fun _=>0) rank)
    (hshape : shape N J) (hlen : ∀ p ∈ N, p.length ≤ H)
    (hax : ∀ p ∈ N \ J, liftAx F (line p))
    (hres : ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
      (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ (d : ℕ) (p : List Bool), p ∈ N → H - p.length ≤ d →
      ∀ ρ : RawType n w → Option Bool, Falsifies ρ (line p) →
        ∃ T : RTree (RawType n w),
          RSound F ρ T ∧
          rheight T ≤ H - p.length ∧
          rr T ≤ rank p := by
  intro d
  induction d with
  | zero =>
    intro p hp hle ρ hfals
    have hnotJ : p ∉ J := by
      intro hpJ
      have hc := (hshape.2.2.2 p hpJ).1
      have hlc := hlen (p ++ [false]) hc
      simp at hlc
      omega
    have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hnotJ⟩
    refine ⟨RTree.leaf, ⟨line p, hax p hleaf, hfals⟩, Nat.zero_le _, ?_⟩
    exact Nat.zero_le _
  | succ d ih =>
    intro p hp hle ρ hfals
    by_cases hpJ : p ∈ J
    · have hp0 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
      have hp1 : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
      have hres_p := hres p hpJ
      obtain ⟨v, hv0, hv1, hreq⟩ := hres_p
      have hlen0 : H - (p ++ [false]).length ≤ d := by
        have := hlen (p ++ [false]) hp0; simp at this ⊢; omega
      have hlen1 : H - (p ++ [true]).length ≤ d := by
        have := hlen (p ++ [true]) hp1; simp at this ⊢; omega
      by_cases hρv_some : ρ v = some false
      · have hf0 : Falsifies ρ (line (p ++ [false])) := by
          intro lit hlit
          by_cases hlv : lit.1 = v
          · by_cases hlb : lit.2 = true
            · rw [hlv, hlb, hρv_some]; rfl
            · have hne_vt : lit ≠ (v, true) := fun h => hlb (congrArg Prod.snd h)
              have hmemR : lit ∈ line p := by
                rw [hreq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_vt, hlit⟩)
              exact hfals lit hmemR
          · have hne_vt : lit ≠ (v, true) := fun h => hlv (congrArg Prod.fst h)
            have hmemR : lit ∈ line p := by
              rw [hreq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_vt, hlit⟩)
            exact hfals lit hmemR
        obtain ⟨T0, hS0, hH0, hL0⟩ := ih (p ++ [false]) hp0 hlen0 ρ hf0
        refine ⟨T0, hS0, ?_, ?_⟩
        · simp at hH0; omega
        · have er := law.2 p hpJ
          dsimp only [joinRank] at er; split_ifs at er <;> omega
      · by_cases hρv_true : ρ v = some true
        · have hf1 : Falsifies ρ (line (p ++ [true])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = false
              · rw [hlv, hlb, hρv_true]; rfl
              · have hne_vf : lit ≠ (v, false) := fun h => hlb (congrArg Prod.snd h)
                have hmemR : lit ∈ line p := by
                  rw [hreq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_vf, hlit⟩)
                exact hfals lit hmemR
            · have hne_vf : lit ≠ (v, false) := fun h => hlv (congrArg Prod.fst h)
              have hmemR : lit ∈ line p := by
                rw [hreq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_vf, hlit⟩)
              exact hfals lit hmemR
          obtain ⟨T1, hS1, hH1, hL1⟩ := ih (p ++ [true]) hp1 hlen1 ρ hf1
          refine ⟨T1, hS1, ?_, ?_⟩
          · simp at hH1; omega
          · have er := law.2 p hpJ
            dsimp only [joinRank] at er; split_ifs at er <;> omega
        · have hρv_none : ρ v = none := by
            cases h : ρ v with
            | none => rfl
            | some b => cases b <;> simp_all
          have hf0 : Falsifies (Function.update ρ v (some false)) (line (p ++ [false])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = true
              · rw [hlv, hlb]; simp
              · have hne_vt : lit ≠ (v, true) := fun h => hlb (congrArg Prod.snd h)
                have hmemR : lit ∈ line p := by
                  rw [hreq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_vt, hlit⟩)
                have hcontra := hfals lit hmemR
                rw [hlv, hρv_none] at hcontra
                cases hcontra
            · have hne_vt : lit ≠ (v, true) := fun h => hlv (congrArg Prod.fst h)
              have hmemR : lit ∈ line p := by
                rw [hreq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne_vt, hlit⟩)
              rw [Function.update_of_ne hlv]
              exact hfals lit hmemR
          have hf1 : Falsifies (Function.update ρ v (some true)) (line (p ++ [true])) := by
            intro lit hlit
            by_cases hlv : lit.1 = v
            · by_cases hlb : lit.2 = false
              · rw [hlv, hlb]; simp
              · have hne_vf : lit ≠ (v, false) := fun h => hlb (congrArg Prod.snd h)
                have hmemR : lit ∈ line p := by
                  rw [hreq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_vf, hlit⟩)
                have hcontra := hfals lit hmemR
                rw [hlv, hρv_none] at hcontra
                cases hcontra
            · have hne_vf : lit ≠ (v, false) := fun h => hlv (congrArg Prod.fst h)
              have hmemR : lit ∈ line p := by
                rw [hreq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne_vf, hlit⟩)
              rw [Function.update_of_ne hlv]
              exact hfals lit hmemR
          obtain ⟨T0, hS0, hH0, hL0⟩ := ih (p ++ [false]) hp0 hlen0 _ hf0
          obtain ⟨T1, hS1, hH1, hL1⟩ := ih (p ++ [true]) hp1 hlen1 _ hf1
          refine ⟨RTree.node v T0 T1, ⟨hS0, hS1⟩, ?_, ?_⟩
          · dsimp only [rheight]
            have hlp0 := hlen (p ++ [false]) hp0
            simp at hH0 hH1 hlp0
            omega
          · simpa only [rr,law.2 p hpJ,Nat.zero_add] using jr_mono hL0 hL1
    · have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      refine ⟨RTree.leaf, ⟨line p, hax p hleaf, hfals⟩, Nat.zero_le _, ?_⟩
      exact Nat.zero_le _

def rem {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin (w i))).filter (fun j => ρ ⟨i, j⟩ = none)).card

def partialBits {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool) : ℕ :=
  ∑ i : Fin n, if 0 < rem ρ i then w i - rem ρ i else 0

def blockVal {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool) (i : Fin n) : Bool :=
  parity (fun b => (ρ b).getD false) i

lemma rem_le_w {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool) (i : Fin n) :
    rem ρ i ≤ w i := by
  simpa [rem] using Finset.card_le_univ ((Finset.univ : Finset (Fin (w i))).filter (fun j => ρ ⟨i, j⟩ = none))

lemma rem_update_other {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) (val : Bool) (i : Fin n) (hi : i ≠ v.1) :
    rem (Function.update ρ v (some val)) i = rem ρ i := by
  unfold rem
  congr 1
  ext j
  have hne : (⟨i, j⟩ : RawType n w) ≠ v := fun h => hi (congrArg Sigma.fst h)
  simp [Function.update_of_ne hne]

lemma rem_update_self {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) (hnone : ρ v = none) (val : Bool) :
    rem (Function.update ρ v (some val)) v.1 + 1 = rem ρ v.1 := by
  unfold rem
  let s0 := (Finset.univ : Finset (Fin (w v.1))).filter (fun j => Function.update ρ v (some val) ⟨v.1, j⟩ = none)
  let s1 := (Finset.univ : Finset (Fin (w v.1))).filter (fun j => ρ ⟨v.1, j⟩ = none)
  have hnot : v.2 ∉ s0 := by
    simp [s0]
  have heq : s1 = insert v.2 s0 := by
    ext j
    simp only [s1, s0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : j = v.2
    · subst h
      have hv_eq : (⟨v.1, v.2⟩ : RawType n w) = v := rfl
      simp [hv_eq, hnone]
    · have hne : (⟨v.1, j⟩ : RawType n w) ≠ v := by
        intro heq
        apply h
        cases v
        exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      simp [h, Function.update_of_ne hne]
  change s0.card + 1 = s1.card
  rw [heq, Finset.card_insert_of_notMem hnot]

lemma partialBits_update_ge2 {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) (hnone : ρ v = none) (hge : 2 ≤ rem ρ v.1) (val : Bool) :
    partialBits (Function.update ρ v (some val)) = partialBits ρ + 1 := by
  unfold partialBits
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v.1),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v.1)]
  have hrest :
      ∑ i ∈ Finset.univ.erase v.1,
        (if 0 < rem (Function.update ρ v (some val)) i then w i - rem (Function.update ρ v (some val)) i else 0) =
      ∑ i ∈ Finset.univ.erase v.1,
        (if 0 < rem ρ i then w i - rem ρ i else 0) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [rem_update_other ρ v val i (Finset.mem_erase.mp hi).1]
  rw [hrest]
  have hrem := rem_update_self ρ v hnone val
  have hle := rem_le_w ρ v.1
  have hpos1 : 0 < rem (Function.update ρ v (some val)) v.1 := by omega
  have hpos2 : 0 < rem ρ v.1 := by omega
  simp only [hpos1, hpos2, ↓reduceIte]
  omega

lemma partialBits_update_eq1 {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) (hnone : ρ v = none) (heq1 : rem ρ v.1 = 1) (val : Bool) :
    partialBits ρ = partialBits (Function.update ρ v (some val)) + (w v.1 - 1) := by
  unfold partialBits
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v.1),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v.1)]
  have hrest :
      ∑ i ∈ Finset.univ.erase v.1,
        (if 0 < rem (Function.update ρ v (some val)) i then w i - rem (Function.update ρ v (some val)) i else 0) =
      ∑ i ∈ Finset.univ.erase v.1,
        (if 0 < rem ρ i then w i - rem ρ i else 0) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [rem_update_other ρ v val i (Finset.mem_erase.mp hi).1]
  rw [hrest]
  have hrem := rem_update_self ρ v hnone val
  have h0 : rem (Function.update ρ v (some val)) v.1 = 0 := by omega
  simp only [h0, heq1, Nat.lt_irrefl, Nat.zero_lt_one, ↓reduceIte, zero_add]
  omega

lemma blockVal_update_other {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) (val : Bool) (i : Fin n) (hi : i ≠ v.1) :
    blockVal (Function.update ρ v (some val)) i = blockVal ρ i := by
  unfold blockVal parity
  congr 3
  ext j
  have hne : (⟨i, j⟩ : RawType n w) ≠ v := fun h => hi (congrArg Sigma.fst h)
  simp [Function.update_of_ne hne]

lemma blockVal_update_flip {n : ℕ} {w : Fin n → ℕ} (ρ : RawType n w → Option Bool)
    (v : RawType n w) :
    blockVal (Function.update ρ v (some true)) v.1 =
      !(blockVal (Function.update ρ v (some false)) v.1) := by
  let f : Fin (w v.1) → Bool := fun j => (ρ ⟨v.1, j⟩).getD false
  have hT : blockVal (Function.update ρ v (some true)) v.1 = blockParity (Function.update f v.2 true) := by
    unfold blockVal parity blockParity
    congr 3
    ext j
    by_cases h : j = v.2
    · subst h
      have hv_eq : (⟨v.1, v.2⟩ : RawType n w) = v := rfl
      simp [hv_eq]
    · have hne : (⟨v.1, j⟩ : RawType n w) ≠ v := by
        intro heq; apply h; cases v; exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      simp [f, h, Function.update_of_ne hne]
  have hF : blockVal (Function.update ρ v (some false)) v.1 = blockParity (Function.update f v.2 false) := by
    unfold blockVal parity blockParity
    congr 3
    ext j
    by_cases h : j = v.2
    · subst h
      have hv_eq : (⟨v.1, v.2⟩ : RawType n w) = v := rfl
      simp [hv_eq]
    · have hne : (⟨v.1, j⟩ : RawType n w) ≠ v := by
        intro heq; apply h; cases v; exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      simp [f, h, Function.update_of_ne hne]
  rw [hT, hF]
  exact blockParity_update_not f v.2

lemma extract_outer {n : ℕ} (hn : 0 < n) {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    ∀ (T : RTree (RawType n w)) (ρ : RawType n w → Option Bool),
      RSound F ρ T →
      ∃ (M A : Finset (List Bool)) (q : List Bool → Fin n),
        shape M A ∧
        (∀ p ∈ M, (trace q p).Nodup ∧ (∀ i ∈ trace q p, 0 < rem ρ i) ∧
          ((trace q p).map w).sum ≤ rheight T + partialBits ρ) ∧
        (∀ p ∈ M \ A, ∃ C ∈ F, ∀ lit ∈ C,
          (rem ρ lit.1 = 0 ∧ blockVal ρ lit.1 ≠ lit.2) ∨
          (∃ j : Fin p.length, q (p.take j.val) = lit.1 ∧ p.get j ≠ lit.2)) ∧
        Budget M A (fun p=>w (q p)-1) (rr T+partialBits ρ) := by
  intro T
  induction T with
  | leaf =>
    intro ρ ⟨Cl, hax, hfals⟩
    obtain ⟨C, hCF, y, hyC, hCl_eq⟩ := hax
    refine ⟨{[]}, ∅, fun _ => ⟨0, hn⟩, shape_leaf, ?_, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton.mp hp]
      simp [trace]
    · intro p hp
      have hp' : p = [] := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hp).1
      subst hp'
      refine ⟨C, hCF, fun lit hlit => Or.inl ⟨?_, ?_⟩⟩
      · have hvars : lit.1 ∈ C.image Prod.fst := Finset.mem_image.mpr ⟨lit, hlit, rfl⟩
        have hall_some : ∀ j : Fin (w lit.1), ρ ⟨lit.1, j⟩ = some (y ⟨lit.1, j⟩) := by
          intro j
          have hmemA : (⟨lit.1, j⟩, !(y ⟨lit.1, j⟩)) ∈ Cl := by
            rw [hCl_eq]
            exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvars⟩, rfl⟩
          have hf := hfals _ hmemA
          simpa using hf
        have hrem0 : rem ρ lit.1 = 0 := by
          unfold rem
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _
          rw [hall_some j]
          exact Option.some_ne_none _
        exact hrem0
      · have hvars : lit.1 ∈ C.image Prod.fst := Finset.mem_image.mpr ⟨lit, hlit, rfl⟩
        have hall_some : ∀ j : Fin (w lit.1), ρ ⟨lit.1, j⟩ = some (y ⟨lit.1, j⟩) := by
          intro j
          have hmemA : (⟨lit.1, j⟩, !(y ⟨lit.1, j⟩)) ∈ Cl := by
            rw [hCl_eq]
            exact Finset.mem_image.mpr ⟨⟨lit.1, j⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvars⟩, rfl⟩
          have hf := hfals _ hmemA
          simpa using hf
        have hbv : blockVal ρ lit.1 = parity y lit.1 := by
          unfold blockVal parity
          congr 3
          ext j
          simp [hall_some j]
        rw [hbv]
        exact hyC lit hlit
    · exact budgetLeaf _ _
  | node v l r ihl ihr =>
    intro ρ ⟨hSl, hSr⟩
    by_cases hnone : ρ v = none
    · have hrem_pos : 1 ≤ rem ρ v.1 := by
        unfold rem
        exact Finset.card_pos.mpr ⟨v.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
      by_cases hge2 : 2 ≤ rem ρ v.1
      · by_cases hcmp : rr l ≤ rr r
        · obtain ⟨M, A, q, hsh, hM, hleaf, hsum⟩ := ihl (Function.update ρ v (some false)) hSl
          have hpb := partialBits_update_ge2 ρ v hnone hge2 false
          refine ⟨M, A, q, hsh, ?_, ?_, ?_⟩
          · intro p hp
            obtain ⟨hnod, hrem_p, hht⟩ := hM p hp
            refine ⟨hnod, fun i hi => ?_, ?_⟩
            · have hi' := hrem_p i hi
              by_cases hiv : i = v.1
              · rw [hiv]; omega
              · rwa [rem_update_other ρ v false i hiv] at hi'
            · dsimp only [rheight]
              rw [hpb] at hht
              omega
          · intro p hp
            obtain ⟨C, hCF, hC⟩ := hleaf p hp
            refine ⟨C, hCF, fun lit hlit => ?_⟩
            rcases hC lit hlit with ⟨hrem0, hbv⟩ | hex
            · have hne : lit.1 ≠ v.1 := by
                intro heq
                have := rem_update_self ρ v hnone false
                rw [heq] at hrem0
                omega
              left
              rw [rem_update_other ρ v false lit.1 hne] at hrem0
              rw [blockVal_update_other ρ v false lit.1 hne] at hbv
              exact ⟨hrem0, hbv⟩
            · exact Or.inr hex
          · apply budget_mono hsum
            rw [hpb]; dsimp only [rr,joinRank]; split_ifs <;> omega
        · obtain ⟨M, A, q, hsh, hM, hleaf, hsum⟩ := ihr (Function.update ρ v (some true)) hSr
          have hpb := partialBits_update_ge2 ρ v hnone hge2 true
          refine ⟨M, A, q, hsh, ?_, ?_, ?_⟩
          · intro p hp
            obtain ⟨hnod, hrem_p, hht⟩ := hM p hp
            refine ⟨hnod, fun i hi => ?_, ?_⟩
            · have hi' := hrem_p i hi
              by_cases hiv : i = v.1
              · rw [hiv]; omega
              · rwa [rem_update_other ρ v true i hiv] at hi'
            · dsimp only [rheight]
              rw [hpb] at hht
              omega
          · intro p hp
            obtain ⟨C, hCF, hC⟩ := hleaf p hp
            refine ⟨C, hCF, fun lit hlit => ?_⟩
            rcases hC lit hlit with ⟨hrem0, hbv⟩ | hex
            · have hne : lit.1 ≠ v.1 := by
                intro heq
                have := rem_update_self ρ v hnone true
                rw [heq] at hrem0
                omega
              left
              rw [rem_update_other ρ v true lit.1 hne] at hrem0
              rw [blockVal_update_other ρ v true lit.1 hne] at hbv
              exact ⟨hrem0, hbv⟩
            · exact Or.inr hex
          · apply budget_mono hsum
            rw [hpb]; dsimp only [rr,joinRank]; split_ifs <;> omega
      · have heq1 : rem ρ v.1 = 1 := by omega
        obtain ⟨Ml, Al, ql, hshl, hMl, hleafl, hsuml⟩ := ihl (Function.update ρ v (some false)) hSl
        obtain ⟨Mr, Ar, qr, hshr, hMr, hleafr, hsumr⟩ := ihr (Function.update ρ v (some true)) hSr
        have hpb_l := partialBits_update_eq1 ρ v hnone heq1 false
        have hpb_r := partialBits_update_eq1 ρ v hnone heq1 true
        have hflip := blockVal_update_flip ρ v
        have hrem_l0 : rem (Function.update ρ v (some false)) v.1 = 0 := by
          have := rem_update_self ρ v hnone false; omega
        have hrem_r0 : rem (Function.update ρ v (some true)) v.1 = 0 := by
          have := rem_update_self ρ v hnone true; omega
        let bF := blockVal (Function.update ρ v (some false)) v.1
        let M0 := if bF = false then Ml else Mr
        let A0 := if bF = false then Al else Ar
        let q0 := if bF = false then ql else qr
        let M1 := if bF = false then Mr else Ml
        let A1 := if bF = false then Ar else Al
        let q1 := if bF = false then qr else ql
        let ρ0 := Function.update ρ v (some (if bF = false then false else true))
        let ρ1 := Function.update ρ v (some (if bF = false then true else false))
        have hbv0 : blockVal ρ0 v.1 = false := by
          dsimp only [ρ0]
          split_ifs with h
          · exact h
          · have ht : bF = true := Bool.eq_true_of_not_eq_false h
            rw [hflip]
            change (!bF) = false
            rw [ht]; rfl
        have hbv1 : blockVal ρ1 v.1 = true := by
          dsimp only [ρ1]
          split_ifs with h
          · rw [hflip]
            change (!bF) = true
            rw [h]; rfl
          · exact Bool.eq_true_of_not_eq_false h
        have hsh0 : shape M0 A0 := by dsimp only [M0, A0]; split_ifs <;> assumption
        have hsh1 : shape M1 A1 := by dsimp only [M1, A1]; split_ifs <;> assumption
        have hpb0 : partialBits ρ = partialBits ρ0 + (w v.1 - 1) := by
          dsimp only [ρ0]; split_ifs <;> assumption
        have hpb1 : partialBits ρ = partialBits ρ1 + (w v.1 - 1) := by
          dsimp only [ρ1]; split_ifs <;> assumption
        have hM0 : ∀ p ∈ M0, (trace q0 p).Nodup ∧ (∀ i ∈ trace q0 p, 0 < rem ρ0 i) ∧
            ((trace q0 p).map w).sum ≤ max (rheight l) (rheight r) + partialBits ρ0 := by
          dsimp only [M0, q0, ρ0]
          split_ifs
          · intro p hp; obtain ⟨h1, h2, h3⟩ := hMl p hp; exact ⟨h1, h2, by omega⟩
          · intro p hp; obtain ⟨h1, h2, h3⟩ := hMr p hp; exact ⟨h1, h2, by omega⟩
        have hM1 : ∀ p ∈ M1, (trace q1 p).Nodup ∧ (∀ i ∈ trace q1 p, 0 < rem ρ1 i) ∧
            ((trace q1 p).map w).sum ≤ max (rheight l) (rheight r) + partialBits ρ1 := by
          dsimp only [M1, q1, ρ1]
          split_ifs
          · intro p hp; obtain ⟨h1, h2, h3⟩ := hMr p hp; exact ⟨h1, h2, by omega⟩
          · intro p hp; obtain ⟨h1, h2, h3⟩ := hMl p hp; exact ⟨h1, h2, by omega⟩
        have hleaf0 : ∀ p ∈ M0 \ A0, ∃ C ∈ F, ∀ lit ∈ C,
            (rem ρ0 lit.1 = 0 ∧ blockVal ρ0 lit.1 ≠ lit.2) ∨
            (∃ j : Fin p.length, q0 (p.take j.val) = lit.1 ∧ p.get j ≠ lit.2) := by
          dsimp only [M0, A0, q0, ρ0]; split_ifs <;> assumption
        have hleaf1 : ∀ p ∈ M1 \ A1, ∃ C ∈ F, ∀ lit ∈ C,
            (rem ρ1 lit.1 = 0 ∧ blockVal ρ1 lit.1 ≠ lit.2) ∨
            (∃ j : Fin p.length, q1 (p.take j.val) = lit.1 ∧ p.get j ≠ lit.2) := by
          dsimp only [M1, A1, q1, ρ1]; split_ifs <;> assumption
        let M := insert [] (M0.image (false :: ·) ∪ M1.image (true :: ·))
        let A := insert [] (A0.image (false :: ·) ∪ A1.image (true :: ·))
        let q : List Bool → Fin n := fun p =>
          match p with
          | [] => v.1
          | false :: t => q0 t
          | true :: t => q1 t
        refine ⟨M, A, q, shape_combine hsh0 hsh1, ?_, ?_, ?_⟩
        · intro p hp
          simp only [M, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with rfl | ⟨p0, hp0, rfl⟩ | ⟨p1, hp1, rfl⟩
          · simp [trace]
          · have htr : trace q (false :: p0) = v.1 :: trace q0 p0 := by
              simpa [q] using trace_cons v.1 q0 q1 false p0
            obtain ⟨hnod0, hrem0, hht0⟩ := hM0 p0 hp0
            have hrem_ρ0_v : rem ρ0 v.1 = 0 := by dsimp only [ρ0]; split_ifs <;> assumption
            have hv_not_mem : v.1 ∉ trace q0 p0 := fun hm => by
              have := hrem0 v.1 hm; omega
            rw [htr]
            refine ⟨List.nodup_cons.mpr ⟨hv_not_mem, hnod0⟩, ?_, ?_⟩
            · intro i hi
              simp only [List.mem_cons] at hi
              rcases hi with rfl | hi
              · omega
              · have hi' := hrem0 i hi
                have hne : i ≠ v.1 := fun h => by rw [h] at hi'; omega
                dsimp only [ρ0] at hi'
                split_ifs at hi' <;> rwa [rem_update_other ρ v _ i hne] at hi'
            · simp only [List.map_cons, List.sum_cons, rheight]
              have hwv := hw v.1
              omega
          · have htr : trace q (true :: p1) = v.1 :: trace q1 p1 := by
              simpa [q] using trace_cons v.1 q0 q1 true p1
            obtain ⟨hnod1, hrem1, hht1⟩ := hM1 p1 hp1
            have hrem_ρ1_v : rem ρ1 v.1 = 0 := by dsimp only [ρ1]; split_ifs <;> assumption
            have hv_not_mem : v.1 ∉ trace q1 p1 := fun hm => by
              have := hrem1 v.1 hm; omega
            rw [htr]
            refine ⟨List.nodup_cons.mpr ⟨hv_not_mem, hnod1⟩, ?_, ?_⟩
            · intro i hi
              simp only [List.mem_cons] at hi
              rcases hi with rfl | hi
              · omega
              · have hi' := hrem1 i hi
                have hne : i ≠ v.1 := fun h => by rw [h] at hi'; omega
                dsimp only [ρ1] at hi'
                split_ifs at hi' <;> rwa [rem_update_other ρ v _ i hne] at hi'
            · simp only [List.map_cons, List.sum_cons, rheight]
              have hwv := hw v.1
              omega
        · intro p hp
          rw [sdiff_combine] at hp
          rcases Finset.mem_union.mp hp with hp0_img | hp1_img
          · obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hp0_img
            obtain ⟨C, hCF, hC⟩ := hleaf0 p0 hp0
            refine ⟨C, hCF, fun lit hlit => ?_⟩
            rcases hC lit hlit with ⟨hrem0, hbv⟩ | ⟨j, hjq, hjb⟩
            · by_cases hlv : lit.1 = v.1
              · right
                refine ⟨⟨0, by simp⟩, by simp [q, hlv], ?_⟩
                rw [hlv, hbv0] at hbv
                simpa using hbv
              · left
                dsimp only [ρ0] at hrem0 hbv
                split_ifs at hrem0 hbv
                · rw [rem_update_other ρ v false lit.1 hlv] at hrem0
                  rw [blockVal_update_other ρ v false lit.1 hlv] at hbv
                  exact ⟨hrem0, hbv⟩
                · rw [rem_update_other ρ v true lit.1 hlv] at hrem0
                  rw [blockVal_update_other ρ v true lit.1 hlv] at hbv
                  exact ⟨hrem0, hbv⟩
            · right
              refine ⟨⟨j.val + 1, by simp⟩, ?_, ?_⟩
              · simpa [q] using hjq
              · simpa using hjb
          · obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hp1_img
            obtain ⟨C, hCF, hC⟩ := hleaf1 p1 hp1
            refine ⟨C, hCF, fun lit hlit => ?_⟩
            rcases hC lit hlit with ⟨hrem1, hbv⟩ | ⟨j, hjq, hjb⟩
            · by_cases hlv : lit.1 = v.1
              · right
                refine ⟨⟨0, by simp⟩, by simp [q, hlv], ?_⟩
                rw [hlv, hbv1] at hbv
                simpa using hbv
              · left
                dsimp only [ρ1] at hrem1 hbv
                split_ifs at hrem1 hbv
                · rw [rem_update_other ρ v true lit.1 hlv] at hrem1
                  rw [blockVal_update_other ρ v true lit.1 hlv] at hbv
                  exact ⟨hrem1, hbv⟩
                · rw [rem_update_other ρ v false lit.1 hlv] at hrem1
                  rw [blockVal_update_other ρ v false lit.1 hlv] at hbv
                  exact ⟨hrem1, hbv⟩
            · right
              refine ⟨⟨j.val + 1, by simp⟩, ?_, ?_⟩
              · simpa [q] using hjq
              · simpa using hjb
        · have same : partialBits (Function.update ρ v (some true))=partialBits (Function.update ρ v (some false)) := by omega
          by_cases e : bF=false
          · apply budget_mono (budget_merge (fun p=>w (q p)-1) (by simpa [q,M0,A0,q0,e] using hsuml) (by simpa [q,M1,A1,q1,e] using hsumr))
            change w v.1-1+joinRank _ _ ≤ rr (.node v l r)+partialBits ρ
            rw [same,jr_shift]; dsimp only [rr]; omega
          · apply budget_mono (budget_merge (fun p=>w (q p)-1) (by simpa [q,M0,A0,q0,e] using hsumr) (by simpa [q,M1,A1,q1,e] using hsuml))
            change w v.1-1+joinRank _ _ ≤ rr (.node v l r)+partialBits ρ
            rw [same,jr_shift,jr_flip (rr r)]; dsimp only [rr]; omega
    · cases hρv : ρ v with
      | none => exact absurd hρv hnone
      | some b =>
        cases b
        · have hupd : Function.update ρ v (some false) = ρ := by
            funext u; by_cases h : u = v
            · subst h; simp [hρv]
            · simp [h]
          rw [hupd] at hSl
          obtain ⟨M, A, q, hsh, hM, hleaf, hsum⟩ := ihl ρ hSl
          refine ⟨M, A, q, hsh, ?_, hleaf, ?_⟩
          · intro p hp
            obtain ⟨h1, h2, h3⟩ := hM p hp
            exact ⟨h1, h2, by dsimp only [rheight]; omega⟩
          · apply budget_mono hsum; dsimp only [rr,joinRank]; split_ifs <;> omega
        · have hupd : Function.update ρ v (some true) = ρ := by
            funext u; by_cases h : u = v
            · subst h; simp [hρv]
            · simp [h]
          rw [hupd] at hSr
          obtain ⟨M, A, q, hsh, hM, hleaf, hsum⟩ := ihr ρ hSr
          refine ⟨M, A, q, hsh, ?_, hleaf, ?_⟩
          · intro p hp
            obtain ⟨h1, h2, h3⟩ := hM p hp
            exact ⟨h1, h2, by dsimp only [rheight]; omega⟩
          · apply budget_mono hsum; dsimp only [rr,joinRank]; split_ifs <;> omega

lemma resolve_rtree {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    ∀ (T : RTree (RawType n w)) (ρ : RawType n w → Option Bool),
      RSound F ρ T →
      ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (RawType n w)),
        shape N J ∧
        Falsifies ρ (line []) ∧
        (∀ p ∈ N, p.length ≤ rheight T) ∧
        Budget N J (fun _=>0) (rr T) ∧
        (∀ p ∈ N \ J, liftAx F (line p)) ∧
        (∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
          (line (p ++ [false])) (line (p ++ [true])) (line p)) := by
  intro T
  induction T with
  | leaf =>
    intro ρ ⟨Cl, hax, hfals⟩
    refine ⟨{[]}, ∅, fun _ => Cl, shape_leaf, hfals, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton.mp hp]; simp [rheight]
    · exact budgetLeaf _ _
    · intro p _; exact hax
    · intro p hp; exact absurd hp (Finset.notMem_empty _)
  | node v l r ihl ihr =>
    intro ρ ⟨hSl, hSr⟩
    obtain ⟨N0, J0, line0, hsh0, hf0, hht0, hlf0, hax0, hres0⟩ :=
      ihl (Function.update ρ v (some false)) hSl
    obtain ⟨N1, J1, line1, hsh1, hf1, hht1, hlf1, hax1, hres1⟩ :=
      ihr (Function.update ρ v (some true)) hSr
    by_cases hv0 : (v, true) ∈ line0 []
    · by_cases hv1 : (v, false) ∈ line1 []
      · let R := (line0 []).erase (v, true) ∪ (line1 []).erase (v, false)
        let N := insert [] (N0.image (false :: ·) ∪ N1.image (true :: ·))
        let J := insert [] (J0.image (false :: ·) ∪ J1.image (true :: ·))
        let line : List Bool → PEqualNP.ProofComplexity.Clause (RawType n w) := fun p =>
          match p with
          | [] => R
          | false :: t => line0 t
          | true :: t => line1 t
        refine ⟨N, J, line, shape_combine hsh0 hsh1, ?_, ?_, ?_, ?_, ?_⟩
        · intro lit hlit
          rcases Finset.mem_union.mp hlit with hl0 | hl1
          · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hl0
            have h := hf0 lit hmem
            have hlv : lit.1 ≠ v := by
              intro heq
              rw [heq, Function.update_self] at h
              have hlt : lit.2 = true := by cases hlb : lit.2 <;> simp_all
              exact hne (Prod.ext heq hlt)
            rwa [Function.update_of_ne hlv] at h
          · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hl1
            have h := hf1 lit hmem
            have hlv : lit.1 ≠ v := by
              intro heq
              rw [heq, Function.update_self] at h
              have hlf : lit.2 = false := by cases hlb : lit.2 <;> simp_all
              exact hne (Prod.ext heq hlf)
            rwa [Function.update_of_ne hlv] at h
        · intro p hp
          simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with rfl | ⟨p0, hp0, rfl⟩ | ⟨p1, hp1, rfl⟩
          · simp
          · have := hht0 p0 hp0; simp only [List.length_cons, rheight]; omega
          · have := hht1 p1 hp1; simp only [List.length_cons, rheight]; omega
        · simpa only [Nat.zero_add,rr] using budget_merge (fun _=>0) hlf0 hlf1
        · intro p hp
          rw [sdiff_combine] at hp
          rcases Finset.mem_union.mp hp with hp0_img | hp1_img
          · obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hp0_img
            exact hax0 p0 hp0
          · obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hp1_img
            exact hax1 p1 hp1
        · intro p hp
          simp only [J, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with rfl | ⟨p0, hp0, rfl⟩ | ⟨p1, hp1, rfl⟩
          · exact ⟨v, hv0, hv1, rfl⟩
          · exact hres0 p0 hp0
          · exact hres1 p1 hp1
      · refine ⟨N1, J1, line1, hsh1, ?_, ?_, ?_, hax1, hres1⟩
        · intro lit hlit
          have h := hf1 lit hlit
          have hlv : lit.1 ≠ v := by
            intro heq
            rw [heq, Function.update_self] at h
            have hlf : lit.2 = false := by cases hlb : lit.2 <;> simp_all
            have hlit_eq : lit = (v, false) := Prod.ext heq hlf
            exact hv1 (hlit_eq ▸ hlit)
          rwa [Function.update_of_ne hlv] at h
        · intro p hp; have := hht1 p hp; dsimp only [rheight]; omega
        · apply budget_mono hlf1; dsimp only [rr,joinRank]; split_ifs <;> omega
    · refine ⟨N0, J0, line0, hsh0, ?_, ?_, ?_, hax0, hres0⟩
      · intro lit hlit
        have h := hf0 lit hlit
        have hlv : lit.1 ≠ v := by
          intro heq
          rw [heq, Function.update_self] at h
          have hlt : lit.2 = true := by cases hlb : lit.2 <;> simp_all
          have hlit_eq : lit = (v, true) := Prod.ext heq hlt
          exact hv0 (hlit_eq ▸ hlit)
        rwa [Function.update_of_ne hlv] at h
      · intro p hp; have := hht0 p hp; dsimp only [rheight]; omega
      · apply budget_mono hlf0; dsimp only [rr,joinRank]; split_ifs <;> omega

def expandBlock {n : ℕ} {w : Fin n → ℕ} (i : Fin n)
    (tFalse tTrue : RTree (RawType n w)) :
    ∀ (remSteps : ℕ), remSteps ≤ w i → Bool → RTree (RawType n w)
  | 0, _, acc => if acc = false then tFalse else tTrue
  | k + 1, hk, acc =>
      let idx : Fin (w i) := ⟨w i - (k + 1), by omega⟩
      RTree.node ⟨i, idx⟩
        (expandBlock i tFalse tTrue k (by omega) acc)
        (expandBlock i tFalse tTrue k (by omega) (!acc))

lemma expandBlock_height {n : ℕ} {w : Fin n → ℕ} (i : Fin n)
    (tFalse tTrue : RTree (RawType n w)) :
    ∀ (k : ℕ) (hk : k ≤ w i) (acc : Bool),
      rheight (expandBlock i tFalse tTrue k hk acc) ≤ k + max (rheight tFalse) (rheight tTrue) := by
  intro k
  induction k with
  | zero =>
    intro hk acc
    dsimp only [expandBlock]
    split_ifs <;> omega
  | succ k ih =>
    intro hk acc
    dsimp only [expandBlock, rheight]
    have h0 := ih (by omega) acc
    have h1 := ih (by omega) (!acc)
    omega

lemma expandBlock_sound {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (i : Fin n) (tFalse tTrue : RTree (RawType n w)) :
    ∀ (k : ℕ) (hk : k ≤ w i) (ρ : RawType n w → Option Bool) (acc : Bool),
      (∀ (ρ' : RawType n w → Option Bool),
        (∀ j : Fin (w i), j.val < w i - k → ρ' ⟨i, j⟩ = ρ ⟨i, j⟩) →
        (∀ b : RawType n w, b.1 ≠ i → ρ' b = ρ b) →
        (∀ j : Fin (w i), w i - k ≤ j.val → ∃ b : Bool, ρ' ⟨i, j⟩ = some b) →
        let finalAcc :=
          (List.ofFn (fun j : Fin k => (ρ' ⟨i, ⟨w i - k + j.val, by omega⟩⟩).getD false)).foldl xor acc
        if finalAcc = false then RSound F ρ' tFalse else RSound F ρ' tTrue) →
      RSound F ρ (expandBlock i tFalse tTrue k hk acc) := by
  intro k
  induction k with
  | zero =>
    intro hk ρ acc hcond
    have h := hcond ρ (fun _ _ => rfl) (fun _ _ => rfl) (fun j hj => by have := j.isLt; omega)
    dsimp only [expandBlock]
    cases acc <;> simpa using h
  | succ k ih =>
    intro hk ρ acc hcond
    dsimp only [expandBlock, RSound]
    let idx : Fin (w i) := ⟨w i - (k + 1), by omega⟩
    constructor
    · refine ih (by omega) (Function.update ρ ⟨i, idx⟩ (some false)) acc ?_
      intro ρ' hlt hoth hge
      have hlt' : ∀ j : Fin (w i), j.val < w i - (k + 1) → ρ' ⟨i, j⟩ = ρ ⟨i, j⟩ := by
        intro j hj
        rw [hlt j (by omega)]
        have hne : (⟨i, j⟩ : RawType n w) ≠ ⟨i, idx⟩ := by
          intro h; have := congrArg (fun x : RawType n w => x.2.val) h
          dsimp only [idx] at this; omega
        exact Function.update_of_ne hne _ _
      have hoth' : ∀ b : RawType n w, b.1 ≠ i → ρ' b = ρ b := by
        intro b hb
        rw [hoth b hb]
        have hne : b ≠ ⟨i, idx⟩ := fun h => hb (congrArg Sigma.fst h)
        exact Function.update_of_ne hne _ _
      have hidx_val : ρ' ⟨i, idx⟩ = some false := by
        rw [hlt idx (by dsimp only [idx]; omega), Function.update_self]
      have hge' : ∀ j : Fin (w i), w i - (k + 1) ≤ j.val → ∃ b : Bool, ρ' ⟨i, j⟩ = some b := by
        intro j hj
        by_cases hjeq : j.val = w i - (k + 1)
        · have hj' : j = idx := Fin.ext hjeq
          exact ⟨false, hj' ▸ hidx_val⟩
        · exact hge j (by omega)
      have hres := hcond ρ' hlt' hoth' hge'
      have hfold :
          (List.ofFn (fun j : Fin (k + 1) => (ρ' ⟨i, ⟨w i - (k + 1) + j.val, by omega⟩⟩).getD false)).foldl xor acc =
          (List.ofFn (fun j : Fin k => (ρ' ⟨i, ⟨w i - k + j.val, by omega⟩⟩).getD false)).foldl xor acc := by
        rw [List.ofFn_succ, List.foldl_cons]
        simp only [Fin.val_zero, Fin.val_succ]
        have h0 : (⟨w i - (k + 1) + 0, by omega⟩ : Fin (w i)) = idx := Fin.ext (by dsimp [idx])
        rw [h0, hidx_val]
        simp only [Option.getD_some, Bool.xor_false]
        congr 2
        funext j
        have heq : (⟨w i - (k + 1) + (j.val + 1), by omega⟩ : Fin (w i)) = ⟨w i - k + j.val, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [heq]
      dsimp only at hres ⊢
      rwa [hfold] at hres
    · refine ih (by omega) (Function.update ρ ⟨i, idx⟩ (some true)) (!acc) ?_
      intro ρ' hlt hoth hge
      have hlt' : ∀ j : Fin (w i), j.val < w i - (k + 1) → ρ' ⟨i, j⟩ = ρ ⟨i, j⟩ := by
        intro j hj
        rw [hlt j (by omega)]
        have hne : (⟨i, j⟩ : RawType n w) ≠ ⟨i, idx⟩ := by
          intro h; have := congrArg (fun x : RawType n w => x.2.val) h
          dsimp only [idx] at this; omega
        exact Function.update_of_ne hne _ _
      have hoth' : ∀ b : RawType n w, b.1 ≠ i → ρ' b = ρ b := by
        intro b hb
        rw [hoth b hb]
        have hne : b ≠ ⟨i, idx⟩ := fun h => hb (congrArg Sigma.fst h)
        exact Function.update_of_ne hne _ _
      have hidx_val : ρ' ⟨i, idx⟩ = some true := by
        rw [hlt idx (by dsimp only [idx]; omega), Function.update_self]
      have hge' : ∀ j : Fin (w i), w i - (k + 1) ≤ j.val → ∃ b : Bool, ρ' ⟨i, j⟩ = some b := by
        intro j hj
        by_cases hjeq : j.val = w i - (k + 1)
        · have hj' : j = idx := Fin.ext hjeq
          exact ⟨true, hj' ▸ hidx_val⟩
        · exact hge j (by omega)
      have hres := hcond ρ' hlt' hoth' hge'
      have hfold :
          (List.ofFn (fun j : Fin (k + 1) => (ρ' ⟨i, ⟨w i - (k + 1) + j.val, by omega⟩⟩).getD false)).foldl xor acc =
          (List.ofFn (fun j : Fin k => (ρ' ⟨i, ⟨w i - k + j.val, by omega⟩⟩).getD false)).foldl xor (!acc) := by
        rw [List.ofFn_succ, List.foldl_cons]
        simp only [Fin.val_zero, Fin.val_succ]
        have h0 : (⟨w i - (k + 1) + 0, by omega⟩ : Fin (w i)) = idx := Fin.ext (by dsimp [idx])
        rw [h0, hidx_val]
        simp only [Option.getD_some, Bool.xor_true]
        congr 2
        funext j
        have heq : (⟨w i - (k + 1) + (j.val + 1), by omega⟩ : Fin (w i)) = ⟨w i - k + j.val, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [heq]
      dsimp only at hres ⊢
      rwa [hfold] at hres


lemma expand_rank {n : ℕ} {w : Fin n→ℕ} (i : Fin n) (l r : RTree (RawType n w)) (k : ℕ)
    (hk : k+1≤w i) (b : Bool) : rr (expandBlock i l r (k+1) hk b)=k+joinRank (rr l) (rr r) := by
  induction k generalizing b with
  | zero => cases b <;> simp [expandBlock,rr,joinRank,eq_comm,max_comm] <;> split_ifs <;> omega
  | succ k ih =>
    change joinRank (rr (expandBlock i l r (k+1) _ b)) (rr (expandBlock i l r (k+1) _ (!b)))=_
    rw [ih (by omega) b,ih (by omega) (!b)]
    simp [joinRank]; omega

lemma build_rtree_from_outer {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (M A : Finset (List Bool)) (q : List Bool → Fin n) (H : ℕ)
    (rank : List Bool→ℕ) (law : RankLaw M A (fun p=>w (q p)-1) rank)
    (hsh : shape M A)
    (hM : ∀ p ∈ M, (trace q p).Nodup ∧ ((trace q p).map w).sum ≤ H)
    (hleaf : ∀ p ∈ M \ A, ∃ C ∈ F, ∀ lit ∈ C, ∃ j : Fin p.length,
      q (p.take j.val) = lit.1 ∧ p.get j ≠ lit.2) :
    ∀ (d : ℕ) (p : List Bool), p ∈ M → n - p.length ≤ d →
      ∃ T : RTree (RawType n w),
        (∀ ρ : RawType n w → Option Bool,
          (∀ j : Fin p.length,
            (∀ t : Fin (w (q (p.take j.val))), ∃ b : Bool, ρ ⟨q (p.take j.val), t⟩ = some b) ∧
            blockVal ρ (q (p.take j.val)) = p.get j) →
          RSound F ρ T) ∧
        rheight T + ((trace q p).map w).sum ≤ H ∧
        rr T ≤ rank p := by
  have hleaf_case : ∀ (p : List Bool), p ∈ M → p ∉ A →
      ∃ T : RTree (RawType n w),
        (∀ ρ : RawType n w → Option Bool,
          (∀ j : Fin p.length,
            (∀ t : Fin (w (q (p.take j.val))), ∃ b : Bool, ρ ⟨q (p.take j.val), t⟩ = some b) ∧
            blockVal ρ (q (p.take j.val)) = p.get j) →
          RSound F ρ T) ∧
        rheight T + ((trace q p).map w).sum ≤ H ∧
        rr T ≤ rank p := by
    intro p hp hnotA
    have hmem : p ∈ M \ A := Finset.mem_sdiff.mpr ⟨hp, hnotA⟩
    obtain ⟨C, hCF, hC⟩ := hleaf p hmem
    refine ⟨RTree.leaf, ?_, ?_, ?_⟩
    · intro ρ hρ
      let y : RawType n w → Bool := fun b => (ρ b).getD false
      let Cl : PEqualNP.ProofComplexity.Clause (RawType n w) :=
        ((Finset.univ : Finset (RawType n w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
          (fun b => (b, !(y b)))
      refine ⟨Cl, ⟨C, hCF, y, ?_, rfl⟩, ?_⟩
      · intro lit hlit
        obtain ⟨j, hjq, hjb⟩ := hC lit hlit
        have hbv := (hρ j).2
        rw [hjq] at hbv
        have heq : parity y lit.1 = blockVal ρ lit.1 := rfl
        rw [heq, hbv]
        exact hjb
      · intro lit hlit
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hlit
        have hb_var : b.1 ∈ C.image Prod.fst := (Finset.mem_filter.mp hb).2
        obtain ⟨clit, hclit, hcb⟩ := Finset.mem_image.mp hb_var
        obtain ⟨j, hjq, _⟩ := hC clit hclit
        have hsome := (hρ j).1 (hcb.symm.trans hjq.symm ▸ b.2)
        obtain ⟨bv, hbv⟩ := hsome
        have heq_b : (⟨q (p.take j.val), hcb.symm.trans hjq.symm ▸ b.2⟩ : RawType n w) = b := by
          cases b with
          | mk b1 b2 =>
            dsimp only at hcb ⊢
            exact Sigma.ext (hjq.trans hcb) (by simp)
        rw [heq_b] at hbv
        simp only [y, hbv, Option.getD_some, Bool.not_not]
    · dsimp only [rheight]
      have := (hM p hp).2
      omega
    · exact Nat.zero_le _
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have hnotA : p ∉ A := by
      intro hpA
      have hp0 := (hsh.2.2.2 p hpA).1
      have hnod := (hM (p ++ [false]) hp0).1
      have hlen_le : (trace q (p ++ [false])).length ≤ Fintype.card (Fin n) :=
        List.Nodup.length_le_card hnod
      simp only [trace, List.length_ofFn, List.length_append, List.length_singleton,
        Fintype.card_fin] at hlen_le
      omega
    exact hleaf_case p hp hnotA
  | succ d ih =>
    intro p hp hd
    by_cases hpA : p ∈ A
    · have hp0 : p ++ [false] ∈ M := (hsh.2.2.2 p hpA).1
      have hp1 : p ++ [true] ∈ M := (hsh.2.2.2 p hpA).2
      have hlen0 : n - (p ++ [false]).length ≤ d := by simp; omega
      have hlen1 : n - (p ++ [true]).length ≤ d := by simp; omega
      let i := q p
      have hnod0 := (hM (p ++ [false]) hp0).1
      have htr_append : ∀ b : Bool, trace q (p ++ [b]) = trace q p ++ [i] := by
        intro b
        apply List.ext_getElem
        · simp [trace]
        · intro idx h1 h2
          by_cases hidx : idx < p.length
          · rw [List.getElem_append_left (by simpa [trace] using hidx)]
            simp only [trace, List.getElem_ofFn, List.take_append_of_le_length (le_of_lt hidx)]
          · have hidx_eq : idx = p.length := by simp [trace] at h1; omega
            subst hidx_eq
            rw [List.getElem_append_right (by simp [trace])]
            simp only [trace, List.getElem_ofFn, List.length_ofFn, Nat.sub_self,
              List.getElem_singleton, List.take_left', i]
      have hi_not_in_p : ∀ j : Fin p.length, q (p.take j.val) ≠ i := by
        intro j heq
        rw [htr_append false, List.nodup_append] at hnod0
        have hmem_p : i ∈ trace q p := by
          rw [← heq]
          simp only [trace, List.mem_ofFn]
          exact ⟨j, rfl⟩
        exact hnod0.2.2 i hmem_p i (by simp) rfl
      have hsum_step : ∀ b : Bool,
          ((trace q (p ++ [b])).map w).sum = ((trace q p).map w).sum + w i := by
        intro b
        rw [htr_append b, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      obtain ⟨T0, hS0, hH0, hL0⟩ := ih (p ++ [false]) hp0 hlen0
      obtain ⟨T1, hS1, hH1, hL1⟩ := ih (p ++ [true]) hp1 hlen1
      let T := expandBlock i T0 T1 (w i) le_rfl false
      refine ⟨T, ?_, ?_, ?_⟩
      · intro ρ hρ
        refine expandBlock_sound F i T0 T1 (w i) le_rfl ρ false ?_
        intro ρ' _ hoth hge
        have hfull : ∀ t : Fin (w i), ∃ v : Bool, ρ' ⟨i, t⟩ = some v := by
          intro t
          exact hge t (by omega)
        have hacc_eq :
            (List.ofFn (fun j : Fin (w i) => (ρ' ⟨i, ⟨w i - w i + j.val, by omega⟩⟩).getD false)).foldl xor false =
              blockVal ρ' i := by
          have hpx := blockParity_prefix_xor (fun t : Fin (w i) => (ρ' ⟨i, t⟩).getD false) (w i) le_rfl
          have hbv :
              decide (Odd ((Finset.univ : Finset (Fin (w i))).filter
                (fun j => j.val < w i ∧ (ρ' ⟨i, j⟩).getD false = true)).card) = blockVal ρ' i := by
            unfold blockVal parity
            congr 3
            ext j
            simp
          rw [hbv] at hpx
          rw [hpx]
          congr 2
          funext j
          have hj_eq : (⟨w i - w i + j.val, by omega⟩ : Fin (w i)) = ⟨j.val, j.isLt⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hj_eq]
        have hbranch : ∀ (b : Bool), blockVal ρ' i = b →
            (∀ j : Fin (p ++ [b]).length,
              (∀ t : Fin (w (q ((p ++ [b]).take j.val))), ∃ v : Bool, ρ' ⟨q ((p ++ [b]).take j.val), t⟩ = some v) ∧
              blockVal ρ' (q ((p ++ [b]).take j.val)) = (p ++ [b]).get j) := by
          intro b hbv j
          by_cases hj : j.val < p.length
          · have htake : (p ++ [b]).take j.val = p.take j.val := List.take_append_of_le_length (le_of_lt hj)
            have hget : (p ++ [b]).get j = p.get ⟨j.val, hj⟩ := by
              simp [List.getElem_append_left hj]
            have hne : q (p.take j.val) ≠ i := hi_not_in_p ⟨j.val, hj⟩
            rw [htake, hget]
            constructor
            · intro t
              rw [hoth ⟨q (p.take j.val), t⟩ hne]
              exact (hρ ⟨j.val, hj⟩).1 t
            · have hbv_eq : blockVal ρ' (q (p.take j.val)) = blockVal ρ (q (p.take j.val)) := by
                unfold blockVal parity
                congr 3
                ext t
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hoth ⟨q (p.take j.val), t⟩ hne]
              rw [hbv_eq]
              exact (hρ ⟨j.val, hj⟩).2
          · have hjeq : j.val = p.length := by have := j.isLt; simp at this; omega
            have htake : (p ++ [b]).take j.val = p := by rw [hjeq]; simp
            have hget : (p ++ [b]).get j = b := by
              simp [hjeq]
            rw [htake, hget]
            exact ⟨hfull, hbv⟩
        dsimp only
        rw [hacc_eq]
        cases hbv : blockVal ρ' i
        · simp only [↓reduceIte]
          exact hS0 ρ' (hbranch false hbv)
        · simp only [Bool.true_eq_false, ↓reduceIte]
          exact hS1 ρ' (hbranch true hbv)
      · have hh := expandBlock_height i T0 T1 (w i) le_rfl false
        rw [hsum_step false] at hH0
        rw [hsum_step true] at hH1
        dsimp only [T]
        omega
      · have hwi := hw i
        have hrt : rr T=(w i-1)+joinRank (rr T0) (rr T1) := by
          have sz : (w i-1)+1=w i := by omega
          have e : T=expandBlock i T0 T1 ((w i-1)+1) (by omega) false := by dsimp only [T]; congr 1 <;> omega
          rw [e,expand_rank]
        rw [hrt,law.2 p hpA]
        exact Nat.add_le_add_left (jr_mono hL0 hL1) _
    · exact hleaf_case p hp hpA


theorem prefix_inner (N J : Finset (List Bool)) (hs : shape N J) (p : List Bool) (hp : p∈N)
    (j : ℕ) (hj : j<p.length) : p.take j∈J := by
  induction p using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton l b ih =>
    have hi := hs.2.2.1 l b hp
    have bound : j ≤ l.length := by simp at hj; omega
    rw [List.take_append_of_le_length bound]
    rcases bound.eq_or_lt with h|h
    · simpa [h] using hi
    · exact ih (hs.2.1 hi) _ h

theorem someTrace {n : ℕ} (q : List Bool→Fin n) (ask : List Bool→Option (Fin n)) (N J : Finset (List Bool))
    (sh : shape N J) (ag : ∀ u∈J,ask u=some (q u)) (p : List Bool) (hp : p∈N) :
    trace ask p=(trace q p).map some := by
  unfold trace
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact ag _ (prefix_inner N J sh p hp j.val j.isLt)


open PEqualNP.ProofComplexity

lemma prefix_inj {n : ℕ} (q : List Bool → Fin n) (p : List Bool) (hn : (trace q p).Nodup) :
    Function.Injective (fun j : Fin p.length=>q (p.take j.val)) := by
  unfold trace at hn
  exact List.nodup_ofFn.mp hn

lemma trace_assignment {n : ℕ} (q : List Bool→Fin n) (p : List Bool) (nd : (trace q p).Nodup) (d : Bool) :
    ∃ x : Fin n→Bool,(∀ j : Fin p.length,x (q (p.take j.val))=p.get j) ∧
      ∀ v,(∀ j : Fin p.length,q (p.take j.val)≠v) → x v=d := by
  classical
  let g := fun j : Fin p.length=>q (p.take j.val)
  let x := fun v=>if h : ∃ j,g j=v then p.get h.choose else d
  refine ⟨x,?_,?_⟩
  · intro j
    have ex : ∃ k,g k=g j := ⟨j,rfl⟩
    change (if h : ∃ k,g k=g j then p.get h.choose else d)=_
    rw [dif_pos ex]
    exact congrArg p.get (prefix_inj q p nd ex.choose_spec)
  · intro v h; simp only [x,dif_neg (show ¬∃j,g j=v from fun ⟨j,e⟩=>h j e)]

lemma leaf_data {n : ℕ} (F : Set (Clause (Fin n))) (q : List Bool→Fin n) (p : List Bool)
    (C : Clause (Fin n)) (nd : (trace q p).Nodup)
    (valid : ∀ x : Fin n→Bool,(∀ j : Fin p.length,x (q (p.take j.val))=p.get j) → C∈F ∧ ¬ClauseSat x C) :
    C∈F ∧ ∀ l∈C,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2 := by
  obtain ⟨x,hx,_⟩ := trace_assignment q p nd false
  refine ⟨(valid x hx).1,?_⟩
  intro l hl
  obtain ⟨y,hy,hd⟩ := trace_assignment q p nd l.2
  have ne : y l.1≠l.2 := fun e=>(valid y hy).2 ⟨l,hl,e⟩
  by_contra miss
  by_cases ex : ∃ j : Fin p.length,q (p.take j.val)=l.1
  · obtain ⟨j,e⟩ := ex
    exact miss ⟨j,e,fun h=>ne (e ▸ (hy j).trans h)⟩
  · exact ne (hd _ (fun j e=>ex ⟨j,e⟩))

theorem leaf_some (N J : Finset (List Bool)) (sh : shape N J) : (N\J).Nonempty := by
  obtain ⟨p,hp,hi⟩ := Finset.exists_max_image N List.length ⟨[],sh.1⟩
  refine ⟨p,Finset.mem_sdiff.mpr ⟨hp,?_⟩⟩
  intro h
  have b := hi _ (sh.2.2.2 p h).1
  simp at b


open PEqualNP.ProofComplexity in
theorem rankIff : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw)
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false]))
        (line (p ++ [true])) (line p) ∧ r p = join (r (p ++ [false])) (r (p ++ [true]))
  let search := fun {V Ans : Type} (len fee : V → ℕ) (pay : Ans → ℕ)
      (ok : (V → Bool) → Ans → Prop) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (q : List Bool → Option V)
      (out : List Bool → Ans) (r : List Bool → ℕ),
      shape N J ∧ r [] ≤ s ∧
      (∀ p ∈ N, (List.ofFn (fun j : Fin p.length => q (p.take j.val))).Nodup ∧
        (List.ofFn (fun j : Fin p.length => (q (p.take j.val)).elim 0 len)).sum ≤ H) ∧
      (∀ p ∈ J, ∃ v, q p = some v ∧
        r p = fee v + join (r (p ++ [false])) (r (p ++ [true]))) ∧
      ∀ p ∈ N \ J, r p = pay (out p) ∧ ∀ x : V → Bool,
        (∀ j : Fin p.length, (q (p.take j.val)).map x = some (p.get j)) → ok x (out p)
  ∀ (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ),
    refutes F H s ↔ search w (fun i => w i-1) (fun _ => 0)
      (fun x C => C ∈ F ∧ ¬ PEqualNP.ProofComplexity.ClauseSat x C) H s := by
  classical
  intro n w hw Raw par lifted sh join searchRef search F H cap
  by_cases hn : 0 < n
  · constructor
    · rintro ⟨N,J,line,r,shape,root,rr0,bounded,leaves,branch⟩
      have law : RankLaw N J (fun _=>0) r := ⟨fun p h=>(leaves p h).2,fun p h=>by simpa only [Nat.zero_add,joinRank,join] using (branch p h).2⟩
      have emp : Falsifies (fun _ : RawType n w=>none) (line []) := by rw [root]; intro _ h; exact False.elim (Finset.notMem_empty _ h)
      obtain ⟨T,sound,height,rank⟩ := extract_rtree_aux F N J line H r law shape bounded (fun p hp=>(leaves p hp).1)
        (fun p hp=>(branch p hp).1) H [] shape.1 (by simp) _ emp
      obtain ⟨M,A,q,sm,walk,le,budget⟩ := extract_outer hn hw F T (fun _=>none) sound
      have init (i : Fin n) : rem (fun _ : RawType n w=>none) i=w i := by simp [rem]
      have pb : partialBits (fun _ : RawType n w=>none)=0 := by
        unfold partialBits; apply Finset.sum_eq_zero; intro i _; rw [init i]; simp
      rw [pb,Nat.add_zero] at budget
      obtain ⟨rk,hk,top⟩ := budget
      let ans := fun p=>if h : p∈M\A then (le p h).choose else ∅
      refine ⟨M,A,fun p=>some (q p),ans,rk,sm,(top.trans rank).trans rr0,?_,?_,?_⟩
      · intro p hp
        obtain ⟨nd,_,len⟩ := walk p hp
        constructor
        · have tr : (List.ofFn (fun j : Fin p.length=>some (q (p.take j.val))))=(trace q p).map some := by unfold trace; rw [List.map_ofFn]; rfl
          rw [tr]; exact nd.map (fun _ _ e=>Option.some.inj e)
        · rw [pb,Nat.add_zero] at len
          simp only [List.length_nil,Nat.sub_zero] at height
          simpa only [trace,List.map_ofFn,Function.comp_def,Option.elim_some] using len.trans height
      · intro p h; exact ⟨q p,rfl,hk.2 p h⟩
      · intro p h
        refine ⟨hk.1 p h,?_⟩
        intro x agrees
        dsimp only [ans]; rw [dif_pos h]
        obtain ⟨cf,cert⟩ := (le p h).choose_spec
        refine ⟨cf,?_⟩
        rintro ⟨lit,hl,val⟩
        rcases cert lit hl with ⟨empty,_⟩|⟨j,eq,avoid⟩
        · rw [init] at empty; have := hw lit.1; omega
        · have aj : some (x (q (p.take j.val)))=some (p.get j) := agrees j
          rw [eq,val] at aj
          exact avoid (Option.some.inj aj).symm
    · rintro ⟨M,A,ask,out,r,shape,cr,walk,branch,leaf⟩
      let q := fun p=>(ask p).getD ⟨0,hn⟩
      have atnode (p) (h : p∈A) : ask p=some (q p) := by
        obtain ⟨i,e,_⟩ := branch p h; simp [q,e]
      have law : RankLaw M A (fun p=>w (q p)-1) r := by
        refine ⟨fun p hp=>(leaf p hp).1,?_⟩
        intro p h; obtain ⟨i,e,hr⟩ := branch p h; simpa only [q,e,Option.getD_some,joinRank,join] using hr
      have qwalk (p) (h : p∈M) : (trace q p).Nodup ∧ ((trace q p).map w).sum ≤ H := by
        obtain ⟨nd,len⟩ := walk p h
        change (trace ask p).Nodup at nd
        rw [someTrace q ask M A shape atnode p h] at nd
        refine ⟨nd.of_map _,?_⟩
        have same : List.ofFn (fun j : Fin p.length=>(ask (p.take j.val)).elim 0 w)=(trace q p).map w := by
          unfold trace; rw [List.map_ofFn]; apply congrArg List.ofFn; funext j
          rw [atnode _ (prefix_inner M A shape p h j.val j.isLt)]; rfl
        simpa only [same] using len
      have certifies (p) (h : p∈M\A) : ∃ C∈F,∀ l∈C,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2 := by
        use out p
        have inM := (Finset.mem_sdiff.mp h).1
        apply leaf_data F q p (out p) (qwalk _ inM).1
        intro x ax
        apply (leaf p h).2 x
        intro j
        rw [atnode _ (prefix_inner M A shape p inM j.val j.isLt)]
        exact congrArg some (ax j)
      obtain ⟨T,sound,he,rrk⟩ := build_rtree_from_outer hw F M A q H r law shape qwalk certifies n [] shape.1 (by simp)
      obtain ⟨N,J,line,shN,fal,hgt,budget,ax,res⟩ := resolve_rtree F T (fun _=>none) (sound _ (fun j=>Fin.elim0 j))
      obtain ⟨rk,lawN,lb⟩ := budget
      have rt : line []=∅ := Finset.eq_empty_of_forall_notMem (fun l hl=>by have h := fal l hl; cases h)
      refine ⟨N,J,line,rk,shN,rt,(lb.trans rrk).trans cr,?_,?_,?_⟩
      · intro p h; have b := hgt p h; simp [trace] at he; omega
      · exact fun p h=>⟨ax p h,lawN.1 p h⟩
      · exact fun p h=>⟨res p h,by simpa only [Nat.zero_add,joinRank,join] using lawN.2 p h⟩
  · have ce (C : Clause (Fin n)) : C=∅ := Finset.eq_empty_of_forall_notMem (fun l _=>by have := l.1.isLt; omega)
    constructor
    · rintro ⟨N,J,line,r,hs,_,_,_,leaf,_⟩
      obtain ⟨p,hp⟩ := leaf_some N J hs
      obtain ⟨C,hC,_⟩ := (leaf p hp).1
      refine ⟨{[]},∅,fun _=>none,fun _=>C,fun _=>0,shape_leaf,Nat.zero_le _,?_,by simp,?_⟩
      · intro p hp; rw [Finset.mem_singleton.mp hp]; simp
      · intro p _; refine ⟨rfl,fun x _=>⟨hC,?_⟩⟩; rw [ce C]; simp [ClauseSat]
    · rintro ⟨M,A,ask,out,r,hs,_,_,branch,leaf⟩
      have empty : []∉A := fun h=>by obtain ⟨i,_,_⟩ := branch [] h; have := i.isLt; omega
      have h := (leaf [] (Finset.mem_sdiff.mpr ⟨hs.1,empty⟩)).2 (fun _=>false) (fun j=>Fin.elim0 j)
      refine ⟨{[]},∅,fun _=>∅,fun _=>0,shape_leaf,rfl,Nat.zero_le _,?_,?_,by simp⟩
      · intro p hp; rw [Finset.mem_singleton.mp hp]; simp
      · intro p _; refine ⟨⟨out [],h.1,fun _=>false,?_,?_⟩,rfl⟩ <;> rw [ce (out [])] <;> simp


open PEqualNP.ProofComplexity

def edge (n e : ℕ) : Clause (Fin n) :=
  ((Finset.univ.filter (fun v : Fin n=>v.val+1=e)).image fun v=>(v,false)) ∪
  ((Finset.univ.filter (fun v : Fin n=>v.val=e)).image fun v=>(v,true))
def edges (n : ℕ) : Set (Clause (Fin n)) := {C | ∃ e : Fin (n+1), C=edge n e.val}
def thr (n e : ℕ) (v : Fin n) := decide (v.val < e)
def boundary {n} (x : Fin n→Bool) (i j : ℕ) :=
  (∀ v : Fin n,v.val+1=i → x v=true) ∧ (∀ v : Fin n,v.val=j → x v=false)
lemma edge_miss {n} (x : Fin n→Bool) (e : ℕ) :
    ¬ClauseSat x (edge n e) ↔ boundary x e e := by
  classical
  constructor
  · intro miss; constructor
    · intro v hv; cases h : x v with
      | true => rfl
      | false => exact False.elim (miss ⟨(v,false),Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,by simp [hv],rfl⟩),h⟩)
    · intro v hv; cases h : x v with
      | false => rfl
      | true => exact False.elim (miss ⟨(v,true),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,by simp [hv],rfl⟩),h⟩)
  · rintro ⟨l,r⟩ ⟨lit,hl,hv⟩
    simp only [edge,Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] at hl
    rcases hl with ⟨v,e,rfl⟩|⟨v,e,rfl⟩
    · change x v=false at hv; rw [l v e] at hv; contradiction
    · change x v=true at hv; rw [r v e] at hv; contradiction

lemma threshold_unique {n i e : ℕ} (hi : i ≤ n) (he : e ≤ n)
    (miss : ¬ClauseSat (thr n i) (edge n e)) : i=e := by
  obtain ⟨l,r⟩ := (edge_miss ..).mp miss
  by_cases h : e < i
  · have contra := r ⟨e,by omega⟩ rfl
    simp [thr,h] at contra
  · by_cases h' : i < e
    · have contra := l ⟨e-1,by omega⟩ (by dsimp; omega)
      simp [thr,show ¬e-1 < i by omega] at contra
    · omega

def fits {n : ℕ} (w : Fin n→ℕ) : ℕ→ℕ→ℕ→ℕ→ℕ→Prop := Nat.rec
  (fun i j _ _=>i=j) (fun _ prev i j H s => i=j ∨ ∃ v : Fin n,i ≤ v.val ∧ v.val < j ∧ w v ≤ H ∧
    ∃ a b : ℕ,(w v-1)+joinRank a b ≤ s ∧ prev i v.val (H-w v) a ∧ prev (v.val+1) j (H-w v) b)
lemma fits_point {n} (w : Fin n→ℕ) (d i H s : ℕ) : fits w d i i H s := by
  cases d <;> simp [fits]
lemma fits_weaken {n} (w : Fin n→ℕ) {d i j H s} (h : fits w d i j H s) :
    ∀ {d' H' s' : ℕ},d ≤ d' → H ≤ H' → s ≤ s' → fits w d' i j H' s' := by
  induction d generalizing i j H s with
  | zero => intro d' H' s' _ _ _; change i=j at h; subst j; exact fits_point ..
  | succ d ih =>
    intro d' H' s' hd hh hs
    cases d' with
    | zero => omega
    | succ u =>
      rcases h with eq|⟨v,lv,rv,ok,a,b,fee,l,r⟩
      · exact Or.inl eq
      · exact Or.inr ⟨v,lv,rv,le_trans ok hh,a,b,fee.trans hs,
          ih l (by omega) (by omega) le_rfl,ih r (by omega) (by omega) le_rfl⟩

def Agrees {V : Type} (q : List Bool→Option V) (p : List Bool) (x : V→Bool) :=
  ∀ j : Fin p.length, (q (p.take j.val)).map x=some (p.get j)
def toll {V : Type} (w : V→ℕ) (q : List Bool→Option V) (p : List Bool) :=
  ((trace q p).map (fun z=>z.elim 0 w)).sum
lemma trace_snoc {V : Type} (q : List Bool→V) (p : List Bool) (b : Bool) :
    trace q (p++[b])=trace q p++[q p] := by
  apply List.ext_getElem
  · simp [trace]
  · intro j h1 h2
    by_cases h : j < p.length
    · rw [List.getElem_append_left (by simpa [trace] using h)]
      simp only [trace,List.getElem_ofFn,List.take_append_of_le_length (le_of_lt h)]
    · have e : j=p.length := by simp [trace] at h1; omega
      subst j; rw [List.getElem_append_right (by simp [trace])]
      simp only [trace,List.getElem_ofFn,List.length_ofFn,Nat.sub_self,List.getElem_singleton,List.take_left']
lemma agree_snoc {V : Type} (q : List Bool→Option V) (p : List Bool) (x : V→Bool)
    (v : V) (e : q p=some v) (ok : Agrees q p x) : Agrees q (p++[x v]) x := by
  intro j
  by_cases h : j.val < p.length
  · simpa only [List.take_append_of_le_length (le_of_lt h),List.get_eq_getElem,List.getElem_append_left h] using ok ⟨j.val,h⟩
  · have e' : j.val=p.length := by have := j.isLt; simp at this; omega
    simp [e',e,List.get_eq_getElem]



theorem contract_intervals {n} (w : Fin n→ℕ) (M A : Finset (List Bool)) (ask : List Bool→Option (Fin n))
    (out : List Bool→Clause (Fin n)) (r : List Bool→ℕ) (H : ℕ) (sh : shape M A)
    (bounded : ∀ p∈M,toll w ask p  ≤  H)
    (branch : ∀ p∈A,∃ v,ask p=some v ∧ r p=w v-1+joinRank (r (p++[false])) (r (p++[true])))
    (leaf : ∀ p∈M\A,∀ x, Agrees ask p x → out p∈edges n ∧ ¬ClauseSat x (out p)) :
    fits w n 0 n H (r []) := by
  classical
  let L := M.sum List.length
  have maxL (p) (h : p∈M) : p.length  ≤  L := Finset.single_le_sum (f:=List.length) (fun _ _=>Nat.zero_le _) h
  have aux (d : ℕ) : ∀ p∈M,L-p.length  ≤  d → ∀ i j : ℕ,i ≤ j → j ≤ n →
      (∀ e,i ≤ e → e ≤ j → Agrees ask p (thr n e)) →
      fits w (j-i) i j (H-toll w ask p) (r p) := by
    induction d with
    | zero =>
      intro p hp hlen i j lo hi agree
      have leafP : p∈M\A := by
        refine Finset.mem_sdiff.mpr ⟨hp,?_⟩
        intro inner
        have m := maxL _ (sh.2.2.2 p inner).1; simp at m; omega
      obtain ⟨⟨e,ec⟩,mi⟩ := leaf _ leafP _ (agree i le_rfl lo)
      have mj := (leaf _ leafP _ (agree j lo le_rfl)).2
      rw [ec] at mi mj
      have ei := threshold_unique (lo.trans hi) (Nat.le_of_lt_succ e.isLt) mi
      have ej := threshold_unique hi (Nat.le_of_lt_succ e.isLt) mj
      rw [ei,ej]; exact fits_point ..
    | succ d ih =>
      intro p hp hlen i j lo hi agree
      by_cases same : i=j
      · subst j; exact fits_point ..
      by_cases inner : p∈A
      · obtain ⟨v,ev,er⟩ := branch p inner
        have hc (b : Bool) : p++[b]∈M := by cases b with
          | false => exact (sh.2.2.2 p inner).1
          | true => exact (sh.2.2.2 p inner).2
        have nw (b : Bool) : toll w ask (p++[b])=toll w ask p+w v := by simp [toll,trace_snoc,ev]
        have bh := bounded _ (hc false); rw [nw] at bh
        have descend (b : Bool) (a z : ℕ) (az : a ≤ z) (ia : i ≤ a) (zj : z ≤ j)
            (constant : ∀ e,a ≤ e → e ≤ z → thr n e v=b) :
            fits w (z-a) a z ((H-toll w ask p)-w v) (r (p++[b])) := by
          have hd : L-(p++[b]).length  ≤  d := by simp; omega
          have eqH : (H-toll w ask p)-w v=H-toll w ask (p++[b]) := by rw [nw]; omega
          rw [eqH]
          refine ih _ (hc b) hd a z az (zj.trans hi) ?_
          intro e ae ez
          have ok := agree_snoc ask p (thr n e) v ev (agree e (ia.trans ae) (ez.trans zj))
          rwa [constant e ae ez] at ok
        by_cases before : v.val < i
        · have rgt := descend true i j lo le_rfl le_rfl (fun e a _=>by simp [thr,show v.val < e by omega])
          apply fits_weaken w rgt le_rfl (by omega)
          dsimp [joinRank] at er; split_ifs at er <;> omega
        · by_cases after : j ≤ v.val
          · have lft := descend false i j lo le_rfl le_rfl (fun e _ a=>by simp [thr,show ¬v.val < e by omega])
            apply fits_weaken w lft le_rfl (by omega)
            dsimp [joinRank] at er; split_ifs at er <;> omega
          · have lft := descend false i v.val (by omega) (by omega) (by omega) (fun e _ a=>by simp [thr,show ¬v.val < e by omega])
            have rgt := descend true (v.val+1) j (by omega) (by omega) (by omega) (fun e a _=>by simp [thr,show v.val < e by omega])
            have len : j-i=(j-i-1)+1 := by omega
            rw [len]
            exact Or.inr ⟨v,by omega,by omega,by omega,_,_,er.symm.le, fits_weaken w lft (by omega) le_rfl le_rfl,
              fits_weaken w rgt (by omega) le_rfl le_rfl⟩
      · have hpL := Finset.mem_sdiff.mpr ⟨hp,inner⟩
        obtain ⟨⟨e,ec⟩,mi⟩ := leaf _ hpL _ (agree i le_rfl lo)
        have mj := (leaf _ hpL _ (agree j lo le_rfl)).2
        rw [ec] at mi mj
        have ei := threshold_unique (lo.trans hi) (Nat.le_of_lt_succ e.isLt) mi
        have ej := threshold_unique hi (Nat.le_of_lt_succ e.isLt) mj
        exact False.elim (same (ei.trans ej.symm))
  simpa [toll,trace] using aux L [] sh.1 (by simp) 0 n (by omega) le_rfl (fun _ _ _ j=>Fin.elim0 j)


def fee {n} (w : Fin n→ℕ) (q : List Bool→Option (Fin n)) (p : List Bool) := (q p).elim 0 (fun v=>w v-1)
def Build {n} (w : Fin n→ℕ) (i j H s : ℕ) := ∃ (N J : Finset (List Bool)) (q : List Bool→Option (Fin n))
    (out : List Bool→Fin (n+1)), shape N J ∧ Budget N J (fee w q) s ∧
    (∀ p∈J,∃ v,q p=some v) ∧
    (∀ p∈N,(trace q p).Nodup ∧ toll w q p  ≤  H ∧ ∀ z∈trace q p,∃ v,z=some v ∧ i ≤ v.val ∧ v.val < j) ∧
    ∀ p∈N\J,∀ x,Agrees q p x → boundary x i j → boundary x (out p).val (out p).val

lemma build_pt {n} (w : Fin n→ℕ) {i H s} (hi : i ≤ n) : Build w i i H s := by
  refine ⟨{[]},∅,fun _=>none,fun _=>⟨i,by omega⟩,shape_leaf,budgetLeaf ..,by simp,?_,?_⟩
  · intro p hp; rw [Finset.mem_singleton.mp hp]; simp [trace,toll]
  · exact fun _ _ _ _ h=>h

lemma agree_cons {n} (v : Fin n) (ql qr : List Bool→Option (Fin n)) (p : List Bool) (b : Bool) (x : Fin n→Bool)
    (ok : Agrees (fork (some v) ql qr) (b::p) x) : x v=b ∧ Agrees (if b then qr else ql) p x := by
  have h := ok ⟨0,by simp⟩
  have val : x v=b := by simpa [fork] using h
  refine ⟨val,?_⟩
  intro j
  have e := ok ⟨j.val+1,by simp⟩
  cases b <;> simpa [fork,List.get_eq_getElem] using e

lemma push_walk {n} (w : Fin n→ℕ) (v : Fin n) {i j H : ℕ} (iv : i ≤ v.val) (vj : v.val < j) (feeOK : w v ≤ H)
    (a z : ℕ) (ia : i ≤ a) (zj : z ≤ j) (out : v.val < a ∨ z ≤ v.val)
    (raw : List (Option (Fin n))) (nd : raw.Nodup) (lim : (raw.map (fun u=>u.elim 0 w)).sum  ≤  H-w v)
    (bounds : ∀ t∈raw, ∃ u,t=some u ∧ a ≤ u.val ∧ u.val < z) :
    (some v::raw).Nodup ∧ ((some v::raw).map (fun u=>u.elim 0 w)).sum  ≤  H ∧
      ∀ t∈(some v::raw), ∃ u,t=some u ∧ i ≤ u.val ∧ u.val < j := by
  refine ⟨List.nodup_cons.mpr ⟨?_,nd⟩,by simp; omega,?_⟩
  · intro h; obtain ⟨u,e,lo,hi⟩ := bounds _ h; have eq := Option.some.inj e; subst u; omega
  · intro t ht
    rcases List.mem_cons.mp ht with rfl|h
    · exact ⟨v,rfl,iv,vj⟩
    · obtain ⟨u,e,lo,hi⟩ := bounds _ h
      exact ⟨u,e,ia.trans lo,lt_of_lt_of_le hi zj⟩

lemma build_join {n} (w : Fin n→ℕ) (i j H s : ℕ) (v : Fin n) (iv : i ≤ v.val) (vj : v.val < j) (ok : w v ≤ H)
    (a b : ℕ) (cost : w v-1+joinRank a b ≤ s)
    (bl : Build w i v.val (H-w v) a) (br : Build w (v.val+1) j (H-w v) b) : Build w i j H s := by
  classical
  obtain ⟨Nl,Jl,ql,ol,sl,rl,al,wl,el⟩ := bl
  obtain ⟨Nr,Jr,qr,or',sr,rr',ar,wr,er⟩ := br
  let q := fork (some v) ql qr
  have ef : q=(fun l=>match l with | []=>some v | false::p=>ql p | true::p=>qr p) := by
    funext l; cases l with
    | nil => rfl
    | cons b p => cases b <;> rfl
  let ans := fork (0 : Fin (n+1)) ol or'
  refine ⟨_,_,q,ans,shape_combine sl sr,budget_mono (budget_merge (fee w q) rl rr') cost,?_,?_,?_⟩
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hp
    rcases hp with rfl|⟨p,h,rfl⟩|⟨p,h,rfl⟩
    · exact ⟨v,rfl⟩
    · exact al _ h
    · exact ar _ h
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hp
    rcases hp with rfl|⟨p,h,rfl⟩|⟨p,h,rfl⟩
    · simp [toll,trace]
    · have eq : trace q (false::p)=some v::trace ql p := by rw [ef,trace_cons]; rfl
      unfold toll; rw [eq]
      exact push_walk w v iv vj ok i v.val le_rfl vj.le (Or.inr le_rfl) _ (wl _ h).1 (wl _ h).2.1 (wl _ h).2.2
    · have eq : trace q (true::p)=some v::trace qr p := by rw [ef,trace_cons]; rfl
      unfold toll; rw [eq]
      exact push_walk w v iv vj ok (v.val+1) j (by omega) le_rfl (Or.inl (by omega)) _ (wr _ h).1 (wr _ h).2.1 (wr _ h).2.2
  · intro p hp x agr B
    rw [sdiff_combine] at hp
    rcases Finset.mem_union.mp hp with h|h
    · obtain ⟨p,hp0,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨answer,agree⟩ := agree_cons v ql qr p false x agr
      apply el p hp0 x agree
      exact ⟨B.1,fun u eq=>by have e : u=v := Fin.ext eq; simpa [e] using answer⟩
    · obtain ⟨p,hp0,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨answer,agree⟩ := agree_cons v ql qr p true x agr
      apply er p hp0 x agree
      exact ⟨fun u eq=>by have e : u=v := Fin.ext (by omega); simpa [e] using answer,B.2⟩

theorem fits_build {n} (w : Fin n→ℕ) {d i j H s} (bound : j ≤ n) (h : fits w d i j H s) : Build w i j H s := by
  induction d generalizing i j H s with
  | zero => change i=j at h; subst i; exact build_pt w bound
  | succ _ ih =>
    rcases h with rfl|⟨v,iv,vj,ok,a,b,c,l,r⟩
    · exact build_pt w bound
    · exact build_join w i j H s v iv vj ok a b c (ih v.isLt.le l) (ih bound r)



open PEqualNP.ProofComplexity in
theorem intervalIff : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw)
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false]))
        (line (p ++ [true])) (line p) ∧ r p = join (r (p ++ [false])) (r (p ++ [true]))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C | ∃ e : Fin (n+1),
    C = (((Finset.univ : Finset (Fin n)).filter (fun v => v.val+1 = e.val)).image
      (fun v => (v,false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
      (fun v => (v,true)))}
  let feasible : ℕ → ℕ → ℕ → ℕ → ℕ → Prop := Nat.rec
    (fun i j _ _ => i = j)
    (fun _ prev i j H s => i = j ∨ ∃ v : Fin n, i ≤ v.val ∧ v.val < j ∧ w v ≤ H ∧
      ∃ a b : ℕ, (w v-1) + join a b ≤ s ∧ prev i v.val (H-w v) a ∧ prev (v.val+1) j (H-w v) b)
  ∀ H s : ℕ, refutes F H s ↔ feasible n 0 n H s := by
  classical
  intro n w hw Raw par la sh join ref F feasible H s
  have convert := rankIff n w hw (edges n) H s
  constructor
  · intro h
    obtain ⟨M,A,ask,out,r,shape,c,walk,br,fl⟩ := convert.mp h
    change fits w n 0 n H s
    apply fits_weaken w (contract_intervals w M A ask out r H shape ?_ br (fun p hp=>(fl p hp).2)) le_rfl le_rfl c
    intro p hp
    simpa only [toll,trace,List.map_ofFn,Function.comp_def] using (walk p hp).2
  · intro h
    change fits w n 0 n H s at h
    obtain ⟨M,A,q,out,shape,⟨r,law,cap⟩,ask,walk,le⟩ := fits_build w le_rfl h
    apply convert.mpr
    refine ⟨M,A,q,fun p=>edge n (out p).val,r,shape,cap,?_,?_,?_⟩
    · intro p hp
      refine ⟨(walk p hp).1,?_⟩
      simpa only [toll,trace,List.map_ofFn,Function.comp_def] using (walk p hp).2.1
    · intro p hp; obtain ⟨v,e⟩ := ask p hp
      refine ⟨v,e,?_⟩
      simpa only [fee,e,Option.elim_some,joinRank] using law.2 p hp
    · intro p hp; refine ⟨law.1 p hp,?_⟩
      intro x agr
      have B : boundary x 0 n := ⟨fun v eq=>by omega,fun v eq=>by have := v.isLt; omega⟩
      exact ⟨⟨out p,rfl⟩,(edge_miss _ _).mpr (le p hp x agr B)⟩


open Finset

def slice (b s l j : ℕ) := if (b-1)*l+j+b  ≤  s then Nat.choose l j else 0
def layer (b s l : ℕ) := (range (l+1)).sum (slice b s l)
def capacity (b d s : ℕ) := (range d).sum (layer b s)
lemma cap_monotone {b d s t : ℕ} (h : s ≤ t) : capacity b d s  ≤  capacity b d t := by
  apply sum_le_sum; intro l _; apply sum_le_sum; intro j _
  unfold slice; split_ifs <;> omega
lemma cap_small {b s : ℕ} (less : s < b) (d : ℕ) : capacity b d s=0 := by
  apply sum_eq_zero; intro l _; apply sum_eq_zero; intro j _; unfold slice; split_ifs <;> omega
lemma slice_pascal {b s : ℕ} (bp : 0 < b) (sb : b ≤ s) (l j : ℕ) :
    slice b s (l+1) (j+1)=slice b (s-(b-1)) l (j+1)+slice b (s-b) l j := by
  unfold slice; rw [Nat.mul_succ,Nat.choose_succ_succ]; simp only [Nat.succ_eq_add_one]; split_ifs <;> omega
lemma slice_left {b s : ℕ} (sb : b ≤ s) (l : ℕ) :
    slice b s (l+1) 0=slice b (s-(b-1)) l 0 := by
  unfold slice; rw [Nat.mul_succ]; simp only [Nat.choose_zero_right]; split_ifs <;> omega
lemma layer_step {b s : ℕ} (bp : 0 < b) (sb : b ≤ s) (l : ℕ) :
    layer b s (l+1)=layer b (s-(b-1)) l+layer b (s-b) l := by
  unfold layer; rw [sum_range_succ']
  simp_rw [slice_pascal bp sb]; rw [sum_add_distrib,slice_left sb]
  have last : slice b (s-(b-1)) l (l+1)=0 := by simp [slice,Nat.choose_eq_zero_of_lt]
  have shift : (∑ j∈range (l+1), slice b (s-(b-1)) l (j+1))+slice b (s-(b-1)) l 0 =
      (range (l+1)).sum (slice b (s-(b-1)) l) := by
    rw [←sum_range_succ',sum_range_succ,last,add_zero]
  rw [←shift]; ac_rfl
lemma cap_step {b s : ℕ} (bp : 0 < b) (sb : b ≤ s) (d : ℕ) :
    capacity b (d+1) s=1+capacity b d (s-(b-1))+capacity b d (s-b) := by
  unfold capacity; rw [sum_range_succ']; simp_rw [layer_step bp sb]
  rw [sum_add_distrib]; have first : layer b s 0=1 := by simp [layer,slice,sb]
  rw [first]; ac_rfl

lemma div_height {H b : ℕ} (bp : 0 < b) (bh : b ≤ H) : (H-b)/b+1=H/b := by
  calc
    _ = ((H-b)+b)/b := (Nat.add_div_right _ bp).symm
    _ = _ := by rw [Nat.sub_add_cancel bh]

theorem fits_upper {n b d i j H s : ℕ} (bp : 0 < b) (h : fits (fun _ : Fin n=>b) d i j H s) :
    j-i  ≤  capacity b (H/b) s := by
  induction d generalizing i j H s with
  | zero => change i=j at h; omega
  | succ d ih =>
    rcases h with rfl|⟨v,iv,vj,bh,a,c,fee,left,right⟩
    · omega
    · have sizes (x : ℕ) : x=x := Eq.refl x
      change b ≤ H at bh
      change b-1+joinRank a c  ≤  s at fee
      have sb : b ≤ s := by unfold joinRank at fee; split_ifs at fee <;> omega
      have paid : (a ≤ s-(b-1) ∧ c ≤ s-b) ∨ (a ≤ s-b ∧ c ≤ s-(b-1)) := by
        unfold joinRank at fee; split_ifs at fee <;> omega
      have lbd := ih left
      have rbd := ih right
      rw [←div_height bp bh,cap_step bp sb]
      rcases paid with ⟨u,v'⟩|⟨u,v'⟩
      · have l := lbd.trans (cap_monotone u); have r := rbd.trans (cap_monotone v'); dsimp at l r; omega
      · have l := lbd.trans (cap_monotone u); have r := rbd.trans (cap_monotone v'); dsimp at l r; omega

theorem make_fit {n b : ℕ} (bp : 0 < b) (d i j H s : ℕ) (ij : i ≤ j) (jn : j ≤ n) (enough : j-i ≤ d)
    (bound : j-i  ≤  capacity b (H/b) s) : fits (fun _ : Fin n=>b) d i j H s := by
  induction d generalizing i j H s with
  | zero => change i=j; omega
  | succ d ih =>
    by_cases eq : i=j
    · exact Or.inl eq
    have sb : b ≤ s := by
      by_contra no; rw [cap_small (by omega)] at bound; omega
    have bh : b ≤ H := by
      by_contra no; have dz : H/b=0 := Nat.div_eq_of_lt (by omega); rw [dz] at bound
      simp [capacity] at bound; omega
    rw [←div_height bp bh,cap_step bp sb] at bound
    let a := s-(b-1)
    let c := s-b
    let L := capacity b ((H-b)/b) a
    let R := capacity b ((H-b)/b) c
    have cap : j-i  ≤  1+L+R := bound
    let t := i+min L (j-i-1)
    have ti : i ≤ t := Nat.le_add_right ..
    have tj : t < j := by dsimp [t]; omega
    let v : Fin n := ⟨t,by omega⟩
    refine Or.inr ⟨v,ti,tj,bh,a,c,?_,?_,?_⟩
    · change b-1+joinRank a c  ≤  s
      unfold joinRank; dsimp only [a,c]; split_ifs <;> omega
    · exact ih i t (H-b) a ti (by omega) (by omega) (by change t-i ≤ L; dsimp only [t]; omega)
    · exact ih (t+1) j (H-b) c (by omega) jn (by omega) (by change j-(t+1) ≤ R; dsimp only [t]; omega)


end PEqualNP.Outside.L_pcx_338_aux

open PEqualNP.Outside.L_pcx_338_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_338 : ∀ (n b : ℕ), 0 < b →
  let w := fun (_ : Fin n) => b
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let join := fun a b : ℕ => if a = b then a+1 else max a b
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H s : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw)
      (r : List Bool → ℕ), shape N J ∧ line [] = ∅ ∧ r [] ≤ s ∧ (∀ p ∈ N, p.length ≤ H) ∧
      (∀ p ∈ N \ J, liftAx F (line p) ∧ r p = 0) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false]))
        (line (p ++ [true])) (line p) ∧ r p = join (r (p ++ [false])) (r (p ++ [true]))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C | ∃ e : Fin (n+1),
    C = (((Finset.univ : Finset (Fin n)).filter (fun v => v.val+1 = e.val)).image
      (fun v => (v,false))) ∪ (((Finset.univ : Finset (Fin n)).filter (fun v => v.val = e.val)).image
      (fun v => (v,true)))}
  ∀ H s : ℕ, refutes F H s ↔
    n ≤ (Finset.range (H/b)).sum (fun l => (Finset.range (l+1)).sum
      (fun j => if (b-1)*l + j + b ≤ s then Nat.choose l j else 0)) := by
  classical
  intro n b bp w Raw par la shape join ref F H s
  have previous := intervalIff n (fun _=>b) (fun _=>bp) H s
  constructor
  · intro h
    have f := previous.mp h
    change fits (fun _ : Fin n=>b) n 0 n H s at f
    change n ≤ capacity b (H/b) s
    simpa only [Nat.sub_zero] using fits_upper bp f
  · intro h
    change n ≤ capacity b (H/b) s at h
    apply previous.mpr
    apply make_fit bp n 0 n H s (by omega) le_rfl (by omega)
    simpa only [Nat.sub_zero] using h


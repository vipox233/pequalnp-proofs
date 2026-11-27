import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_330_aux

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

lemma extract_rtree_aux {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (RawType n w))
    (H : ℕ)
    (hshape : shape N J) (hlen : ∀ p ∈ N, p.length ≤ H)
    (hax : ∀ p ∈ N \ J, liftAx F (line p))
    (hres : ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
      (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ (d : ℕ) (p : List Bool), p ∈ N → H - p.length ≤ d →
      ∀ ρ : RawType n w → Option Bool, Falsifies ρ (line p) →
        ∃ T : RTree (RawType n w),
          RSound F ρ T ∧
          rheight T ≤ H - p.length ∧
          rleaves T ≤ ((N \ J).filter (fun q => p <+: q)).card := by
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
    have hmem : p ∈ (N \ J).filter (fun q => p <+: q) :=
      Finset.mem_filter.mpr ⟨hleaf, List.prefix_refl p⟩
    exact Finset.card_pos.mpr ⟨p, hmem⟩
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
        · refine le_trans hL0 (Finset.card_le_card ?_)
          intro q hq
          simp only [Finset.mem_filter] at hq ⊢
          exact ⟨hq.1, List.IsPrefix.trans (List.prefix_append p [false]) hq.2⟩
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
          · refine le_trans hL1 (Finset.card_le_card ?_)
            intro q hq
            simp only [Finset.mem_filter] at hq ⊢
            exact ⟨hq.1, List.IsPrefix.trans (List.prefix_append p [true]) hq.2⟩
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
          · dsimp only [rleaves]
            have hdisj : Disjoint ((N \ J).filter (fun q => p ++ [false] <+: q))
                ((N \ J).filter (fun q => p ++ [true] <+: q)) := by
              rw [Finset.disjoint_left]
              intro q hq0 hq1
              obtain ⟨t0, ht0⟩ := (Finset.mem_filter.mp hq0).2
              obtain ⟨t1, ht1⟩ := (Finset.mem_filter.mp hq1).2
              have heq := ht0.trans ht1.symm
              rw [List.append_assoc, List.append_assoc] at heq
              have htail := List.append_cancel_left heq
              exact Bool.noConfusion (List.cons.inj htail).1
            have hsub :
                (N \ J).filter (fun q => p ++ [false] <+: q) ∪
                  (N \ J).filter (fun q => p ++ [true] <+: q) ⊆
                (N \ J).filter (fun q => p <+: q) := by
              intro q hq
              simp only [Finset.mem_union, Finset.mem_filter] at hq ⊢
              rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
              · exact ⟨hq1, List.IsPrefix.trans (List.prefix_append p [false]) hq2⟩
              · exact ⟨hq1, List.IsPrefix.trans (List.prefix_append p [true]) hq2⟩
            have hcard_sum :
                ((N \ J).filter (fun q => p ++ [false] <+: q)).card +
                  ((N \ J).filter (fun q => p ++ [true] <+: q)).card ≤
                ((N \ J).filter (fun q => p <+: q)).card := by
              rw [← Finset.card_union_of_disjoint hdisj]
              exact Finset.card_le_card hsub
            omega
    · have hleaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hp, hpJ⟩
      refine ⟨RTree.leaf, ⟨line p, hax p hleaf, hfals⟩, Nat.zero_le _, ?_⟩
      have hmem : p ∈ (N \ J).filter (fun q => p <+: q) :=
        Finset.mem_filter.mpr ⟨hleaf, List.prefix_refl p⟩
      exact Finset.card_pos.mpr ⟨p, hmem⟩

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
        (M \ A).sum (fun p => 2 ^ (((trace q p).map w).sum - p.length)) ≤
          rleaves T * 2 ^ partialBits ρ := by
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
    · simp only [Finset.sdiff_empty, Finset.sum_singleton, trace, List.length_nil, List.ofFn_zero,
        List.map_nil, List.sum_nil, Nat.sub_self, pow_zero, rleaves, one_mul]
      exact Nat.one_le_two_pow
  | node v l r ihl ihr =>
    intro ρ ⟨hSl, hSr⟩
    by_cases hnone : ρ v = none
    · have hrem_pos : 1 ≤ rem ρ v.1 := by
        unfold rem
        exact Finset.card_pos.mpr ⟨v.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩⟩
      by_cases hge2 : 2 ≤ rem ρ v.1
      · by_cases hcmp : rleaves l ≤ rleaves r
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
          · dsimp only [rleaves]
            rw [hpb, pow_succ] at hsum
            have h2 : 2 * rleaves l ≤ rleaves l + rleaves r := by omega
            calc (M \ A).sum (fun p => 2 ^ (((trace q p).map w).sum - p.length))
                ≤ rleaves l * (2 ^ partialBits ρ * 2) := hsum
              _ = (2 * rleaves l) * 2 ^ partialBits ρ := by ring
              _ ≤ (rleaves l + rleaves r) * 2 ^ partialBits ρ := Nat.mul_le_mul_right _ h2
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
          · dsimp only [rleaves]
            rw [hpb, pow_succ] at hsum
            have h2 : 2 * rleaves r ≤ rleaves l + rleaves r := by omega
            calc (M \ A).sum (fun p => 2 ^ (((trace q p).map w).sum - p.length))
                ≤ rleaves r * (2 ^ partialBits ρ * 2) := hsum
              _ = (2 * rleaves r) * 2 ^ partialBits ρ := by ring
              _ ≤ (rleaves l + rleaves r) * 2 ^ partialBits ρ := Nat.mul_le_mul_right _ h2
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
        · have hlen_ge : ∀ (qf : List Bool → Fin n) (p : List Bool),
              p.length ≤ ((trace qf p).map w).sum := by
            intro qf p
            have hl : p.length = (trace qf p).length := by simp [trace]
            rw [hl]
            have h1 : ∀ L : List (Fin n), L.length ≤ (L.map w).sum := by
              intro L
              induction L with
              | nil => simp
              | cons a t ih =>
                simp only [List.length_cons, List.map_cons, List.sum_cons]
                have := hw a
                omega
            exact h1 (trace qf p)
          rw [sdiff_combine, Finset.sum_union (disjoint_cons_images _ _),
            Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2),
            Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)]
          have hs0 :
              ∑ p0 ∈ M0 \ A0, 2 ^ (((trace q (false :: p0)).map w).sum - (false :: p0).length) =
                2 ^ (w v.1 - 1) * ∑ p0 ∈ M0 \ A0, 2 ^ (((trace q0 p0).map w).sum - p0.length) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p0 _ => ?_)
            have htr : trace q (false :: p0) = v.1 :: trace q0 p0 := by
              simpa [q] using trace_cons v.1 q0 q1 false p0
            rw [htr, List.map_cons, List.sum_cons, List.length_cons]
            have hge0 := hlen_ge q0 p0
            have hwv := hw v.1
            have hexp : w v.1 + ((trace q0 p0).map w).sum - (p0.length + 1) =
                (w v.1 - 1) + (((trace q0 p0).map w).sum - p0.length) := by omega
            rw [hexp, pow_add]
          have hs1 :
              ∑ p1 ∈ M1 \ A1, 2 ^ (((trace q (true :: p1)).map w).sum - (true :: p1).length) =
                2 ^ (w v.1 - 1) * ∑ p1 ∈ M1 \ A1, 2 ^ (((trace q1 p1).map w).sum - p1.length) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p1 _ => ?_)
            have htr : trace q (true :: p1) = v.1 :: trace q1 p1 := by
              simpa [q] using trace_cons v.1 q0 q1 true p1
            rw [htr, List.map_cons, List.sum_cons, List.length_cons]
            have hge1 := hlen_ge q1 p1
            have hwv := hw v.1
            have hexp : w v.1 + ((trace q1 p1).map w).sum - (p1.length + 1) =
                (w v.1 - 1) + (((trace q1 p1).map w).sum - p1.length) := by omega
            rw [hexp, pow_add]
          rw [hs0, hs1, ← mul_add]
          have hsum_both :
              (∑ p0 ∈ M0 \ A0, 2 ^ (((trace q0 p0).map w).sum - p0.length)) +
                (∑ p1 ∈ M1 \ A1, 2 ^ (((trace q1 p1).map w).sum - p1.length)) =
              (∑ p0 ∈ Ml \ Al, 2 ^ (((trace ql p0).map w).sum - p0.length)) +
                (∑ p1 ∈ Mr \ Ar, 2 ^ (((trace qr p1).map w).sum - p1.length)) := by
            dsimp only [M0, A0, q0, M1, A1, q1]
            split_ifs
            · rfl
            · exact add_comm _ _
          rw [hsum_both]
          have hpb_eq : partialBits (Function.update ρ v (some false)) =
              partialBits (Function.update ρ v (some true)) := by omega
          calc 2 ^ (w v.1 - 1) *
                ((∑ p0 ∈ Ml \ Al, 2 ^ (((trace ql p0).map w).sum - p0.length)) +
                  (∑ p1 ∈ Mr \ Ar, 2 ^ (((trace qr p1).map w).sum - p1.length)))
              ≤ 2 ^ (w v.1 - 1) *
                (rleaves l * 2 ^ partialBits (Function.update ρ v (some false)) +
                  rleaves r * 2 ^ partialBits (Function.update ρ v (some true))) :=
                Nat.mul_le_mul_left _ (Nat.add_le_add hsuml hsumr)
            _ = (rleaves l + rleaves r) *
                (2 ^ partialBits (Function.update ρ v (some false)) * 2 ^ (w v.1 - 1)) := by
                rw [← hpb_eq]; ring
            _ = rleaves (RTree.node v l r) * 2 ^ partialBits ρ := by
                rw [← pow_add, ← hpb_l]; rfl
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
          · exact le_trans hsum (Nat.mul_le_mul_right _ (by dsimp only [rleaves]; omega))
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
          · exact le_trans hsum (Nat.mul_le_mul_right _ (by dsimp only [rleaves]; omega))

lemma resolve_rtree {n : ℕ} {w : Fin n → ℕ}
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) :
    ∀ (T : RTree (RawType n w)) (ρ : RawType n w → Option Bool),
      RSound F ρ T →
      ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (RawType n w)),
        shape N J ∧
        Falsifies ρ (line []) ∧
        (∀ p ∈ N, p.length ≤ rheight T) ∧
        (N \ J).card ≤ rleaves T ∧
        (∀ p ∈ N \ J, liftAx F (line p)) ∧
        (∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
          (line (p ++ [false])) (line (p ++ [true])) (line p)) := by
  intro T
  induction T with
  | leaf =>
    intro ρ ⟨Cl, hax, hfals⟩
    refine ⟨{[]}, ∅, fun _ => Cl, shape_leaf, hfals, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton.mp hp]; simp [rheight]
    · simp [rleaves]
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
        · rw [sdiff_combine, Finset.card_union_of_disjoint (disjoint_cons_images _ _),
            Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
            Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)]
          dsimp only [rleaves]
          omega
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
        · dsimp only [rleaves]; omega
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
      · dsimp only [rleaves]; omega

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

lemma expandBlock_leaves {n : ℕ} {w : Fin n → ℕ} (i : Fin n)
    (tFalse tTrue : RTree (RawType n w)) :
    ∀ (k : ℕ) (hk : k + 1 ≤ w i) (acc : Bool),
      rleaves (expandBlock i tFalse tTrue (k + 1) hk acc) =
        2 ^ k * (rleaves tFalse + rleaves tTrue) := by
  intro k
  induction k with
  | zero =>
    intro hk acc
    cases acc <;> simp [expandBlock, rleaves, add_comm]
  | succ k ih =>
    intro hk acc
    rw [expandBlock, rleaves, ih (by omega) acc, ih (by omega) (!acc), pow_succ]
    ring

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

lemma build_rtree_from_outer {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (M A : Finset (List Bool)) (q : List Bool → Fin n) (H : ℕ)
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
        rleaves T * 2 ^ (((trace q p).map w).sum - p.length) ≤
          ((M \ A).filter (fun r => p <+: r)).sum
            (fun r => 2 ^ (((trace q r).map w).sum - r.length)) := by
  have hleaf_case : ∀ (p : List Bool), p ∈ M → p ∉ A →
      ∃ T : RTree (RawType n w),
        (∀ ρ : RawType n w → Option Bool,
          (∀ j : Fin p.length,
            (∀ t : Fin (w (q (p.take j.val))), ∃ b : Bool, ρ ⟨q (p.take j.val), t⟩ = some b) ∧
            blockVal ρ (q (p.take j.val)) = p.get j) →
          RSound F ρ T) ∧
        rheight T + ((trace q p).map w).sum ≤ H ∧
        rleaves T * 2 ^ (((trace q p).map w).sum - p.length) ≤
          ((M \ A).filter (fun r => p <+: r)).sum
            (fun r => 2 ^ (((trace q r).map w).sum - r.length)) := by
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
    · dsimp only [rleaves]
      rw [one_mul]
      have hmp : p ∈ (M \ A).filter (fun r => p <+: r) :=
        Finset.mem_filter.mpr ⟨hmem, List.prefix_refl p⟩
      exact Finset.single_le_sum
        (f := fun r => 2 ^ (((trace q r).map w).sum - r.length))
        (fun _ _ => Nat.zero_le _) hmp
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
      · have hwi : 1 ≤ w i := hw i
        have hrl : rleaves T = 2 ^ (w i - 1) * (rleaves T0 + rleaves T1) := by
          have := expandBlock_leaves i T0 T1 (w i - 1) (by omega) false
          have hT_eq : T = expandBlock i T0 T1 ((w i - 1) + 1) (by omega) false := by
            dsimp only [T]
            congr 1
            omega
          rw [hT_eq]
          exact this
        have hlen_ge : p.length ≤ ((trace q p).map w).sum := by
          have hl : p.length = (trace q p).length := by simp [trace]
          rw [hl]
          have h1 : ∀ L : List (Fin n), L.length ≤ (L.map w).sum := by
            intro L
            induction L with
            | nil => simp
            | cons a t iht =>
              simp only [List.length_cons, List.map_cons, List.sum_cons]
              have := hw a; omega
          exact h1 (trace q p)
        have hexp_eq : ∀ b : Bool,
            ((trace q (p ++ [b])).map w).sum - (p ++ [b]).length =
              (w i - 1) + (((trace q p).map w).sum - p.length) := by
          intro b
          rw [hsum_step b, List.length_append, List.length_singleton]
          omega
        have hdisj : Disjoint ((M \ A).filter (fun r => p ++ [false] <+: r))
            ((M \ A).filter (fun r => p ++ [true] <+: r)) := by
          rw [Finset.disjoint_left]
          intro r hr0 hr1
          obtain ⟨t0, ht0⟩ := (Finset.mem_filter.mp hr0).2
          obtain ⟨t1, ht1⟩ := (Finset.mem_filter.mp hr1).2
          have heq := ht0.trans ht1.symm
          rw [List.append_assoc, List.append_assoc] at heq
          exact Bool.noConfusion (List.cons.inj (List.append_cancel_left heq)).1
        have hsub :
            (M \ A).filter (fun r => p ++ [false] <+: r) ∪
              (M \ A).filter (fun r => p ++ [true] <+: r) ⊆
            (M \ A).filter (fun r => p <+: r) := by
          intro r hr
          simp only [Finset.mem_union, Finset.mem_filter] at hr ⊢
          rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, List.IsPrefix.trans (List.prefix_append p [false]) h2⟩
          · exact ⟨h1, List.IsPrefix.trans (List.prefix_append p [true]) h2⟩
        have hsum_sub :
            ((M \ A).filter (fun r => p ++ [false] <+: r)).sum
              (fun r => 2 ^ (((trace q r).map w).sum - r.length)) +
            ((M \ A).filter (fun r => p ++ [true] <+: r)).sum
              (fun r => 2 ^ (((trace q r).map w).sum - r.length)) ≤
            ((M \ A).filter (fun r => p <+: r)).sum
              (fun r => 2 ^ (((trace q r).map w).sum - r.length)) := by
          rw [← Finset.sum_union hdisj]
          exact Finset.sum_le_sum_of_subset hsub
        rw [hexp_eq false, pow_add] at hL0
        rw [hexp_eq true, pow_add] at hL1
        calc rleaves T * 2 ^ (((trace q p).map w).sum - p.length)
            = rleaves T0 * (2 ^ (w i - 1) * 2 ^ (((trace q p).map w).sum - p.length)) +
              rleaves T1 * (2 ^ (w i - 1) * 2 ^ (((trace q p).map w).sum - p.length)) := by
                rw [hrl]; ring
          _ ≤ ((M \ A).filter (fun r => p ++ [false] <+: r)).sum
                (fun r => 2 ^ (((trace q r).map w).sum - r.length)) +
              ((M \ A).filter (fun r => p ++ [true] <+: r)).sum
                (fun r => 2 ^ (((trace q r).map w).sum - r.length)) :=
                Nat.add_le_add hL0 hL1
          _ ≤ ((M \ A).filter (fun r => p <+: r)).sum
                (fun r => 2 ^ (((trace q r).map w).sum - r.length)) := hsum_sub
    · exact hleaf_case p hp hpA


theorem general305 : (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ), (∀ i, 0 < w i) →
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
  let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
      shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H) ∧ (N \ J).card ≤ K ∧
      (∀ p ∈ N \ J, liftAx F (line p)) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
        (line (p ++ [false])) (line (p ++ [true])) (line p)
  let trace := fun {V : Type} (ask : List Bool → V) (p : List Bool) =>
    List.ofFn (fun j : Fin p.length => ask (p.take j.val))
  ∀ (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H K : ℕ),
    Iff (refutes F H K)
      (∃ (M A : Finset (List Bool)) (q : List Bool → Fin n),
        shape M A ∧ (∀ p ∈ M, (trace q p).Nodup ∧ ((trace q p).map w).sum ≤ H) ∧
        (∀ p ∈ M \ A, ∃ C ∈ F, ∀ lit ∈ C, ∃ j : Fin p.length,
          q (p.take j.val) = lit.1 ∧ p.get j ≠ lit.2) ∧
        (M \ A).sum (fun p => 2^(((trace q p).map w).sum - p.length)) ≤ K)) := by
  intro n hn w hw
  dsimp only
  intro F H K
  constructor
  · rintro ⟨N, J, line, hsh, hroot, hlen, hcard, hax, hres⟩
    have hfals_empty : PEqualNP.Outside.L_pcx_330_aux.Falsifies (fun _ : PEqualNP.Outside.L_pcx_330_aux.RawType n w => none) (line []) := by
      rw [hroot]
      intro lit hlit
      exact absurd hlit (Finset.notMem_empty _)
    obtain ⟨T, hS, hH, hL⟩ := PEqualNP.Outside.L_pcx_330_aux.extract_rtree_aux F N J line H
      hsh hlen hax hres H [] hsh.1 (by simp) _ hfals_empty
    obtain ⟨M, A, q, hshM, hM, hleaf, hsum⟩ :=
      PEqualNP.Outside.L_pcx_330_aux.extract_outer hn hw F T (fun _ => none) hS
    have hrem_init : ∀ i : Fin n, PEqualNP.Outside.L_pcx_330_aux.rem (fun _ : PEqualNP.Outside.L_pcx_330_aux.RawType n w => none) i = w i := by
      intro i
      simp [PEqualNP.Outside.L_pcx_330_aux.rem]
    have hpb_init : PEqualNP.Outside.L_pcx_330_aux.partialBits (fun _ : PEqualNP.Outside.L_pcx_330_aux.RawType n w => none) = 0 := by
      unfold PEqualNP.Outside.L_pcx_330_aux.partialBits
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hrem_init i]
      simp
    refine ⟨M, A, q, hshM, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hnod, _, hht⟩ := hM p hp
      rw [hpb_init, add_zero] at hht
      simp at hH
      exact ⟨hnod, le_trans hht hH⟩
    · intro p hp
      obtain ⟨C, hCF, hC⟩ := hleaf p hp
      refine ⟨C, hCF, fun lit hlit => ?_⟩
      rcases hC lit hlit with ⟨hrem0, _⟩ | hex
      · rw [hrem_init lit.1] at hrem0
        have := hw lit.1
        omega
      · exact hex
    · rw [hpb_init, pow_zero, mul_one] at hsum
      have hfilt : (N \ J).filter (fun r => [] <+: r) = N \ J := by
        ext r; simp
      rw [hfilt] at hL
      exact le_trans hsum (le_trans hL hcard)
  · rintro ⟨M, A, q, hsh, hM, hleaf, hsum⟩
    obtain ⟨T, hS, hH, hL⟩ := PEqualNP.Outside.L_pcx_330_aux.build_rtree_from_outer hw F M A q H
      hsh hM hleaf n [] hsh.1 (by simp)
    have hS0 : PEqualNP.Outside.L_pcx_330_aux.RSound F (fun _ => none) T :=
      hS (fun _ => none) (fun j => Fin.elim0 j)
    obtain ⟨N, J, line, hshN, hfals, hht, hcard, hax, hres⟩ :=
      PEqualNP.Outside.L_pcx_330_aux.resolve_rtree F T (fun _ => none) hS0
    have hroot : line [] = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro lit hlit
      have h := hfals lit hlit
      cases h
    refine ⟨N, J, line, hshN, hroot, ?_, ?_, hax, hres⟩
    · intro p hp
      have := hht p hp
      simp [PEqualNP.Outside.L_pcx_330_aux.trace] at hH
      omega
    · have hfilt : (M \ A).filter (fun r => [] <+: r) = M \ A := by
        ext r; simp
      simp only [PEqualNP.Outside.L_pcx_330_aux.trace, List.length_nil, List.ofFn_zero,
        List.map_nil, List.sum_nil, Nat.sub_self, pow_zero, mul_one, hfilt] at hL
      exact le_trans hcard (le_trans hL hsum)


open PEqualNP.ProofComplexity

abbrev Raw {n : ℕ} (w : Fin n→ℕ) := (i : Fin n) × Fin (w i)
abbrev Tape {n : ℕ} (w : Fin n→ℕ) := (i : Fin n)→Bool→Fin (w i)→Bool
abbrev Gad {n : ℕ} (w : Fin n→ℕ) := (i : Fin n)→(Fin (w i)→Bool)→Bool
abbrev B (n : ℕ) := Clause (Fin n)

def vars {n : ℕ} (C : B n) := C.image Prod.fst
def clean {n : ℕ} (C : B n) := ∀ i,¬((i,true)∈C ∧ (i,false)∈C)
def slot {n : ℕ} (C : B n) (i : Fin n) := decide ((i,false)∈C)
def sectionOK {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (s : Tape w) := ∀ i b,g i (s i b)=b
noncomputable def sections {n : ℕ} {w : Fin n→ℕ} (g : Gad w) : Finset (Tape w) :=
  Finset.univ.filter (fun s=>∀ i b,g i (s i b)=b)
def decoder {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (x : Raw w→Bool) := fun i=>g i (fun j=>x ⟨i,j⟩)
def block {n : ℕ} (w : Fin n→ℕ) (C : B n) (x : Raw w→Bool) : Clause (Raw w) :=
  ((Finset.univ : Finset (Raw w)).filter (fun z=>z.1∈vars C)).image (fun z=>(z,!(x z)))
noncomputable def copies {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) : Finset (Clause (Raw w)) :=
  (Finset.univ.filter (fun x : Raw w→Bool=>∀ l∈C,decoder g x l.1≠l.2)).image (block w C)
def reprBlock {n : ℕ} {w : Fin n→ℕ} (C : B n) (s : Tape w) := block w C (fun z=>s z.1 (slot C z.1) z.2)

theorem slot_diff {n : ℕ} (C : B n) (cc : clean C) (l : Fin n×Bool) (hl : l∈C) : slot C l.1≠l.2 := by
  obtain ⟨i,t⟩ := l
  cases t
  · simp [slot,hl]
  · have no : (i,false)∉C := fun hf=>cc i ⟨hl,hf⟩
    simp [slot,no]

theorem slot_match {n : ℕ} (C : B n) (q : Fin n→Bool) (miss : ∀ l∈C,q l.1≠l.2)
    (i : Fin n) (h : i∈vars C) : q i=slot C i := by
  obtain ⟨⟨k,t⟩,hmem,e⟩ := Finset.mem_image.mp h
  change k=i at e
  subst k
  by_cases f : (i,false)∈C
  · have v := miss (i,false) f
    simpa [slot,f] using v
  · cases t
    · contradiction
    · have v := miss (i,true) hmem
      simpa [slot,f] using v

theorem block_mem {n : ℕ} {w : Fin n→ℕ} (C : B n) (x : Raw w→Bool) (z : Raw w) (b : Bool) :
    (z,b)∈block w C x ↔ z.1∈vars C ∧ (!(x z))=b := by
  constructor
  · intro h
    obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp h
    have e : k=z := congrArg Prod.fst eq
    subst k
    exact ⟨(Finset.mem_filter.mp hk).2,congrArg Prod.snd eq⟩
  · rintro ⟨h,e⟩
    exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,Prod.ext rfl e⟩

theorem block_eq {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) :
    block w C x=block w C y ↔ ∀ z : Raw w,z.1∈vars C → x z=y z := by
  constructor
  · intro eq z h
    have m := eq ▸ (block_mem C x z (!(x z))).mpr ⟨h,rfl⟩
    have yz := ((block_mem C y z (!(x z))).mp m).2
    simpa using yz.symm
  · intro ag
    ext ⟨z,b⟩
    simp only [block_mem]
    exact and_congr_right (fun h=>by rw [ag z h])

theorem kills {n : ℕ} {w : Fin n→ℕ} (C : B n) (x y : Raw w→Bool) :
    ¬ ClauseSat x (block w C y) ↔ ∀ z : Raw w,z.1∈vars C → x z=y z := by
  constructor
  · intro no z h
    have bad : x z≠ !(y z) := fun eq=>no ⟨_,(block_mem C y z (!(y z))).mpr ⟨h,rfl⟩,eq⟩
    simpa using bad
  · rintro ag ⟨⟨z,b⟩,mem,yes⟩
    obtain ⟨h,eq⟩ := (block_mem C y z b).mp mem
    change x z=b at yes
    rw [ag z h,← eq] at yes
    simpa using yes

theorem copy_rep {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) (cc : clean C)
    (s : Tape w) (hs : sectionOK g s) : reprBlock C s∈copies g C := by
  refine Finset.mem_image.mpr ⟨fun z=>s z.1 (slot C z.1) z.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  intro l hl
  change g l.1 (s l.1 (slot C l.1))≠l.2
  rw [hs]
  exact slot_diff C cc l hl

theorem dec_agree {n : ℕ} {w : Fin n→ℕ} (g : Gad w) (C : B n) (x y : Raw w→Bool)
    (ag : ∀ z : Raw w,z.1∈vars C → x z=y z) (l : Fin n×Bool) (h : l∈C) :
    decoder g x l.1=decoder g y l.1 :=
  congrArg (g l.1) (funext (fun k=>ag ⟨l.1,k⟩ (Finset.mem_image_of_mem _ h)))

theorem parity_fiber {k : ℕ} (hk : 0<k) (b : Bool) :
    Fintype.card {x : Fin k→Bool // blockParity x=b}=2^(k-1) := by
  classical
  let j : Fin k := ⟨0,hk⟩
  let flip (x : Fin k→Bool) := Function.update x j (!(x j))
  have turn (x : Fin k→Bool) : blockParity (flip x)= !(blockParity x) := by
    have h := blockParity_update_not x j
    have own : Function.update x j (x j)=x := Function.update_eq_self j x
    cases e : x j <;> simp only [e] at own ⊢
    · simpa [flip,e,own] using h
    · rw [own] at h
      simpa [flip,e,h] using congrArg Bool.not h.symm
  have invol (x : Fin k→Bool) : flip (flip x)=x := by
    funext i
    by_cases eq : i=j <;> simp [flip,eq,Function.update_of_ne]
  let S := (Finset.univ : Finset (Fin k→Bool)).filter (fun x=>blockParity x=b)
  let Q := (Finset.univ : Finset (Fin k→Bool)).filter (fun x=>¬blockParity x=b)
  have same : S.card=Q.card := by
    apply Finset.card_bij' (fun x _=>flip x) (fun x _=>flip x)
    · intro x hx
      have eq := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [turn,eq]⟩
    · intro x hx
      have ne := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [turn]; cases z : blockParity x <;> cases b <;> simp_all⟩
    · exact fun x _=>invol x
    · exact fun x _=>invol x
  have split : S.card+Q.card=2^k := by
    simpa only [Fintype.card_fun,Fintype.card_bool,Finset.card_univ,Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset (Fin k→Bool))) (fun x=>blockParity x=b)
  have pk : 2^k=2^(k-1)*2 := by conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
  rw [Fintype.card_subtype]
  change S.card=_
  omega

theorem parity_sur {n : ℕ} (w : Fin n→ℕ) (hw : ∀ i,0<w i) (i : Fin n) (b : Bool) :
    ∃ x : Fin (w i)→Bool,blockParity x=b := by
  have pos : 0<Fintype.card {x : Fin (w i)→Bool // blockParity x=b} := by
    rw [parity_fiber (hw i)]; positivity
  obtain ⟨⟨x,h⟩⟩ := Fintype.card_pos_iff.mp pos
  exact ⟨x,h⟩

def fee {n : ℕ} (w : Fin n→ℕ) (C : B n) := 2^((vars C).sum (fun i=>w i-1))

theorem copies_card {n : ℕ} (w : Fin n→ℕ) (hw : ∀ i,0<w i) (C : B n) (cc : clean C) :
    (copies (fun i=>@blockParity (w i)) C).card=fee w C := by
  classical
  let V := vars C
  let X := (i : ↥V)→ {u : Fin (w i.val)→Bool // blockParity u=slot C i.val}
  let raw := fun (f : X) (z : Raw w) => if h : z.1∈V then (f ⟨z.1,h⟩).val z.2 else false
  let g : Gad w := fun i=>@blockParity (w i)
  let code := fun f : X=>block w C (raw f)
  have val (f : X) (i : Fin n) (hi : i∈V) : decoder g (raw f) i=slot C i := by
    simpa [decoder,g,raw,hi] using (f ⟨i,hi⟩).property
  have mem (f : X) : code f∈copies g C := by
    refine Finset.mem_image.mpr ⟨raw f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    intro l hl
    rw [val f l.1 (Finset.mem_image_of_mem _ hl)]
    exact slot_diff C cc l hl
  have inj : Function.Injective code := by
    intro f k h
    have ag := (block_eq C _ _).mp h
    funext i
    apply Subtype.ext
    funext j
    simpa [raw,i.property] using ag ⟨i.val,j⟩ i.property
  have onto (A : Clause (Raw w)) (h : A∈copies g C) : ∃ f,code f=A := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    let f : X := fun i=>⟨(fun j=>x ⟨i.val,j⟩),slot_match C (decoder g x) (Finset.mem_filter.mp hx).2 i i.property⟩
    refine ⟨f,(block_eq C _ x).mpr ?_⟩
    intro z hz
    simp [f,raw,show z.1∈V from hz]
  have id : Finset.univ.image code=copies g C := by
    ext A; simp only [Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun ⟨f,h⟩=>h ▸ mem f,onto A⟩
  change (copies g C).card=_
  rw [← id,Finset.card_image_of_injective _ inj,Finset.card_univ]
  change Fintype.card ((i : ↥V)→ {u : Fin (w i.val)→Bool // blockParity u=slot C i.val})=_
  rw [Fintype.card_pi]; simp_rw [parity_fiber (hw _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_attach V (fun i=>w i-1)

theorem private_base {n : ℕ} (F : Finset (B n)) (bad : ¬Satisfiable (F : Set (B n)))
    (minimal : ∀ C∈F,Satisfiable (F.erase C : Set (B n))) (C : B n) (hc : C∈F) :
    ∃ q, (∀ l∈C,q l.1≠l.2) ∧ ∀ D∈F,D≠C→ClauseSat q D := by
  obtain ⟨q,hq⟩ := minimal C hc
  have oth (D : B n) (hd : D∈F) (ne : D≠C) := hq D (Finset.mem_erase.mpr ⟨ne,hd⟩)
  refine ⟨q,?_,oth⟩
  intro l hl yes
  apply bad
  refine ⟨q,fun D hd=>?_⟩
  by_cases eq : D=C
  · exact eq ▸ ⟨l,hl,yes⟩
  · exact oth D hd eq

theorem clean_private {n : ℕ} (C : B n) (q : Fin n→Bool) (h : ∀l∈C,q l.1≠l.2) :
    clean C := by
  rintro i ⟨p,n⟩
  have a := h (i,true) p
  have b := h (i,false) n
  cases q i <;> simp_all

abbrev Label {n : ℕ} (w : Fin n→ℕ) (F : Finset (B n)) :=
  (C : ↥F) × ↥(copies (fun i=>@blockParity (w i)) C.val)

def labelAx {n : ℕ} {w : Fin n→ℕ} {F : Finset (B n)} (q : Label w F) := q.2.val

theorem labeled {n : ℕ} {w : Fin n→ℕ} {F : Finset (B n)} (A : Clause (Raw w)) :
    liftAx (w:=w) (F:Set (B n)) A ↔ ∃ q : Label w F,labelAx q=A := by
  constructor
  · rintro ⟨C,hC,x,miss,rfl⟩
    exact ⟨⟨⟨C,hC⟩,_,Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,miss⟩,rfl⟩⟩,rfl⟩
  · rintro ⟨⟨⟨C,hC⟩,⟨A,ha⟩⟩,rfl⟩
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨C,hC,x,(Finset.mem_filter.mp hx).2,rfl⟩

theorem private_raw {n : ℕ} (w : Fin n→ℕ) (hw : ∀i,0<w i) (F : Finset (B n))
    (bad : ¬Satisfiable (F : Set (B n))) (minF : ∀ C∈F,Satisfiable (F.erase C : Set (B n)))
    (p : Label w F) : ∃ x : Raw w→Bool, ¬ClauseSat x (labelAx p) ∧
      ∀ q : Label w F,¬ClauseSat x (labelAx q) → p=q := by
  classical
  obtain ⟨⟨C,hC⟩,⟨A,ha⟩⟩ := p
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b,badC,other⟩ := private_base F bad minF C hC
  let g : Gad w := fun i=>@blockParity (w i)
  let x : Raw w→Bool := fun z=>if z.1∈vars C then y z else (parity_sur w hw z.1 (b z.1)).choose z.2
  have ag (z : Raw w) (hz : z.1∈vars C) : x z=y z := by simp [x,hz]
  have eq (i : Fin n) : decoder g x i=b i := by
    by_cases hi : i∈vars C
    · have e : decoder g x i=decoder g y i := congrArg (g i) (funext (fun j=>ag ⟨i,j⟩ hi))
      exact e.trans ((slot_match C (decoder g y) (Finset.mem_filter.mp hy).2 i hi).trans (slot_match C b badC i hi).symm)
    · simpa [decoder,x,hi,g] using (parity_sur w hw i (b i)).choose_spec
  refine ⟨x,(kills C x y).mpr ag,?_⟩
  rintro ⟨⟨D,hD⟩,⟨A,ha⟩⟩ no
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
  have agD := (kills D x z).mp no
  have dc : D=C := by
    by_contra ne
    obtain ⟨l,hl,yes⟩ := other D hD ne
    have zd := (Finset.mem_filter.mp hz).2 l hl
    exact zd ((dec_agree g D x z agD l hl).symm.trans ((eq l.1).trans yes))
  subst D
  have yz := (block_eq C y z).mpr (fun i h=>(ag i h).symm.trans (agD i h))
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext yz))

theorem numLabels {n : ℕ} (w : Fin n→ℕ) (hw : ∀ i,0<w i) (F : Finset (B n))
    (cleanF : ∀ C∈F,clean C) : Fintype.card (Label w F)=F.sum (fee w) := by
  classical
  rw [Fintype.card_sigma]
  calc ∑ C : ↥F,Fintype.card (↥(copies (fun i=>@blockParity (w i)) C.val)) = ∑ C : ↥F,fee w C.val :=
         Finset.sum_congr rfl (fun C _=>by rw [Fintype.card_coe,copies_card w hw _ (cleanF _ C.property)])
    _ = _ := Finset.sum_attach F (fee w)


theorem query_leaf {n : ℕ} (N J : Finset (List Bool)) (hs : shape N J) (q : List Bool→Fin n) (x : Fin n→Bool) :
    ∃ p∈N\J,∀ j : Fin p.length,p.get j=x (q (p.take j.val)) := by
  classical
  let ok := fun p : List Bool => ∀ j : Fin p.length,p.get j=x (q (p.take j.val))
  let paths := N.filter ok
  have root : []∈paths := Finset.mem_filter.mpr ⟨hs.1,by simp [ok]⟩
  obtain ⟨p,hp,mx⟩ := Finset.exists_max_image paths List.length ⟨_,root⟩
  obtain ⟨pn,op⟩ := Finset.mem_filter.mp hp
  refine ⟨p,Finset.mem_sdiff.mpr ⟨pn,?_⟩,op⟩
  intro pj
  let b := x (q p)
  have sub : p++[b]∈N := by cases e : b <;> simp [e,(hs.2.2.2 p pj).1,(hs.2.2.2 p pj).2]
  have ext : ok (p++[b]) := by
    intro i
    by_cases h : i.val<p.length
    · have z := op ⟨i.val,h⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left h,List.take_append_of_le_length (Nat.le_of_lt h)] using z
    · have z : i.val=p.length := by have := i.isLt; simp at this; omega
      simp [List.get_eq_getElem,z,List.getElem_append_right (by omega : p.length ≤ i.val),b]
  have le := mx _ (Finset.mem_filter.mpr ⟨sub,ext⟩)
  simp at le

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

theorem resolve_sound {V : Type} [DecidableEq V] {C D R : Clause V} (rule : IsResolvent C D R) (x : V → Bool)
    (c : ClauseSat x C) (d : ClauseSat x D) : ClauseSat x R := by
  classical
  obtain ⟨v,hpos,hneg,rfl⟩ := rule
  obtain ⟨p,hp,xp⟩ := c
  obtain ⟨q,hq,xq⟩ := d
  by_cases eq : p=(v,true)
  · subst p
    have neq : q≠(v,false) := by rintro rfl; simp_all
    exact ⟨q,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨neq,hq⟩),xq⟩
  · exact ⟨p,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hp⟩),xp⟩

theorem raw_leaf {V : Type} [DecidableEq V] (N J : Finset (List Bool)) (hs : shape N J)
    (line : List Bool→Clause V) (root : line []=∅) (res : ∀ p∈J, IsResolvent (line (p++[false])) (line (p++[true])) (line p))
    (x : V→Bool) : ∃ p∈N\J,¬ClauseSat x (line p) := by
  classical
  let bad := N.filter (fun p=>¬ClauseSat x (line p))
  have start : []∈bad := Finset.mem_filter.mpr ⟨hs.1,by simp [root,ClauseSat]⟩
  obtain ⟨p,hp,mx⟩ := Finset.exists_max_image bad List.length ⟨_,start⟩
  obtain ⟨pn,fail⟩ := Finset.mem_filter.mp hp
  refine ⟨p,Finset.mem_sdiff.mpr ⟨pn,?_⟩,fail⟩
  intro pj
  have ext (b : Bool) (hn : p++[b]∈N) : ClauseSat x (line (p++[b])) := by
    by_contra no
    have bound := mx _ (Finset.mem_filter.mpr ⟨hn,no⟩)
    simp at bound
  exact fail (resolve_sound (res p pj) x (ext false (hs.2.2.2 p pj).1) (ext true (hs.2.2.2 p pj).2))

theorem exponents {n : ℕ} (w : Fin n→ℕ) (hw : ∀ i,0<w i) (l : List (Fin n)) (nd : l.Nodup) :
    (l.map w).sum-l.length=l.toFinset.sum (fun v=>w v-1) := by
  induction l with
  | nil => simp
  | cons i es ih =>
    obtain ⟨no,tail⟩ := List.nodup_cons.mp nd
    have prev := ih tail
    have lower (v : List (Fin n)) : v.length ≤ (v.map w).sum := by
      induction v with
      | nil => simp
      | cons a t it => simp only [List.length_cons,List.map_cons,List.sum_cons]; have := hw a; omega
    have b := lower es
    have pos := hw i
    simp only [List.map_cons,List.sum_cons,List.length_cons,List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using no)]
    omega

def expFee {n : ℕ} (w : Fin n→ℕ) (q : List Bool→Fin n) (p : List Bool) :=
  2^(((trace q p).map w).sum-p.length)

theorem path_fee {n : ℕ} (w : Fin n→ℕ) (hw : ∀i,0<w i) (q : List Bool→Fin n) (p : List Bool)
    (C : B n) (nd : (trace q p).Nodup)
    (lit : ∀ l∈C,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2) :
    fee w C ≤ expFee w q p ∧ ((fee w C=expFee w q p) ↔
      ∀ v∈trace q p,1<w v → v∈vars C) := by
  classical
  let path := (trace q p).toFinset
  have sub : vars C⊆path := by
    intro i hi
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,_⟩ := lit l hl
    exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨j,hj⟩)
  let extra := path\vars C
  let f := fun v=>w v-1
  have add : extra.sum f+(vars C).sum f=path.sum f := Finset.sum_sdiff sub
  have plen : (trace q p).length=p.length := by simp [trace]
  have expo := exponents w hw (trace q p) nd
  rw [plen] at expo
  change ((trace q p).map w).sum-p.length=path.sum f at expo
  change 2^((vars C).sum f) ≤ 2^(((trace q p).map w).sum-p.length) ∧ _
  rw [expo]
  constructor
  · apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    omega
  · change 2^((vars C).sum f)=2^(((trace q p).map w).sum-p.length) ↔ _
    rw [expo,Nat.pow_right_inj (by decide : 1<(2:ℕ))]
    constructor
    · intro eq v hv wide
      by_contra no
      have h : v∈extra := Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hv,no⟩
      have z := Finset.single_le_sum (f:=f) (fun v _=>Nat.zero_le (f v)) h
      change f v ≤ extra.sum f at z
      have pos : 0<f v := by dsimp [f]; omega
      omega
    · intro no
      have zero : extra.sum f=0 := Finset.sum_eq_zero (by
        intro i hi
        obtain ⟨hv,nv⟩ := Finset.mem_sdiff.mp hi
        have dis := no i (List.mem_toFinset.mp hv)
        change w i-1=0
        by_contra! big
        exact nv (dis (by omega)))
      omega


theorem forced_bijection {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : Finset β) (f : α→β) (fee : β→ℕ) (weight : α→ℕ)
    (into : ∀ p∈S,f p∈F) (onto : ∀ C∈F,∃ p∈S,f p=C)
    (costPos : ∀ C∈F,0<fee C) (low : ∀ p∈S,fee (f p) ≤ weight p) (cap : S.sum weight ≤ F.sum fee) :
    Set.BijOn f (S:Set α) (F:Set β) ∧ ∀ p∈S,fee (f p)=weight p := by
  classical
  let pick := fun C : ↥F=>(onto C.val C.property).choose
  have pS (C : ↥F) : pick C∈S := (onto C.val C.property).choose_spec.1
  have key (C : ↥F) : f (pick C)=C.val := (onto C.val C.property).choose_spec.2
  have inj : Function.Injective pick := fun a b h=>Subtype.ext ((key a).symm.trans ((congrArg f h).trans (key b)))
  let Z := Finset.univ.image pick
  have sub : Z⊆S := by rintro x hx; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact pS i
  let h := fun x=>fee (f x)
  have mass : Z.sum h=F.sum fee := by
    unfold Z
    rw [Finset.sum_image (fun _ _ _ _ eq=>inj eq)]
    simp only [h,key]
    exact Finset.sum_attach _ _
  have rest : (S\Z).sum h+Z.sum h=S.sum h := Finset.sum_sdiff sub
  have upper : S.sum h ≤ S.sum weight := Finset.sum_le_sum low
  have same : S=Z := by
    apply Finset.Subset.antisymm _ sub
    intro x hx
    by_contra no
    have xp : x∈S\Z := Finset.mem_sdiff.mpr ⟨hx,no⟩
    have t := Finset.single_le_sum (f:=h) (fun _ _=>Nat.zero_le _) xp
    change h x ≤ (S\Z).sum h at t
    have hp : 0<h x := costPos _ (into x hx)
    omega
  refine ⟨⟨fun x hx=>into x hx,?_,fun y hy=>onto y hy⟩,?_⟩
  · intro p hp q hq eq
    rw [same] at hp hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    rw [key,key] at eq
    exact congrArg pick (Subtype.ext eq)
  · intro p hp
    by_contra ne
    have lt := Finset.sum_lt_sum low ⟨p,hp,lt_of_le_of_ne (low p hp) ne⟩
    change S.sum h < S.sum weight at lt
    omega

theorem all_queries {n : ℕ} (F : Finset (B n)) (bad : ¬Satisfiable (F : Set (B n)))
    (minF : ∀ C∈F,Satisfiable (F.erase C : Set (B n))) (M J : Finset (List Bool)) (sh : shape M J)
    (q : List Bool→Fin n) (cert : List Bool→B n) (into : ∀ p∈M\J,cert p∈F)
    (evidence : ∀ p∈M\J,∀ l∈cert p,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2) :
    ∀ C∈F,∃ p∈M\J,cert p=C := by
  classical
  intro C hC
  obtain ⟨x,_,oth⟩ := private_base F bad minF C hC
  obtain ⟨p,hp,agree⟩ := query_leaf M J sh q x
  refine ⟨p,hp,?_⟩
  by_contra ne
  obtain ⟨l,hl,yes⟩ := oth (cert p) (into p hp) ne
  obtain ⟨j,hj,wrong⟩ := evidence p hp l hl
  exact wrong ((agree j).trans ((congrArg x hj).trans yes))

theorem label_cover {n : ℕ} (w : Fin n→ℕ) (hw : ∀i,0<w i) (F : Finset (B n))
    (bad : ¬Satisfiable (F : Set (B n))) (minF : ∀ C∈F,Satisfiable (F.erase C : Set (B n)))
    (N J : Finset (List Bool)) (sh : shape N J) (line : List Bool→Clause (Raw w))
    (root : line []=∅) (used : ∀p∈N\J,liftAx (w:=w) (F:Set (B n)) (line p))
    (res : ∀p∈J,IsResolvent (line (p++[false])) (line (p++[true])) (line p)) :
    ∃ assign : ↥(N\J) → Label w F, Function.Surjective assign ∧
       (∀ p,labelAx (assign p)=line p.val) ∧ Function.Injective (labelAx (w:=w) (F:=F)) := by
  classical
  let assign := fun p : ↥(N\J) => ((labeled _).mp (used p.val p.property)).choose
  have eq (p : ↥(N\J)) : labelAx (assign p)=line p.val := ((labeled _).mp (used p.val p.property)).choose_spec
  have inj : Function.Injective (labelAx (w:=w) (F:=F)) := by
    intro p q same
    obtain ⟨x,fails,private0⟩ := private_raw w hw F bad minF p
    exact private0 q (same ▸ fails)
  refine ⟨assign,?_,eq,inj⟩
  intro q
  obtain ⟨x,_,only⟩ := private_raw w hw F bad minF q
  obtain ⟨p,h,invalid⟩ := raw_leaf N J sh line root res x
  exact ⟨⟨p,h⟩,(only _ (eq ⟨p,h⟩ ▸ invalid)).symm⟩

theorem size_inj {α β : Type*} [Fintype α] [Fintype β] (f : α→β) (sur : Function.Surjective f)
    (le : Fintype.card α ≤ Fintype.card β) : Function.Injective f := by
  classical
  let pick := Function.surjInv sur
  have right : Function.RightInverse pick f := Function.rightInverse_surjInv sur
  have eq := Fintype.card_le_of_surjective f sur
  have card := le.antisymm eq
  have b : Function.Bijective pick := (Fintype.bijective_iff_injective_and_card pick).mpr ⟨right.injective,card.symm⟩
  intro i j h
  obtain ⟨x,rfl⟩ := b.2 i
  obtain ⟨y,rfl⟩ := b.2 j
  exact congrArg pick ((right x).symm.trans (h.trans (right y)))



end PEqualNP.Outside.L_pcx_330_aux

open PEqualNP.Outside.L_pcx_330_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_330 : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
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
  let trace := fun (ask : List Bool → Option (Fin n)) (p : List Bool) =>
    List.ofFn (fun j : Fin p.length => ask (p.take j.val))
  ∀ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
    (¬ PEqualNP.ProofComplexity.Satisfiable (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) →
    (∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (↑(F.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) →
      Iff (∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
        shape N J ∧ line [] = ∅ ∧ Set.InjOn line ((↑(N \ J)) : Set (List Bool)) ∧
        (∀ p ∈ N \ J, liftAx (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (line p)) ∧
        ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p))
      (∃ (M D : Finset (List Bool)) (ask : List Bool → Option (Fin n))
         (cert : List Bool → PEqualNP.ProofComplexity.Clause (Fin n)),
        shape M D ∧ (∀ p ∈ D, (ask p).isSome = true) ∧ (∀ p ∈ M, (trace ask p).Nodup) ∧
        Set.BijOn cert ((↑(M \ D)) : Set (List Bool)) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
        ∀ p ∈ M \ D,
          (∀ lit ∈ cert p, ∃ j : Fin p.length, ask (p.take j.val) = some lit.1 ∧ p.get j ≠ lit.2) ∧
          ∀ v : Fin n, some v ∈ trace ask p → 1 < w v → v ∈ (cert p).image Prod.fst) := by
  classical
  intro n w hw Raw0 parity0 lift shape0 trace0 F bad minF
  by_cases hn : 0<n
  · have cleanF (C : B n) (hC : C∈F) : clean C := by
      obtain ⟨x,miss,_⟩ := private_base F bad minF C hC
      exact clean_private C x miss
    let K := F.sum (fee w)
    have count : Fintype.card (Label w F)=K := numLabels w hw F cleanF
    constructor
    · rintro ⟨N,J,line,sh,root,inj,used,res⟩
      obtain ⟨tag,_,eq,_⟩ := label_cover w hw F bad minF N J sh line root used res
      have it : Function.Injective tag := by
        intro p q h
        apply Subtype.ext
        exact inj p.property q.property ((eq p).symm.trans ((congrArg labelAx h).trans (eq q)))
      have lk : (N\J).card ≤ K := by simpa only [Fintype.card_coe,count] using Fintype.card_le_of_injective tag it
      let H := N.sum List.length
      have hb (p : List Bool) (hp : p∈N) : p.length ≤ H :=
        Finset.single_le_sum (f:=List.length) (fun i _=>Nat.zero_le _) hp
      obtain ⟨M,D,q,sM,walk,leaf,tot⟩ := (general305 n hn w hw (F:Set (B n)) H K).mp
        ⟨N,J,line,sh,root,hb,lk,used,res⟩
      let S := M\D
      let cert : List Bool→B n := fun p=>if h : p∈S then (leaf p h).choose else ∅
      have cf (p : List Bool) (hp : p∈S) : cert p∈F ∧
          ∀ l∈cert p,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2 := by
        dsimp only [cert]
        rw [dif_pos hp]
        exact ⟨(leaf p hp).choose_spec.1,(leaf p hp).choose_spec.2⟩
      have path (p : List Bool) (hp : p∈S) := path_fee w hw q p (cert p) (walk p (Finset.mem_sdiff.mp hp).1).1 (cf p hp).2
      have sur := all_queries F bad minF M D sM q cert (fun p h=>(cf p h).1) (fun p h=>(cf p h).2)
      obtain ⟨bij,price⟩ := forced_bijection S F cert (fee w) (expFee w q) (fun p h=>(cf p h).1) sur
        (fun C _=>by dsimp only [fee]; positivity) (fun p h=>(path p h).1) tot
      let ask := fun p=>some (q p)
      have tr (p : List Bool) : trace ask p=(trace q p).map some := by
        unfold trace; rw [List.map_ofFn]; rfl
      refine ⟨M,D,ask,cert,sM,by simp [ask],?_,bij,?_⟩
      · intro p hp
        change (trace ask p).Nodup
        rw [tr]
        exact (walk p hp).1.map (fun _ _ e=>Option.some.inj e)
      · intro p hp
        constructor
        · intro l hl
          obtain ⟨j,e,v⟩ := (cf p hp).2 l hl
          exact ⟨j,congrArg some e,v⟩
        · intro v hv wide
          change some v∈trace ask p at hv
          rw [tr] at hv
          exact (path p hp).2.mp (price p hp) v (by simpa using hv) wide
    · rintro ⟨M,D,ask,cert,sh,asks,nd,bij,ends⟩
      let q := fun p=>(ask p).getD ⟨0,hn⟩
      have aeq (p : List Bool) (hp : p∈D) : ask p=some (q p) := by
        have present := asks p hp
        cases e : ask p <;> simp_all only [q,e,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,Option.getD_some]
      have tr (p : List Bool) (hp : p∈M) := someTrace q ask M D sh aeq p hp
      have nodup (p : List Bool) (hp : p∈M) : (trace q p).Nodup := by
        have d := nd p hp
        change (trace ask p).Nodup at d
        rw [tr p hp] at d
        exact d.of_map _
      have certifies (p : List Bool) (hp : p∈M\D) :
          ∀ l∈cert p,∃ j : Fin p.length,q (p.take j.val)=l.1 ∧ p.get j≠l.2 := by
        intro l hl
        obtain ⟨j,eq,ne⟩ := (ends p hp).1 l hl
        exact ⟨j,by simp [q,eq],ne⟩
      have price (p : List Bool) (hp : p∈M\D) : expFee w q p=fee w (cert p) := by
        apply Eq.symm
        apply (path_fee w hw q p _ (nodup p (Finset.mem_sdiff.mp hp).1) (certifies p hp)).2.mpr
        intro v h wide
        apply (ends p hp).2 v _ wide
        change some v∈trace ask p
        rw [tr p (Finset.mem_sdiff.mp hp).1]
        exact List.mem_map.mpr ⟨v,h,rfl⟩
      have feq : (M\D).image cert=F := by
        ext C
        simp only [Finset.mem_image]
        exact ⟨fun ⟨p,hp,ep⟩=>ep ▸ bij.1 hp,fun h=>bij.2.2 h⟩
      have upper : (M\D).sum (expFee w q) ≤ K := by
        rw [Finset.sum_congr rfl price]
        change _ ≤ F.sum (fee w)
        rw [← feq,Finset.sum_image (fun i hi j hj e=>bij.2.1 hi hj e)]
      let H := M.sum (fun p=>((trace q p).map w).sum)
      have lim (p : List Bool) (hp : p∈M) : ((trace q p).map w).sum ≤ H :=
        Finset.single_le_sum (f:=fun p=>((trace q p).map w).sum) (fun _ _=>Nat.zero_le _) hp
      obtain ⟨N,J,line,sN,root,_,lk,used,res⟩ := (general305 n hn w hw (F:Set (B n)) H K).mpr
        ⟨M,D,q,sh,fun p hp=>⟨nodup p hp,lim p hp⟩,
          fun p hp=>⟨cert p,bij.1 hp,certifies p hp⟩,upper⟩
      obtain ⟨tag,onto,eq,inj⟩ := label_cover w hw F bad minF N J sN line root used res
      have ti := size_inj tag onto (by simpa only [Fintype.card_coe,count] using lk)
      refine ⟨N,J,line,sN,root,?_,used,res⟩
      intro p hp q hq h
      exact congrArg Subtype.val (ti (inj ((eq ⟨p,hp⟩).trans (h.trans (eq ⟨q,hq⟩).symm))))
  · have ez : n=0 := by omega
    have ce (C : B n) : C=∅ := Finset.eq_empty_of_forall_notMem (fun l _=>by have lt := l.1.isLt; omega)
    have non : F.Nonempty := by
      by_contra no
      have ff := Finset.not_nonempty_iff_eq_empty.mp no
      exact bad ⟨fun _=>false,by simp [ff,Satisfies]⟩
    have emp : (∅ : B n)∈F := by obtain ⟨C,h⟩ := non; simpa [ce C] using h
    have singleton : F={∅} := by ext C; simp [ce C,emp]
    constructor
    · intro _
      refine ⟨{[]},∅,fun _=>none,fun _=>∅,shape_leaf,by simp,?_,?_,?_⟩
      · intro p h; simp only [Finset.mem_singleton] at h; subst p; simp [trace0]
      · rw [singleton]
        exact ⟨by simp [Set.MapsTo],by simp [Set.InjOn],by simp [Set.SurjOn]⟩
      · intro p h; simp only [Finset.sdiff_empty,Finset.mem_singleton] at h; subst p
        simp [trace0]
    · intro _
      refine ⟨{[]},∅,fun _=>∅,shape_leaf,rfl,by simp [Set.InjOn],?_,by simp⟩
      intro p _
      refine ⟨∅,emp,fun _=>false,by simp,?_⟩
      simp



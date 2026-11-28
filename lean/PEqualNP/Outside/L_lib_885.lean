import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_lib_885

def k (N : Nat) : Nat := 8 * N + 1

def name (N : Nat) (i : Fin N) (s : Fin 8) : Fin (k N) :=
  Fin.ofNat (8 * N + 1) (8 * i.val + s.val)

def leaf (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) : Fin (k N) :=
  name N i (Fin.ofNat 8 (2 + 2 * c.val + b.toNat))

def flag (N : Nat) (i : Fin N) (c : Fin 3) : Finset (Fin (k N)) :=
  {leaf N i c false, leaf N i c true}

def orient (N : Nat) (i : Fin N) : Finset (Fin (k N)) :=
  insert (name N i 0) (Finset.univ.image (fun c : Fin 3 => leaf N i c false))

def triangle (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) : Finset (Fin (k N)) :=
  insert (name N i (if b then 1 else 0)) (flag N i c)

def nextIdx (N : Nat) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def pad (N : Nat) (i : Fin N) (j : Fin 4) : Fin (k N) :=
  name N (nextIdx N i) (Fin.ofNat 8 j.val)

def padded (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) : Finset (Fin (k N)) :=
  insert (pad N i j) (triangle N i c b)

def spare (N : Nat) : Fin (k N) :=
  ⟨8 * N, by unfold k; omega⟩

def hits {N : Nat} (P : Equiv.Perm (Fin (k N))) (S : Finset (Fin (k N))) : Prop :=
  ∃ u ∈ S, P u ∈ S ∧ P u ≠ u

lemma name_val (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val = 8 * i.val + s.val := by
  change (8 * i.val + s.val) % (8 * N + 1) = 8 * i.val + s.val
  exact Nat.mod_eq_of_lt (by omega)

lemma name_inj {N : Nat} {i i' : Fin N} {s s' : Fin 8} :
    name N i s = name N i' s' ↔ i = i' ∧ s = s' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [name_val, name_val] at hv
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma name_div (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val / 8 = i.val := by
  rw [name_val]
  omega

lemma name_mod (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val % 8 = s.val := by
  rw [name_val]
  omega

lemma name_ne_spare (N : Nat) (i : Fin N) (s : Fin 8) :
    name N i s ≠ spare N := by
  intro h
  have hv := congrArg Fin.val h
  rw [name_val] at hv
  simp only [spare] at hv
  omega

lemma eq_name_or_spare (N : Nat) (u : Fin (k N)) :
    (∃ i s, u = name N i s) ∨ u = spare N := by
  by_cases hu : u.val < 8 * N
  · left
    refine ⟨⟨u.val / 8, by omega⟩, ⟨u.val % 8, by omega⟩, Fin.ext ?_⟩
    rw [name_val]
    dsimp only
    omega
  · right
    apply Fin.ext
    have hlt := u.isLt
    unfold k at hlt
    simp only [spare]
    omega

lemma nextIdx_ne {N : Nat} (hN : 2 ≤ N) (i : Fin N) :
    nextIdx N i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nextIdx] at hv
  by_cases h1 : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have h2 : i.val + 1 = N := by omega
    rw [h2, Nat.mod_self] at hv
    omega

lemma leaf_val (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val = 8 * i.val + (2 + 2 * c.val + b.toNat) := by
  unfold leaf
  rw [name_val]
  have hmod : (Fin.ofNat 8 (2 + 2 * c.val + b.toNat)).val = 2 + 2 * c.val + b.toNat := by
    change (2 + 2 * c.val + b.toNat) % 8 = 2 + 2 * c.val + b.toNat
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]

lemma leaf_div (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val / 8 = i.val := by
  rw [leaf_val]
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma leaf_mod (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val % 8 = 2 + 2 * c.val + b.toNat := by
  rw [leaf_val]
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma leaf_inj {N : Nat} {i i' : Fin N} {c c' : Fin 3} {b b' : Bool} :
    leaf N i c b = leaf N i' c' b' ↔ i = i' ∧ c = c' ∧ b = b' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [leaf_val, leaf_val] at hv
    cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv
    · exact ⟨Fin.ext (by omega), Fin.ext (by omega), rfl⟩
    · omega
    · omega
    · exact ⟨Fin.ext (by omega), Fin.ext (by omega), rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

lemma leaf_ne_hub0 (N : Nat) (i i' : Fin N) (c : Fin 3) (b : Bool) :
    leaf N i c b ≠ name N i' 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [leaf_val, name_val] at hv
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Fin.val_zero] at hv <;> omega

lemma leaf_ne_hub1 (N : Nat) (i i' : Fin N) (c : Fin 3) (b : Bool) :
    leaf N i c b ≠ name N i' 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [leaf_val, name_val] at hv
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Fin.val_one] at hv <;> omega

lemma hub0_ne_hub1 (N : Nat) (i i' : Fin N) :
    name N i 0 ≠ name N i' 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [name_val, name_val] at hv
  simp only [Fin.val_zero, Fin.val_one] at hv
  omega

lemma pad_val (N : Nat) (i : Fin N) (j : Fin 4) :
    (pad N i j).val = 8 * (nextIdx N i).val + j.val := by
  unfold pad
  rw [name_val]
  have hmod : (Fin.ofNat 8 j.val).val = j.val := by
    change j.val % 8 = j.val
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]

lemma pad_div (N : Nat) (i : Fin N) (j : Fin 4) :
    (pad N i j).val / 8 = (nextIdx N i).val := by
  rw [pad_val]
  omega

lemma pad_inj {N : Nat} {i : Fin N} {j j' : Fin 4} :
    pad N i j = pad N i j' ↔ j = j' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [pad_val, pad_val] at hv
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

lemma flag_card (N : Nat) (i : Fin N) (c : Fin 3) :
    (flag N i c).card = 2 := by
  unfold flag
  rw [Finset.card_pair]
  intro h
  have := (leaf_inj.mp h).2.2
  cases this

lemma triangle_card (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (triangle N i c b).card = 3 := by
  unfold triangle
  rw [Finset.card_insert_of_notMem, flag_card]
  intro hm
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hm
  cases b
  · rcases hm with h | h
    · exact leaf_ne_hub0 N i i c false h.symm
    · exact leaf_ne_hub0 N i i c true h.symm
  · rcases hm with h | h
    · exact leaf_ne_hub1 N i i c false h.symm
    · exact leaf_ne_hub1 N i i c true h.symm

lemma orient_card (N : Nat) (i : Fin N) :
    (orient N i).card = 4 := by
  unfold orient
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective]
    · simp
    · intro c1 c2 h
      exact (leaf_inj.mp h).2.1
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨c, _, hc⟩
    exact leaf_ne_hub0 N i i c false hc

lemma pad_notMem_triangle {N : Nat} (hN : 2 ≤ N) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    pad N i j ∉ triangle N i c b := by
  intro hm
  have hne : nextIdx N i ≠ i := nextIdx_ne hN i
  simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, name_div] at this
    exact hne (Fin.ext this)
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, leaf_div] at this
    exact hne (Fin.ext this)
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, leaf_div] at this
    exact hne (Fin.ext this)

lemma padded_card {N : Nat} (hN : 2 ≤ N) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    (padded N i c b j).card = 4 := by
  unfold padded
  rw [Finset.card_insert_of_notMem (pad_notMem_triangle hN i c b j), triangle_card]

lemma flag_disjoint {N : Nat} {i1 i2 : Fin N} (h : i1 ≠ i2) (c1 c2 : Fin 3) :
    Disjoint (flag N i1 c1) (flag N i2 c2) := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
  rcases hu1 with rfl | rfl <;> rcases hu2 with h2 | h2
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1

lemma forb_card {N : Nat} {i1 i2 : Fin N} (h : i1 ≠ i2) (c1 c2 : Fin 3) :
    (flag N i1 c1 ∪ flag N i2 c2).card = 4 := by
  rw [Finset.card_union_of_disjoint (flag_disjoint h c1 c2), flag_card, flag_card]

def blockFilter (N : Nat) (S : Finset (Fin (k N))) (r : Fin N) : Finset (Fin (k N)) :=
  S.filter (fun u => u.val / 8 = r.val)

lemma blockFilter_orient (N : Nat) (i r : Fin N) :
    (blockFilter N (orient N i) r).card = if r = i then 4 else 0 := by
  unfold blockFilter
  by_cases h : r = i
  · subst h
    have heq : (orient N r).filter (fun u => u.val / 8 = r.val) = orient N r := by
      rw [Finset.filter_eq_self]
      intro u hu
      simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu
      rcases hu with rfl | ⟨c, rfl⟩
      · exact name_div N r 0
      · exact leaf_div N r c false
    rw [if_pos rfl, heq, orient_card]
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu
    simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu
    rcases hu with rfl | ⟨c, rfl⟩
    · rw [name_div]; intro heq; exact h (Fin.ext heq.symm)
    · rw [leaf_div]; intro heq; exact h (Fin.ext heq.symm)

lemma blockFilter_padded {N : Nat} (hN : 2 ≤ N) (i r : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    (blockFilter N (padded N i c b j) r).card =
      if r = i then 3 else if r = nextIdx N i then 1 else 0 := by
  unfold blockFilter
  have hne : nextIdx N i ≠ i := nextIdx_ne hN i
  by_cases h1 : r = i
  · subst h1
    have heq : (padded N r c b j).filter (fun u => u.val / 8 = r.val) = triangle N r c b := by
      ext u
      simp only [padded, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | ht, hdiv⟩
        · rw [pad_div] at hdiv
          exact absurd (Fin.ext hdiv) hne
        · exact ht
      · intro ht
        refine ⟨Or.inr ht, ?_⟩
        simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact name_div N r _
        · exact leaf_div N r c false
        · exact leaf_div N r c true
    rw [if_pos rfl, heq, triangle_card]
  · rw [if_neg h1]
    by_cases h2 : r = nextIdx N i
    · subst h2
      have heq : (padded N i c b j).filter (fun u => u.val / 8 = (nextIdx N i).val) = {pad N i j} := by
        ext u
        simp only [padded, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | ht, hdiv⟩
          · rfl
          · simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · rw [name_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
            · rw [leaf_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
            · rw [leaf_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
        · rintro rfl
          exact ⟨Or.inl rfl, pad_div N i j⟩
      rw [if_pos rfl, heq, Finset.card_singleton]
    · rw [if_neg h2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu
      simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · rw [pad_div]; intro heq; exact h2 (Fin.ext heq.symm)
      · rw [name_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)

lemma blockFilter_forb {N : Nat} {i1 i2 : Fin N} (h12 : i1 ≠ i2) (c1 c2 : Fin 3) (r : Fin N) :
    (blockFilter N (flag N i1 c1 ∪ flag N i2 c2) r).card =
      if r = i1 then 2 else if r = i2 then 2 else 0 := by
  unfold blockFilter
  by_cases h1 : r = i1
  · subst h1
    have heq : (flag N r c1 ∪ flag N i2 c2).filter (fun u => u.val / 8 = r.val) = flag N r c1 := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hu | hu, hdiv⟩
        · exact hu
        · simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> rw [leaf_div] at hdiv <;> exact absurd (Fin.ext hdiv.symm) h12
      · intro hu
        refine ⟨Or.inl hu, ?_⟩
        simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> exact leaf_div N r c1 _
    rw [if_pos rfl, heq, flag_card]
  · rw [if_neg h1]
    by_cases h2 : r = i2
    · subst h2
      have heq : (flag N i1 c1 ∪ flag N r c2).filter (fun u => u.val / 8 = r.val) = flag N r c2 := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hu | hu, hdiv⟩
          · simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> rw [leaf_div] at hdiv <;> exact absurd (Fin.ext hdiv) h12
          · exact hu
        · intro hu
          refine ⟨Or.inr hu, ?_⟩
          simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> exact leaf_div N r c2 _
      rw [if_pos rfl, heq, flag_card]
    · rw [if_neg h2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu
      simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with (rfl | rfl) | (rfl | rfl)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h2 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h2 (Fin.ext heq.symm)

lemma orient_inj {N : Nat} {i i' : Fin N} (h : orient N i = orient N i') : i = i' := by
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_orient, if_pos rfl] at hc
  by_contra hne
  rw [if_neg hne] at hc
  omega

lemma padded_inj {N : Nat} (hN : 2 ≤ N) {i i' : Fin N} {c c' : Fin 3} {b b' : Bool} {j j' : Fin 4}
    (h : padded N i c b j = padded N i' c' b' j') :
    i = i' ∧ c = c' ∧ b = b' ∧ j = j' := by
  have hi : i = i' := by
    have hc := congrArg (fun S => (blockFilter N S i).card) h
    rw [blockFilter_padded hN, blockFilter_padded hN, if_pos rfl] at hc
    by_contra hne
    rw [if_neg hne] at hc
    split_ifs at hc <;> omega
  subst hi
  have hj : j = j' := by
    have hmem : pad N i j ∈ padded N i c' b' j' := by
      rw [← h]
      exact Finset.mem_insert_self _ _
    simp only [padded, Finset.mem_insert] at hmem
    rcases hmem with hpad | htri
    · exact pad_inj.mp hpad
    · exact absurd htri (pad_notMem_triangle hN i c' b' j)
  subst hj
  have hb : b = b' := by
    have hmem : name N i (if b then 1 else 0) ∈ padded N i c' b' j := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · have := congrArg (fun u : Fin (k N) => u.val / 8) h1
      rw [name_div, pad_div] at this
      exact absurd (Fin.ext this.symm) (nextIdx_ne hN i)
    · cases b <;> cases b'
      · rfl
      · exact absurd h2 (hub0_ne_hub1 N i i)
      · exact absurd h2.symm (hub0_ne_hub1 N i i)
      · rfl
    · cases b
      · exact absurd h3.symm (leaf_ne_hub0 N i i c' false)
      · exact absurd h3.symm (leaf_ne_hub1 N i i c' false)
    · cases b
      · exact absurd h4.symm (leaf_ne_hub0 N i i c' true)
      · exact absurd h4.symm (leaf_ne_hub1 N i i c' true)
  subst hb
  have hc : c = c' := by
    have hmem : leaf N i c false ∈ padded N i c' b j := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · have := congrArg (fun u : Fin (k N) => u.val / 8) h1
      rw [leaf_div, pad_div] at this
      exact absurd (Fin.ext this.symm) (nextIdx_ne hN i)
    · cases b
      · exact absurd h2 (leaf_ne_hub0 N i i c false)
      · exact absurd h2 (leaf_ne_hub1 N i i c false)
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h4).2.1
  exact ⟨rfl, hc, rfl, rfl⟩

lemma forb_inj {N : Nat} {e1 e2 : (Fin N × Fin 3) × (Fin N × Fin 3)}
    (he1 : e1.1.1 < e1.2.1) (he2 : e2.1.1 < e2.2.1)
    (h : flag N e1.1.1 e1.1.2 ∪ flag N e1.2.1 e1.2.2 =
         flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2) :
    e1 = e2 := by
  have h12 : e1.1.1 ≠ e1.2.1 := ne_of_lt he1
  have h22 : e2.1.1 ≠ e2.2.1 := ne_of_lt he2
  have hmem1 : e1.1.1 = e2.1.1 ∨ e1.1.1 = e2.2.1 := by
    by_cases ha : e1.1.1 = e2.1.1
    · exact Or.inl ha
    · by_cases hb : e1.1.1 = e2.2.1
      · exact Or.inr hb
      · exfalso
        have hc := congrArg (fun S => (blockFilter N S e1.1.1).card) h
        rw [blockFilter_forb h12, blockFilter_forb h22] at hc
        simp [ha, hb] at hc
  have hmem2 : e1.2.1 = e2.1.1 ∨ e1.2.1 = e2.2.1 := by
    by_cases ha : e1.2.1 = e2.1.1
    · exact Or.inl ha
    · by_cases hb : e1.2.1 = e2.2.1
      · exact Or.inr hb
      · exfalso
        have hc := congrArg (fun S => (blockFilter N S e1.2.1).card) h
        rw [blockFilter_forb h12, blockFilter_forb h22] at hc
        simp [h12.symm, ha, hb] at hc
  have hi1 : e1.1.1 = e2.1.1 := by
    rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2
    · exact h1
    · exact h1
    · exfalso
      have : e1.1.1 < e1.2.1 := he1
      rw [h1, h2] at this
      exact absurd (lt_trans this he2) (lt_irrefl _)
    · exfalso; exact h12 (h1.trans h2.symm)
  have hi2 : e1.2.1 = e2.2.1 := by
    rcases hmem2 with h2 | h2
    · exfalso; exact h12 (hi1.trans h2.symm)
    · exact h2
  have hc1 : e1.1.2 = e2.1.2 := by
    have hm : leaf N e1.1.1 e1.1.2 false ∈ flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2 := by
      rw [← h]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (h3 | h3) | (h3 | h3)
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h3).2.1
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi1) h22.symm
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi1) h22.symm
  have hc2 : e1.2.2 = e2.2.2 := by
    have hm : leaf N e1.2.1 e1.2.2 false ∈ flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2 := by
      rw [← h]
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (h3 | h3) | (h3 | h3)
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi2) h22
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi2) h22
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h3).2.1
  rcases e1 with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩
  rcases e2 with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩
  simp only at hi1 hi2 hc1 hc2
  subst hi1; subst hi2; subst hc1; subst hc2
  rfl

lemma orient_ne_padded {N : Nat} (hN : 2 ≤ N) (i i' : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    orient N i ≠ padded N i' c b j := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_padded hN, if_pos rfl] at hc
  split_ifs at hc <;> omega

lemma orient_ne_forb {N : Nat} {i1 i2 : Fin N} (h12 : i1 ≠ i2) (i : Fin N) (c1 c2 : Fin 3) :
    orient N i ≠ flag N i1 c1 ∪ flag N i2 c2 := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_forb h12, if_pos rfl] at hc
  split_ifs at hc <;> omega

lemma padded_ne_forb {N : Nat} (hN : 2 ≤ N) {i1 i2 : Fin N} (h12 : i1 ≠ i2)
    (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) (c1 c2 : Fin 3) :
    padded N i c b j ≠ flag N i1 c1 ∪ flag N i2 c2 := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_padded hN, blockFilter_forb h12, if_pos rfl] at hc
  split_ifs at hc <;> omega

def blockSwap (c : Fin 3) (s : Fin 8) : Fin 8 :=
  if s.val = 0 then Fin.ofNat 8 (2 + 2 * c.val)
  else if s.val = 1 then Fin.ofNat 8 (3 + 2 * c.val)
  else if s.val = 2 + 2 * c.val then 0
  else if s.val = 3 + 2 * c.val then 1
  else if s.val % 2 = 0 then Fin.ofNat 8 (s.val + 1)
  else Fin.ofNat 8 (s.val - 1)

lemma blockSwap_invol : ∀ (c : Fin 3) (s : Fin 8), blockSwap c (blockSwap c s) = s := by
  decide

lemma blockSwap_zero : ∀ c : Fin 3, blockSwap c 0 = Fin.ofNat 8 (2 + 2 * c.val) := by
  decide

lemma blockSwap_one : ∀ c : Fin 3, blockSwap c 1 = Fin.ofNat 8 (3 + 2 * c.val) := by
  decide

lemma blockSwap_leaf_eq :
    ∀ (c : Fin 3) (b : Bool),
      blockSwap c (Fin.ofNat 8 (2 + 2 * c.val + b.toNat)) = if b then 1 else 0 := by
  decide

lemma blockSwap_leaf_ne :
    ∀ (c c' : Fin 3) (b : Bool), c ≠ c' →
      blockSwap c (Fin.ofNat 8 (2 + 2 * c'.val + b.toNat)) =
        Fin.ofNat 8 (2 + 2 * c'.val + (!b).toNat) := by
  decide

lemma blockSwap_diff_card :
    ∀ (c1 c2 : Fin 3), c1 ≠ c2 →
      (Finset.univ.filter (fun s : Fin 8 => blockSwap c1 s ≠ blockSwap c2 s)).card = 6 := by
  decide

def permFun (N : Nat) (a : Fin N → Fin 3) (u : Fin (k N)) : Fin (k N) :=
  if hu : u.val < 8 * N then
    name N ⟨u.val / 8, by omega⟩ (blockSwap (a ⟨u.val / 8, by omega⟩) ⟨u.val % 8, by omega⟩)
  else
    u

lemma permFun_name (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (s : Fin 8) :
    permFun N a (name N i s) = name N i (blockSwap (a i) s) := by
  unfold permFun
  have hlt : (name N i s).val < 8 * N := by rw [name_val]; omega
  rw [dif_pos hlt]
  have hi : (⟨(name N i s).val / 8, by omega⟩ : Fin N) = i := Fin.ext (name_div N i s)
  have hs : (⟨(name N i s).val % 8, by omega⟩ : Fin 8) = s := Fin.ext (name_mod N i s)
  rw [hi, hs]

lemma permFun_spare (N : Nat) (a : Fin N → Fin 3) :
    permFun N a (spare N) = spare N := by
  unfold permFun
  have hnot : ¬ (spare N).val < 8 * N := by simp [spare]
  rw [dif_neg hnot]

lemma permFun_invol (N : Nat) (a : Fin N → Fin 3) :
    Function.Involutive (permFun N a) := by
  intro u
  rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
  · rw [permFun_name, permFun_name, blockSwap_invol]
  · rw [permFun_spare, permFun_spare]

def permOf (N : Nat) (a : Fin N → Fin 3) : Equiv.Perm (Fin (k N)) :=
  ⟨permFun N a, permFun N a, permFun_invol N a, permFun_invol N a⟩

lemma permOf_name (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (s : Fin 8) :
    permOf N a (name N i s) = name N i (blockSwap (a i) s) :=
  permFun_name N a i s

lemma permOf_spare (N : Nat) (a : Fin N → Fin 3) :
    permOf N a (spare N) = spare N :=
  permFun_spare N a

lemma permOf_invol (N : Nat) (a : Fin N → Fin 3) :
    Function.Involutive (permOf N a) :=
  permFun_invol N a

lemma permOf_leaf_eq (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (b : Bool) :
    permOf N a (leaf N i (a i) b) = name N i (if b then 1 else 0) := by
  unfold leaf
  rw [permOf_name, blockSwap_leaf_eq]

lemma permOf_leaf_ne (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) (b : Bool)
    (h : a i ≠ c) :
    permOf N a (leaf N i c b) = leaf N i c (!b) := by
  unfold leaf
  rw [permOf_name, blockSwap_leaf_ne (a i) c b h]

lemma permOf_hits_flag_iff (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) :
    (¬ hits (permOf N a) (flag N i c)) ↔ a i = c := by
  constructor
  · intro hnh
    by_contra hne
    apply hnh
    refine ⟨leaf N i c false, Finset.mem_insert_self _ _, ?_, ?_⟩
    · rw [permOf_leaf_ne N a i c false hne]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [permOf_leaf_ne N a i c false hne]
      intro h
      have := (leaf_inj.mp h).2.2
      cases this
  · intro heq
    subst heq
    rintro ⟨u, hu, hpu, _⟩
    simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu hpu
    rcases hu with rfl | rfl
    · rw [permOf_leaf_eq N a i false] at hpu
      simp only [Bool.false_eq_true, ite_false] at hpu
      rcases hpu with h | h
      · exact leaf_ne_hub0 N i i (a i) false h.symm
      · exact leaf_ne_hub0 N i i (a i) true h.symm
    · rw [permOf_leaf_eq N a i true] at hpu
      simp only [ite_true] at hpu
      rcases hpu with h | h
      · exact leaf_ne_hub1 N i i (a i) false h.symm
      · exact leaf_ne_hub1 N i i (a i) true h.symm

lemma permOf_hits_orient (N : Nat) (a : Fin N → Fin 3) (i : Fin N) :
    hits (permOf N a) (orient N i) := by
  refine ⟨name N i 0, Finset.mem_insert_self _ _, ?_, ?_⟩
  · rw [permOf_name, blockSwap_zero]
    have hlf : name N i (Fin.ofNat 8 (2 + 2 * (a i).val)) = leaf N i (a i) false := rfl
    rw [hlf]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩)
  · rw [permOf_name, blockSwap_zero]
    have hlf : name N i (Fin.ofNat 8 (2 + 2 * (a i).val)) = leaf N i (a i) false := rfl
    rw [hlf]
    exact leaf_ne_hub0 N i i (a i) false

lemma permOf_hits_triangle (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) (b : Bool) :
    hits (permOf N a) (triangle N i c b) := by
  by_cases hc : a i = c
  · subst hc
    refine ⟨leaf N i (a i) b, ?_, ?_, ?_⟩
    · cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [permOf_leaf_eq]
      exact Finset.mem_insert_self _ _
    · rw [permOf_leaf_eq]
      cases b
      · exact (leaf_ne_hub0 N i i (a i) false).symm
      · exact (leaf_ne_hub1 N i i (a i) true).symm
  · refine ⟨leaf N i c false, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_, ?_⟩
    · rw [permOf_leaf_ne N a i c false hc]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [permOf_leaf_ne N a i c false hc]
      intro h
      have := (leaf_inj.mp h).2.2
      cases this

lemma permOf_dist (N : Nat) (a b : Fin N → Fin 3) :
    (Finset.univ.filter (fun u : Fin (k N) => permOf N a u ≠ permOf N b u)).card =
      6 * (Finset.univ.filter (fun i : Fin N => a i ≠ b i)).card := by
  let D := Finset.univ.filter (fun i : Fin N => a i ≠ b i)
  let F : Fin N → Finset (Fin (k N)) := fun i =>
    (Finset.univ.filter (fun s : Fin 8 => blockSwap (a i) s ≠ blockSwap (b i) s)).image (name N i)
  have heq : Finset.univ.filter (fun u : Fin (k N) => permOf N a u ≠ permOf N b u) = D.biUnion F := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, D, F, Finset.mem_image]
    constructor
    · intro hne
      rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
      · rw [permOf_name, permOf_name] at hne
        have hsne : blockSwap (a i) s ≠ blockSwap (b i) s := fun h => hne (by rw [h])
        have hine : a i ≠ b i := fun h => hsne (by rw [h])
        exact ⟨i, hine, s, hsne, rfl⟩
      · rw [permOf_spare, permOf_spare] at hne
        exact absurd rfl hne
    · rintro ⟨i, _, s, hsne, rfl⟩
      rw [permOf_name, permOf_name]
      intro h
      exact hsne (name_inj.mp h).2
  rw [heq, Finset.card_biUnion]
  · have hcard : ∀ i ∈ D, (F i).card = 6 := by
      intro i hi
      have hine : a i ≠ b i := (Finset.mem_filter.mp hi).2
      dsimp only [F]
      rw [Finset.card_image_of_injective _ (fun s1 s2 h => (name_inj.mp h).2)]
      exact blockSwap_diff_card (a i) (b i) hine
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro i1 _ i2 _ hne
    show Disjoint (F i1) (F i2)
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rcases Finset.mem_image.mp hu1 with ⟨s1, _, rfl⟩
    rcases Finset.mem_image.mp hu2 with ⟨s2, _, h2⟩
    exact hne (name_inj.mp h2).1.symm

lemma hits_triangle_of_padded {N : Nat} (P : Equiv.Perm (Fin (k N)))
    (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (b : Bool)
    (hpad : ∀ j : Fin 4, hits P (padded N i c b j)) :
    hits P (triangle N i c b) := by
  by_contra hnt
  have hsub : Finset.univ.image (fun j : Fin 4 => P (pad N i j)) ⊆ triangle N i c b := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
    rcases hpad j with ⟨u, hu, hpu, hne⟩
    simp only [padded, Finset.mem_insert] at hu hpu
    rcases hu with rfl | hut
    · rcases hpu with hp | hpt
      · exact absurd hp hne
      · exact hpt
    · rcases hpu with hp | hpt
      · have hpu' : P (pad N i j) = u := by rw [← hp, hinv u]
        rw [hpu']
        exact hut
      · exact absurd ⟨u, hut, hpt, hne⟩ hnt
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin, triangle_card] at hle
  · omega
  · intro j1 j2 hj
    exact pad_inj.mp (P.injective hj)

lemma hits_flag_eq_swap {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (hh : hits P (flag N i c)) :
    P (leaf N i c false) = leaf N i c true ∧ P (leaf N i c true) = leaf N i c false := by
  rcases hh with ⟨u, hu, hpu, hne⟩
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl <;> rcases hpu with hp | hp
  · exact absurd hp hne
  · exact ⟨hp, by rw [← hp, hinv]⟩
  · exact ⟨by rw [← hp, hinv], hp⟩
  · exact absurd hp hne

lemma hub_maps_into_flag {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (b : Bool)
    (htri : hits P (triangle N i c b)) (hnh : ¬ hits P (flag N i c)) :
    P (name N i (if b then 1 else 0)) ∈ flag N i c := by
  rcases htri with ⟨u, hu, hpu, hne⟩
  simp only [triangle, Finset.mem_insert] at hu hpu
  rcases hu with rfl | huf
  · rcases hpu with hp | hpf
    · exact absurd hp hne
    · exact hpf
  · rcases hpu with hp | hpf
    · have : P (name N i (if b then 1 else 0)) = u := by rw [← hp, hinv]
      rw [this]
      exact huf
    · exact absurd ⟨u, huf, hpf, hne⟩ hnh

lemma exists_unique_unhit_flag {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N)
    (hori : hits P (orient N i))
    (htri : ∀ c b, hits P (triangle N i c b)) :
    ∃! c : Fin 3, ¬ hits P (flag N i c) := by
  have hex : ∃ c : Fin 3, ¬ hits P (flag N i c) := by
    by_contra hall
    push Not at hall
    rcases hori with ⟨u, hu, hpu, hne⟩
    simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu hpu
    rcases hu with rfl | ⟨c, rfl⟩
    · rcases hpu with hp | ⟨c, hpc⟩
      · exact hne hp
      · have hsw := (hits_flag_eq_swap P hinv i c (hall c)).1
        have hback : P (leaf N i c false) = name N i 0 := by rw [hpc, hinv]
        rw [hsw] at hback
        exact leaf_ne_hub0 N i i c true hback
    · have hsw := (hits_flag_eq_swap P hinv i c (hall c)).1
      rw [hsw] at hpu
      rcases hpu with hp | ⟨c', hpc'⟩
      · exact leaf_ne_hub0 N i i c true hp
      · have := (leaf_inj.mp hpc').2.2
        cases this
  rcases hex with ⟨c0, hc0⟩
  refine ⟨c0, hc0, ?_⟩
  intro c1 hc1
  have hm0 := hub_maps_into_flag P hinv i c0 false (htri c0 false) hc0
  have hm1 := hub_maps_into_flag P hinv i c1 false (htri c1 false) hc1
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hm0 hm1
  rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1 <;>
    exact (leaf_inj.mp (h1.symm.trans h0)).2.1

lemma eq_permOf_of_controls {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (a : Fin N → Fin 3)
    (hori : ∀ i, hits P (orient N i))
    (htri : ∀ i c b, hits P (triangle N i c b))
    (hunhit : ∀ i, ¬ hits P (flag N i (a i)))
    (hhit : ∀ i c, c ≠ a i → hits P (flag N i c)) :
    P = permOf N a := by
  have hblock : ∀ (i : Fin N) (s : Fin 8), P (name N i s) = permOf N a (name N i s) := by
    intro i s
    have h0 : P (name N i 0) = leaf N i (a i) false := by
      rcases hori i with ⟨u, hu, hpu, hne⟩
      simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu hpu
      rcases hu with rfl | ⟨c, rfl⟩
      · rcases hpu with hp | ⟨c, hpc⟩
        · exact absurd hp hne
        · by_cases hc : c = a i
          · subst hc; exact hpc.symm
          · exfalso
            have hsw := (hits_flag_eq_swap P hinv i c (hhit i c hc)).1
            have hback : P (leaf N i c false) = name N i 0 := by rw [hpc, hinv]
            rw [hsw] at hback
            exact leaf_ne_hub0 N i i c true hback
      · by_cases hc : c = a i
        · subst hc
          rcases hpu with hp | ⟨c', hpc'⟩
          · rw [← hp, hinv]
          · exfalso
            by_cases hc' : c' = a i
            · subst hc'; exact hne hpc'.symm
            · have hsw := (hits_flag_eq_swap P hinv i c' (hhit i c' hc')).1
              have hback : P (leaf N i c' false) = leaf N i (a i) false := by rw [hpc', hinv]
              rw [hsw] at hback
              have := (leaf_inj.mp hback).2.2
              cases this
        · exfalso
          have hsw := (hits_flag_eq_swap P hinv i c (hhit i c hc)).1
          rw [hsw] at hpu
          rcases hpu with hp | ⟨c', hpc'⟩
          · exact leaf_ne_hub0 N i i c true hp
          · have := (leaf_inj.mp hpc').2.2
            cases this
    have h0_rev : P (leaf N i (a i) false) = name N i 0 := by rw [← h0, hinv]
    have h1 : P (name N i 1) = leaf N i (a i) true := by
      have hm := hub_maps_into_flag P hinv i (a i) true (htri i (a i) true) (hunhit i)
      simp only [ite_true, flag, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hp | hp
      · exfalso
        have heq : name N i 1 = name N i 0 := P.injective (hp.trans h0.symm)
        exact hub0_ne_hub1 N i i heq.symm
      · exact hp
    have h1_rev : P (leaf N i (a i) true) = name N i 1 := by rw [← h1, hinv]
    have hleaf : ∀ (c : Fin 3) (b : Bool), P (leaf N i c b) = permOf N a (leaf N i c b) := by
      intro c b
      by_cases hc : c = a i
      · subst hc
        rw [permOf_leaf_eq]
        cases b
        · exact h0_rev
        · exact h1_rev
      · rw [permOf_leaf_ne N a i c b (Ne.symm hc)]
        have hsw := hits_flag_eq_swap P hinv i c (hhit i c hc)
        cases b
        · exact hsw.1
        · exact hsw.2
    fin_cases s
    · change P (name N i 0) = permOf N a (name N i 0)
      rw [h0, permOf_name, blockSwap_zero]; rfl
    · change P (name N i 1) = permOf N a (name N i 1)
      rw [h1, permOf_name, blockSwap_one]
      apply Fin.ext
      rw [leaf_val, name_val]
      have hmod : (Fin.ofNat 8 (3 + 2 * (a i).val)).val = 3 + 2 * (a i).val := by
        change (3 + 2 * (a i).val) % 8 = 3 + 2 * (a i).val
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      simp only [Bool.toNat_true]
      omega
    · exact hleaf 0 false
    · exact hleaf 0 true
    · exact hleaf 1 false
    · exact hleaf 1 true
    · exact hleaf 2 false
    · exact hleaf 2 true
  ext u
  rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
  · exact congrArg Fin.val (hblock i s)
  · rw [permOf_spare]
    rcases eq_name_or_spare N (P (spare N)) with ⟨i, s, hsp⟩ | hsp
    · exfalso
      have hback : P (name N i s) = spare N := by rw [← hsp, hinv]
      rw [hblock i s, permOf_name] at hback
      exact name_ne_spare N i _ hback
    · exact congrArg Fin.val hsp

end PEqualNP.Outside.L_lib_885

theorem PEqualNP.Outside.L_lib_885 : (∀ (N : Nat), 2 ≤ N →
  let Tag := Fin N × Fin 3
  ∀ B : Finset (Tag × Tag), (∀ e ∈ B, e.1.1 < e.2.1) →
  let k := 8*N+1
  let name := fun (i : Fin N) (s : Fin 8) => Fin.ofNat (8*N+1) (8*i.val+s.val)
  let leaf := fun (i : Fin N) (c : Fin 3) (b : Bool) =>
    name i (Fin.ofNat 8 (2+2*c.val+b.toNat))
  let flag := fun (i : Fin N) (c : Fin 3) => ({leaf i c false,leaf i c true} : Finset (Fin k))
  let orient := fun i : Fin N => insert (name i 0) (Finset.univ.image (fun c : Fin 3 => leaf i c false))
  let triangle := fun (i : Fin N) (c : Fin 3) (b : Bool) => insert (name i (if b then 1 else 0)) (flag i c)
  let pad := fun (i : Fin N) (j : Fin 4) =>
    name (⟨(i.val+1)%N,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin N) (Fin.ofNat 8 j.val)
  let control := fun S : Finset (Fin k) =>
    (∃ i, S = orient i) ∨ (∃ i c b j, S = insert (pad i j) (triangle i c b))
  let tests := Finset.univ.filter (fun S : Finset (Fin k) =>
    control S ∨ ∃ e ∈ B, S = flag e.1.1 e.1.2 ∪ flag e.2.1 e.2.2)
  let valid := fun a : Fin N → Fin 3 => ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2
  let hits := fun (P : Equiv.Perm (Fin k)) (S : Finset (Fin k)) =>
    ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
  let Fits := {P : Equiv.Perm (Fin k) // Function.Involutive P ∧ ∀ S ∈ tests, hits P S}
  tests.card = 25*N+B.card ∧ (∀ S ∈ tests, S.card = 4) ∧
  ∃ E : {a : Fin N → Fin 3 // valid a} ≃ Fits,
    (∀ a i c, (¬ hits (E a).val (flag i c)) ↔ a.val i = c) ∧
    ∀ a b, (Finset.univ.filter (fun u : Fin k => (E a).val u ≠ (E b).val u)).card =
      6*(Finset.univ.filter (fun i : Fin N => a.val i ≠ b.val i)).card) := by
  classical
  intro N hN Tag B hB
  dsimp only
  let O : Finset (Finset (Fin (PEqualNP.Outside.L_lib_885.k N))) :=
    Finset.univ.image (PEqualNP.Outside.L_lib_885.orient N)
  let T : Finset (Finset (Fin (PEqualNP.Outside.L_lib_885.k N))) :=
    Finset.univ.image (fun p : Fin N × Fin 3 × Bool × Fin 4 =>
      PEqualNP.Outside.L_lib_885.padded N p.1 p.2.1 p.2.2.1 p.2.2.2)
  let F : Finset (Finset (Fin (PEqualNP.Outside.L_lib_885.k N))) :=
    B.image (fun e => PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪
      PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2)
  have htests_eq :
      Finset.univ.filter (fun S : Finset (Fin (PEqualNP.Outside.L_lib_885.k N)) =>
        ((∃ i, S = PEqualNP.Outside.L_lib_885.orient N i) ∨
          (∃ i c b j, S = PEqualNP.Outside.L_lib_885.padded N i c b j)) ∨
        ∃ e ∈ B, S = PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪
          PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2) = O ∪ T ∪ F := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      O, T, F, Finset.mem_image]
    constructor
    · rintro ((⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨(i, c, b, j), rfl⟩)
      · exact Or.inr ⟨e, he, rfl⟩
    · rintro ((⟨i, rfl⟩ | ⟨⟨i, c, b, j⟩, rfl⟩) | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨i, c, b, j, rfl⟩)
      · exact Or.inr ⟨e, he, rfl⟩
  have hO_card : O.card = N := by
    dsimp only [O]
    rw [Finset.card_image_of_injective _ (fun _ _ h => PEqualNP.Outside.L_lib_885.orient_inj h)]
    simp
  have hT_card : T.card = 24 * N := by
    dsimp only [T]
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega
    · rintro ⟨i1, c1, b1, j1⟩ ⟨i2, c2, b2, j2⟩ h
      rcases PEqualNP.Outside.L_lib_885.padded_inj hN h with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  have hF_card : F.card = B.card := by
    dsimp only [F]
    rw [Finset.card_image_of_injOn]
    intro e1 he1 e2 he2 h
    exact PEqualNP.Outside.L_lib_885.forb_inj (hB e1 he1) (hB e2 he2) h
  have hOT_disj : Disjoint O T := by
    rw [Finset.disjoint_left]
    intro S hSO hST
    rcases Finset.mem_image.mp hSO with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hST with ⟨⟨i', c, b, j⟩, _, h⟩
    exact PEqualNP.Outside.L_lib_885.orient_ne_padded hN i i' c b j h.symm
  have hOTF_disj : Disjoint (O ∪ T) F := by
    rw [Finset.disjoint_left]
    intro S hSOT hSF
    rcases Finset.mem_image.mp hSF with ⟨e, he, rfl⟩
    have hne : e.1.1 ≠ e.2.1 := ne_of_lt (hB e he)
    rcases Finset.mem_union.mp hSOT with hSO | hST
    · rcases Finset.mem_image.mp hSO with ⟨i, _, h⟩
      exact PEqualNP.Outside.L_lib_885.orient_ne_forb hne i e.1.2 e.2.2 h
    · rcases Finset.mem_image.mp hST with ⟨⟨i, c, b, j⟩, _, h⟩
      exact PEqualNP.Outside.L_lib_885.padded_ne_forb hN hne i c b j e.1.2 e.2.2 h
  refine ⟨?_, ?_, ?_⟩
  · change (Finset.univ.filter (fun S : Finset (Fin (PEqualNP.Outside.L_lib_885.k N)) =>
        ((∃ i, S = PEqualNP.Outside.L_lib_885.orient N i) ∨
          (∃ i c b j, S = PEqualNP.Outside.L_lib_885.padded N i c b j)) ∨
        ∃ e ∈ B, S = PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪
          PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2)).card = 25 * N + B.card
    rw [htests_eq, Finset.card_union_of_disjoint hOTF_disj,
      Finset.card_union_of_disjoint hOT_disj, hO_card, hT_card, hF_card]
    omega
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rcases hS with (⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩
    · exact PEqualNP.Outside.L_lib_885.orient_card N i
    · exact PEqualNP.Outside.L_lib_885.padded_card hN i c b j
    · exact PEqualNP.Outside.L_lib_885.forb_card (ne_of_lt (hB e he)) e.1.2 e.2.2
  · let toFits : {a : Fin N → Fin 3 // ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2} →
        {P : Equiv.Perm (Fin (PEqualNP.Outside.L_lib_885.k N)) //
          Function.Involutive P ∧ ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin (PEqualNP.Outside.L_lib_885.k N)) =>
            ((∃ i, S = PEqualNP.Outside.L_lib_885.orient N i) ∨
              (∃ i c b j, S = PEqualNP.Outside.L_lib_885.padded N i c b j)) ∨
            ∃ e ∈ B, S = PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪
              PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2),
            PEqualNP.Outside.L_lib_885.hits P S} :=
      fun a => ⟨PEqualNP.Outside.L_lib_885.permOf N a.val,
        PEqualNP.Outside.L_lib_885.permOf_invol N a.val, by
          intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          rcases hS with (⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩
          · exact PEqualNP.Outside.L_lib_885.permOf_hits_orient N a.val i
          · rcases PEqualNP.Outside.L_lib_885.permOf_hits_triangle N a.val i c b with ⟨u, hu, hpu, hne⟩
            exact ⟨u, Finset.mem_insert_of_mem hu, Finset.mem_insert_of_mem hpu, hne⟩
          · rcases a.property e he with h1 | h2
            · have hh : PEqualNP.Outside.L_lib_885.hits (PEqualNP.Outside.L_lib_885.permOf N a.val)
                  (PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2) := by
                by_contra hnh
                exact h1 ((PEqualNP.Outside.L_lib_885.permOf_hits_flag_iff N a.val e.1.1 e.1.2).mp hnh)
              rcases hh with ⟨u, hu, hpu, hne⟩
              exact ⟨u, Finset.mem_union_left _ hu, Finset.mem_union_left _ hpu, hne⟩
            · have hh : PEqualNP.Outside.L_lib_885.hits (PEqualNP.Outside.L_lib_885.permOf N a.val)
                  (PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2) := by
                by_contra hnh
                exact h2 ((PEqualNP.Outside.L_lib_885.permOf_hits_flag_iff N a.val e.2.1 e.2.2).mp hnh)
              rcases hh with ⟨u, hu, hpu, hne⟩
              exact ⟨u, Finset.mem_union_right _ hu, Finset.mem_union_right _ hpu, hne⟩⟩
    have hdecode : ∀ P : {P : Equiv.Perm (Fin (PEqualNP.Outside.L_lib_885.k N)) //
          Function.Involutive P ∧ ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin (PEqualNP.Outside.L_lib_885.k N)) =>
            ((∃ i, S = PEqualNP.Outside.L_lib_885.orient N i) ∨
              (∃ i c b j, S = PEqualNP.Outside.L_lib_885.padded N i c b j)) ∨
            ∃ e ∈ B, S = PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪
              PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2),
            PEqualNP.Outside.L_lib_885.hits P S},
        ∃ a : {a : Fin N → Fin 3 // ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2}, toFits a = P := by
      intro P
      have hori : ∀ i, PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.orient N i) := by
        intro i
        apply P.property.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl (Or.inl ⟨i, rfl⟩)
      have htri : ∀ i c b, PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.triangle N i c b) := by
        intro i c b
        apply PEqualNP.Outside.L_lib_885.hits_triangle_of_padded P.val P.property.1 i c b
        intro j
        apply P.property.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨i, c, b, j, rfl⟩)
      have huniq : ∀ i, ∃! c : Fin 3, ¬ PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.flag N i c) :=
        fun i => PEqualNP.Outside.L_lib_885.exists_unique_unhit_flag P.val P.property.1 i (hori i) (htri i)
      let a : Fin N → Fin 3 := fun i => Classical.choose (huniq i)
      have ha_spec : ∀ i, ¬ PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.flag N i (a i)) ∧
          ∀ c, ¬ PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.flag N i c) → c = a i :=
        fun i => Classical.choose_spec (huniq i)
      have hhit : ∀ i c, c ≠ a i → PEqualNP.Outside.L_lib_885.hits P.val (PEqualNP.Outside.L_lib_885.flag N i c) := by
        intro i c hne
        by_contra hnh
        exact hne ((ha_spec i).2 c hnh)
      have hPeq : P.val = PEqualNP.Outside.L_lib_885.permOf N a :=
        PEqualNP.Outside.L_lib_885.eq_permOf_of_controls P.val P.property.1 a hori htri (fun i => (ha_spec i).1) hhit
      have hval : ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2 := by
        intro e he
        by_contra hboth
        push Not at hboth
        rcases hboth with ⟨he1, he2⟩
        have hS : PEqualNP.Outside.L_lib_885.hits P.val
            (PEqualNP.Outside.L_lib_885.flag N e.1.1 e.1.2 ∪ PEqualNP.Outside.L_lib_885.flag N e.2.1 e.2.2) := by
          apply P.property.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨e, he, rfl⟩
        rw [hPeq] at hS
        rcases hS with ⟨u, hu, hpu, _⟩
        simp only [Finset.mem_union, PEqualNP.Outside.L_lib_885.flag,
          Finset.mem_insert, Finset.mem_singleton] at hu hpu
        rcases hu with (rfl | rfl) | (rfl | rfl)
        · rw [← he1, PEqualNP.Outside.L_lib_885.permOf_leaf_eq N a e.1.1 false] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ true h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ true h.symm
        · rw [← he1, PEqualNP.Outside.L_lib_885.permOf_leaf_eq N a e.1.1 true] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ true h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ true h.symm
        · rw [← he2, PEqualNP.Outside.L_lib_885.permOf_leaf_eq N a e.2.1 false] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ true h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub0 N _ _ _ true h.symm
        · rw [← he2, PEqualNP.Outside.L_lib_885.permOf_leaf_eq N a e.2.1 true] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ true h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ false h.symm
          · exact PEqualNP.Outside.L_lib_885.leaf_ne_hub1 N _ _ _ true h.symm
      exact ⟨⟨a, hval⟩, Subtype.ext hPeq.symm⟩
    have hbij : Function.Bijective toFits := by
      constructor
      · intro a1 a2 heq
        apply Subtype.ext
        funext i
        have hperm : PEqualNP.Outside.L_lib_885.permOf N a1.val =
            PEqualNP.Outside.L_lib_885.permOf N a2.val := congrArg Subtype.val heq
        have h1 : ¬ PEqualNP.Outside.L_lib_885.hits (PEqualNP.Outside.L_lib_885.permOf N a1.val)
            (PEqualNP.Outside.L_lib_885.flag N i (a1.val i)) :=
          (PEqualNP.Outside.L_lib_885.permOf_hits_flag_iff N a1.val i (a1.val i)).mpr rfl
        rw [hperm] at h1
        exact ((PEqualNP.Outside.L_lib_885.permOf_hits_flag_iff N a2.val i (a1.val i)).mp h1).symm
      · exact hdecode
    refine ⟨Equiv.ofBijective toFits hbij, ?_, ?_⟩
    · intro a i c
      exact PEqualNP.Outside.L_lib_885.permOf_hits_flag_iff N a.val i c
    · intro a b
      exact PEqualNP.Outside.L_lib_885.permOf_dist N a.val b.val

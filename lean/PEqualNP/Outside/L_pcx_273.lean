import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_273_aux

open PEqualNP.ProofComplexity
open Classical

abbrev Raw (m n : ℕ) := Fin m × Fin n
abbrev Cl (m n a : ℕ) := Clause (Sum (Raw m n) (Fin a))
abbrev Hid (a : ℕ) := Clause (Fin a)

def Consistent {a : ℕ} (U : Finset (Hid a)) : Prop :=
  ∃ z : Fin a → Bool, Satisfies z (↑U : Set _)

def RawSat {m n a : ℕ} (x : Raw m n → Bool) (C : Cl m n a) : Prop :=
  ∃ (p : Raw m n) (b : Bool), (Sum.inl p, b) ∈ C ∧ x p = b

noncomputable def hidPart {m n a : ℕ} (C : Cl m n a) : Hid a :=
  Finset.univ.filter (fun l : Fin a × Bool => (Sum.inr l.1, l.2) ∈ C)

noncomputable def posBlocks {m n a : ℕ} (C : Cl m n a) : Finset (Fin m) :=
  Finset.univ.filter (fun j : Fin m => ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C)

noncomputable def posCount {m n a : ℕ} (C : Cl m n a) : ℕ :=
  (C.filter (fun l => l.2 = true ∧ ∃ e : Raw m n, l.1 = Sum.inl e)).card

lemma mem_hidPart {m n a : ℕ} {C : Cl m n a} {l : Fin a × Bool} :
    l ∈ hidPart C ↔ (Sum.inr l.1, l.2) ∈ C := by
  simp [hidPart]

lemma mem_posBlocks {m n a : ℕ} {C : Cl m n a} {j : Fin m} :
    j ∈ posBlocks C ↔ ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C := by
  simp [posBlocks]

lemma posBlocks_le_posCount {m n a : ℕ} (hn : 0 < n) (C : Cl m n a) :
    (posBlocks C).card ≤ posCount C := by
  have hpick : ∀ j : Fin m, j ∈ posBlocks C → ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C :=
    fun j hj => mem_posBlocks.mp hj
  let f : Fin m → Sum (Raw m n) (Fin a) × Bool := fun j =>
    if hj : j ∈ posBlocks C then (Sum.inl (j, Classical.choose (hpick j hj)), true)
    else (Sum.inl (j, ⟨0, hn⟩), true)
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro j hj
    have hj' : j ∈ posBlocks C := Finset.mem_coe.mp hj
    simp only [f, hj', ↓reduceDIte, Finset.mem_coe, Finset.mem_filter]
    exact ⟨Classical.choose_spec (hpick j hj'), trivial, (j, Classical.choose (hpick j hj')), rfl⟩
  · intro j1 h1 j2 h2 hEq
    have h1' : j1 ∈ posBlocks C := Finset.mem_coe.mp h1
    have h2' : j2 ∈ posBlocks C := Finset.mem_coe.mp h2
    simp only [f, h1', h2', ↓reduceDIte] at hEq
    injection hEq with hv _
    injection hv with hp
    exact congrArg Prod.fst hp

lemma exists_partition_clauses (a : ℕ) :
    ∀ t : ℕ, 1 ≤ t → t ≤ 2 ^ a →
      ∃ U : Finset (Hid a),
        U.card = t ∧
        (∀ z : Fin a → Bool, ∃! H : Hid a, H ∈ U ∧ ¬ ClauseSat z H) ∧
        (∀ H ∈ U, ∃ z : Fin a → Bool, ¬ ClauseSat z H) := by
  intro t ht1
  induction t with
  | zero => omega
  | succ t ih =>
    intro htle
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨{∅}, Finset.card_singleton ∅, ?_, ?_⟩
      · intro z
        refine ⟨∅, ⟨Finset.mem_singleton_self ∅, ?_⟩, ?_⟩
        · rintro ⟨l, hl, _⟩; simp at hl
        · rintro H ⟨hH, _⟩; exact Finset.mem_singleton.mp hH
      · intro H hH
        rw [Finset.mem_singleton.mp hH]
        exact ⟨fun _ => false, by rintro ⟨l, hl, _⟩; simp at hl⟩
    · have ht1' : 1 ≤ t := by omega
      have htle' : t ≤ 2 ^ a := by omega
      obtain ⟨U, hUcard, hUuniq, hUex⟩ := ih ht1' htle'
      have hfree : ∃ H0 ∈ U, ∃ v0 : Fin a, (v0, true) ∉ H0 ∧ (v0, false) ∉ H0 := by
        by_contra hno
        push Not at hno
        have hfull : ∀ H ∈ U, ∀ v : Fin a, (v, true) ∈ H ∨ (v, false) ∈ H := by
          intro H hHU v
          by_cases ht : (v, true) ∈ H
          · exact Or.inl ht
          · exact Or.inr (hno H hHU v ht)
        let cls : (Fin a → Bool) → Hid a := fun z => Classical.choose (hUuniq z)
        have hcls_mem : ∀ z : Fin a → Bool, cls z ∈ U :=
          fun z => (Classical.choose_spec (hUuniq z)).1.1
        have hcls_nsat : ∀ z : Fin a → Bool, ¬ ClauseSat z (cls z) :=
          fun z => (Classical.choose_spec (hUuniq z)).1.2
        have hinj : Set.InjOn cls (↑(Finset.univ : Finset (Fin a → Bool)) : Set _) := by
          intro z1 _ z2 _ hEq
          funext v
          rcases hfull (cls z1) (hcls_mem z1) v with hvt | hvf
          · have h1 : z1 v ≠ true := fun ht => hcls_nsat z1 ⟨(v, true), hvt, ht⟩
            have h2 : z2 v ≠ true := fun ht => hcls_nsat z2 ⟨(v, true), hEq ▸ hvt, ht⟩
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
          · have h1 : z1 v ≠ false := fun hf => hcls_nsat z1 ⟨(v, false), hvf, hf⟩
            have h2 : z2 v ≠ false := fun hf => hcls_nsat z2 ⟨(v, false), hEq ▸ hvf, hf⟩
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
        have hmaps : Set.MapsTo cls (↑(Finset.univ : Finset (Fin a → Bool)) : Set _) (↑U : Set _) :=
          fun z _ => Finset.mem_coe.mpr (hcls_mem z)
        have hle := Finset.card_le_card_of_injOn cls hmaps hinj
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hUcard] at hle
        omega
      obtain ⟨H0, hH0U, v0, hvt, hvf⟩ := hfree
      obtain ⟨z0, hz0⟩ := hUex H0 hH0U
      let H1 : Hid a := insert (v0, true) H0
      let H2 : Hid a := insert (v0, false) H0
      let z1 : Fin a → Bool := Function.update z0 v0 false
      let z2 : Fin a → Bool := Function.update z0 v0 true
      have hz1_H0 : ¬ ClauseSat z1 H0 := by
        rintro ⟨⟨v, b⟩, hmem, hsat⟩
        by_cases hv : v = v0
        · subst hv
          cases b
          · exact hvf hmem
          · exact hvt hmem
        · apply hz0
          refine ⟨(v, b), hmem, ?_⟩
          simpa [z1, Function.update, hv] using hsat
      have hz2_H0 : ¬ ClauseSat z2 H0 := by
        rintro ⟨⟨v, b⟩, hmem, hsat⟩
        by_cases hv : v = v0
        · subst hv
          cases b
          · exact hvf hmem
          · exact hvt hmem
        · apply hz0
          refine ⟨(v, b), hmem, ?_⟩
          simpa [z2, Function.update, hv] using hsat
      have hz1_H1 : ¬ ClauseSat z1 H1 := by
        rintro ⟨l, hl, hsat⟩
        rcases Finset.mem_insert.mp hl with rfl | hl0
        · simp [z1] at hsat
        · exact hz1_H0 ⟨l, hl0, hsat⟩
      have hz2_H2 : ¬ ClauseSat z2 H2 := by
        rintro ⟨l, hl, hsat⟩
        rcases Finset.mem_insert.mp hl with rfl | hl0
        · simp [z2] at hsat
        · exact hz2_H0 ⟨l, hl0, hsat⟩
      have hH1_ne_H2 : H1 ≠ H2 := by
        intro hEq
        have hmem : (v0, true) ∈ H2 := hEq ▸ Finset.mem_insert_self (v0, true) H0
        rcases Finset.mem_insert.mp hmem with h1 | h2
        · cases h1
        · exact hvt h2
      have hH1_not_er : H1 ∉ U.erase H0 := by
        intro hmem
        have h1 := (hUuniq z1).unique ⟨Finset.mem_of_mem_erase hmem, hz1_H1⟩ ⟨hH0U, hz1_H0⟩
        exact (Finset.mem_erase.mp hmem).1 h1
      have hH2_not_er : H2 ∉ U.erase H0 := by
        intro hmem
        have h1 := (hUuniq z2).unique ⟨Finset.mem_of_mem_erase hmem, hz2_H2⟩ ⟨hH0U, hz2_H0⟩
        exact (Finset.mem_erase.mp hmem).1 h1
      let U' : Finset (Hid a) := insert H1 (insert H2 (U.erase H0))
      have hU'card : U'.card = t + 1 := by
        have hH1_not_ins : H1 ∉ insert H2 (U.erase H0) := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with hEq | hEr
          · exact hH1_ne_H2 hEq
          · exact hH1_not_er hEr
        rw [Finset.card_insert_of_notMem hH1_not_ins, Finset.card_insert_of_notMem hH2_not_er,
          Finset.card_erase_of_mem hH0U, hUcard]
        omega
      refine ⟨U', hU'card, ?_, ?_⟩
      · intro z
        obtain ⟨Hz, ⟨hHzU, hHznsat⟩, hHzuniq⟩ := hUuniq z
        by_cases hEq : Hz = H0
        · subst Hz
          have her_sat : ∀ H ∈ U.erase H0, ClauseSat z H := by
            intro H hH
            by_contra hnsat
            exact (Finset.mem_erase.mp hH).1 (hHzuniq H ⟨Finset.mem_of_mem_erase hH, hnsat⟩)
          cases hzv : z v0
          · refine ⟨H1, ⟨Finset.mem_insert_self H1 _, ?_⟩, ?_⟩
            · rintro ⟨l, hl, hsat⟩
              rcases Finset.mem_insert.mp hl with rfl | hl0
              · rw [hzv] at hsat; cases hsat
              · exact hHznsat ⟨l, hl0, hsat⟩
            · rintro H ⟨hHU', hHnsat⟩
              rcases Finset.mem_insert.mp hHU' with rfl | hrest
              · rfl
              · rcases Finset.mem_insert.mp hrest with rfl | hEr
                · exfalso
                  exact hHnsat ⟨(v0, false), Finset.mem_insert_self _ _, hzv⟩
                · exact absurd (her_sat H hEr) hHnsat
          · refine ⟨H2, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self H2 _), ?_⟩, ?_⟩
            · rintro ⟨l, hl, hsat⟩
              rcases Finset.mem_insert.mp hl with rfl | hl0
              · rw [hzv] at hsat; cases hsat
              · exact hHznsat ⟨l, hl0, hsat⟩
            · rintro H ⟨hHU', hHnsat⟩
              rcases Finset.mem_insert.mp hHU' with rfl | hrest
              · exfalso
                exact hHnsat ⟨(v0, true), Finset.mem_insert_self _ _, hzv⟩
              · rcases Finset.mem_insert.mp hrest with rfl | hEr
                · rfl
                · exact absurd (her_sat H hEr) hHnsat
        · have hH0sat : ClauseSat z H0 := by
            by_contra hnsat
            exact hEq (hHzuniq H0 ⟨hH0U, hnsat⟩).symm
          have hH1sat : ClauseSat z H1 := by
            obtain ⟨l, hl, hs⟩ := hH0sat
            exact ⟨l, Finset.mem_insert_of_mem hl, hs⟩
          have hH2sat : ClauseSat z H2 := by
            obtain ⟨l, hl, hs⟩ := hH0sat
            exact ⟨l, Finset.mem_insert_of_mem hl, hs⟩
          refine ⟨Hz, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hEq, hHzU⟩)), hHznsat⟩, ?_⟩
          rintro H ⟨hHU', hHnsat⟩
          rcases Finset.mem_insert.mp hHU' with rfl | hrest
          · exact absurd hH1sat hHnsat
          · rcases Finset.mem_insert.mp hrest with rfl | hEr
            · exact absurd hH2sat hHnsat
            · exact hHzuniq H ⟨Finset.mem_of_mem_erase hEr, hHnsat⟩
      · intro H hHU'
        rcases Finset.mem_insert.mp hHU' with rfl | hrest
        · exact ⟨z1, hz1_H1⟩
        · rcases Finset.mem_insert.mp hrest with rfl | hEr
          · exact ⟨z2, hz2_H2⟩
          · exact hUex H (Finset.mem_of_mem_erase hEr)

lemma exists_cover_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (g : α → ℕ) :
    ∀ S : Finset β, ∑ a ∈ U, g a = S.card →
      ∃ B : α → Finset β,
        (∀ a ∈ U, B a ⊆ S) ∧
        (∀ a ∈ U, (B a).card = g a) ∧
        (∀ j ∈ S, ∃ a ∈ U, j ∈ B a) := by
  induction U using Finset.induction_on with
  | empty =>
    intro S hS
    simp only [Finset.sum_empty] at hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp hS.symm
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro j hj; rw [hSe] at hj; simp at hj
  | insert a s ha ih =>
    intro S hS
    rw [Finset.sum_insert ha] at hS
    have hle : g a ≤ S.card := by omega
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hle
    have hcard_un : (S \ A).card + A.card = S.card := by
      have hdisj : Disjoint (S \ A) A := Finset.sdiff_disjoint
      have hun : (S \ A) ∪ A = S := Finset.sdiff_union_of_subset hAS
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hun] at hc
      exact hc.symm
    have hrem : ∑ x ∈ s, g x = (S \ A).card := by omega
    obtain ⟨B', hB'sub, hB'card, hB'cov⟩ := ih (S \ A) hrem
    refine ⟨fun x => if x = a then A else B' x, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAS]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact Finset.Subset.trans (hB'sub x hxs) Finset.sdiff_subset
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAcard]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact hB'card x hxs
    · intro j hj
      by_cases hjA : j ∈ A
      · exact ⟨a, Finset.mem_insert_self a s, by simp [hjA]⟩
      · have hjs : j ∈ S \ A := Finset.mem_sdiff.mpr ⟨hj, hjA⟩
        obtain ⟨x, hxs, hjx⟩ := hB'cov j hjs
        have hne : x ≠ a := fun h => ha (h ▸ hxs)
        exact ⟨x, Finset.mem_insert_of_mem hxs, by simp [hne, hjx]⟩

noncomputable def mkClause {m n a : ℕ} (H : Hid a) (B : Finset (Fin m)) (f : ↥B → Fin n) : Cl m n a :=
  H.image (fun l => (Sum.inr l.1, l.2)) ∪
  (Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true))

lemma hidPart_mkClause {m n a : ℕ} (H : Hid a) (B : Finset (Fin m)) (f : ↥B → Fin n) :
    hidPart (mkClause H B f) = H := by
  ext l
  rw [mem_hidPart, mkClause, Finset.mem_union]
  constructor
  · rintro (h1 | h2)
    · rcases Finset.mem_image.mp h1 with ⟨l', hl', hEq⟩
      rcases l with ⟨v, b⟩
      rcases l' with ⟨v', b'⟩
      injection hEq with hv hb
      injection hv with hv'
      subst hv'; subst hb
      exact hl'
    · rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
      cases hEq
  · intro hl
    exact Or.inl (Finset.mem_image.mpr ⟨l, hl, rfl⟩)

lemma posCount_mkClause {m n a : ℕ} (H : Hid a) (B : Finset (Fin m)) (f : ↥B → Fin n) :
    posCount (mkClause H B f) = B.card := by
  have hfilt : (mkClause H B f).filter (fun l => l.2 = true ∧ ∃ e : Raw m n, l.1 = Sum.inl e) =
      (Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true)) := by
    ext l
    simp only [Finset.mem_filter, mkClause, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h1 | h2, _, e, he⟩
      · rcases h1 with ⟨lh, _, rfl⟩
        cases he
      · exact h2
    · rintro ⟨j, rfl⟩
      exact ⟨Or.inr ⟨j, rfl⟩, rfl, (j.1, f j), rfl⟩
  rw [posCount, hfilt]
  have hinj : Function.Injective (fun j : ↥B => ((Sum.inl (j.1, f j) : Sum (Raw m n) (Fin a)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    exact Subtype.ext (congrArg Prod.fst hp)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]

lemma mkClause_inj {m n a : ℕ} (H : Hid a) (B : Finset (Fin m)) :
    Function.Injective (mkClause (n := n) H B) := by
  intro f1 f2 hEq
  funext j
  have hmem : ((Sum.inl (j.1, f1 j) : Sum (Raw m n) (Fin a)), true) ∈ mkClause H B f2 := by
    rw [← hEq, mkClause]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  rw [mkClause] at hmem
  rcases Finset.mem_union.mp hmem with h1 | h2
  · rcases Finset.mem_image.mp h1 with ⟨_, _, hC⟩
    cases hC
  · rcases Finset.mem_image.mp h2 with ⟨j', _, hC⟩
    injection hC with hv _
    injection hv with hp
    have hj : j' = j := Subtype.ext (congrArg Prod.fst hp)
    subst hj
    exact (congrArg Prod.snd hp).symm

lemma upper_bound {n m a : ℕ} (hm : 0 < m) :
    let t := min m (2 ^ a)
    let b := m / t
    let s := m % t
    let count := (t - s) * n ^ b + s * n ^ (b + 1)
    let lits := (t - s) * b * n ^ b + s * (b + 1) * n ^ (b + 1)
    let width := (m + t - 1) / t
    ∃ F : Finset (Cl m n a),
      (∀ x : Raw m n → Bool,
        (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
          ∃ z : Fin a → Bool, Satisfies (Sum.elim x z) (↑F : Set _)) ∧
      F.card = count ∧
      (∑ C ∈ F, posCount C) = lits ∧
      (∀ C ∈ F, posCount C ≤ width) ∧
      (∀ C ∈ F, ∀ e : Raw m n, (Sum.inl e, false) ∉ C) := by
  intro t b s count lits width
  have h2a_pos : 0 < 2 ^ a := Nat.pow_pos (by omega)
  have ht_pos : 0 < t := Nat.lt_min.mpr ⟨hm, h2a_pos⟩
  have ht_le_m : t ≤ m := Nat.min_le_left m (2 ^ a)
  have ht_le_2a : t ≤ 2 ^ a := Nat.min_le_right m (2 ^ a)
  have hs_lt : s < t := Nat.mod_lt m ht_pos
  have hs_le : s ≤ t := le_of_lt hs_lt
  have hdiv : t * b + s = m := Nat.div_add_mod m t
  obtain ⟨U, hUcard, hUuniq, hUex⟩ := exists_partition_clauses a t ht_pos ht_le_2a
  have hs_le_U : s ≤ U.card := by omega
  obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hs_le_U
  let g : Hid a → ℕ := fun H => if H ∈ S then b + 1 else b
  have hUS_card : (U \ S).card = t - s := by
    have hd : Disjoint (U \ S) S := Finset.sdiff_disjoint
    have hu : (U \ S) ∪ S = U := Finset.sdiff_union_of_subset hSU
    have hc := Finset.card_union_of_disjoint hd
    rw [hu, hUcard, hScard] at hc
    omega
  have hsum_split : ∀ w : ℕ → ℕ,
      (∑ H ∈ U, w (g H)) = (t - s) * w b + s * w (b + 1) := by
    intro w
    have hu : U = (U \ S) ∪ S := (Finset.sdiff_union_of_subset hSU).symm
    have hd : Disjoint (U \ S) S := Finset.sdiff_disjoint
    rw [hu, Finset.sum_union hd]
    have h1 : (∑ H ∈ U \ S, w (g H)) = (t - s) * w b := by
      have hc : ∀ H ∈ U \ S, w (g H) = w b := by
        intro H hH
        have hnS : H ∉ S := (Finset.mem_sdiff.mp hH).2
        simp [g, hnS]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hUS_card]
    have h2 : (∑ H ∈ S, w (g H)) = s * w (b + 1) := by
      have hc : ∀ H ∈ S, w (g H) = w (b + 1) := by
        intro H hH
        simp [g, hH]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hScard]
    rw [h1, h2]
  have hgsum : ∑ H ∈ U, g H = m := by
    have h := hsum_split id
    simp only [id_eq] at h
    rw [h]
    have hts : (t - s) * b + s * (b + 1) = t * b + s := by
      have : (t - s) * b + s * b = t * b := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hs_le]
      linarith
    omega
  have hcardU : (Finset.univ : Finset (Fin m)).card = m := Fintype.card_fin m
  obtain ⟨B, _, hBcard, hBcov⟩ :=
    exists_cover_card U g (Finset.univ : Finset (Fin m)) (by rw [hgsum, hcardU])
  let fam : Hid a → Finset (Cl m n a) := fun H =>
    (Finset.univ : Finset (↥(B H) → Fin n)).image (mkClause H (B H))
  let F : Finset (Cl m n a) := U.biUnion fam
  have hdisj : Set.PairwiseDisjoint (↑U : Set (Hid a)) fam := by
    intro H1 _ H2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    rcases Finset.mem_image.mp hC1 with ⟨f1, _, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨f2, _, hEq⟩
    have hhid := congrArg hidPart hEq
    rw [hidPart_mkClause, hidPart_mkClause] at hhid
    exact hne hhid.symm
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨j0, hj0⟩
      obtain ⟨H0, hH0U, hj0B⟩ := hBcov j0 (Finset.mem_univ j0)
      obtain ⟨z, hzH0⟩ := hUex H0 hH0U
      have hz_other : ∀ H ∈ U, H ≠ H0 → ClauseSat z H := by
        intro H hHU hne
        by_contra hnsat
        exact hne ((hUuniq z).unique ⟨hHU, hnsat⟩ ⟨hH0U, hzH0⟩)
      refine ⟨z, ?_⟩
      intro C hC
      rcases Finset.mem_biUnion.mp (Finset.mem_coe.mp hC) with ⟨H, hHU, hCH⟩
      rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
      by_cases hEq : H = H0
      · subst hEq
        refine ⟨(Sum.inl (j0, f ⟨j0, hj0B⟩), true), ?_, ?_⟩
        · rw [mkClause]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j0, hj0B⟩, Finset.mem_univ _, rfl⟩)
        · simpa [Sum.elim] using hj0 (f ⟨j0, hj0B⟩)
      · obtain ⟨l, hlH, hlz⟩ := hz_other H hHU hEq
        refine ⟨(Sum.inr l.1, l.2), ?_, ?_⟩
        · rw [mkClause]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, hlH, rfl⟩)
        · simpa [Sum.elim] using hlz
    · rintro ⟨z, hz⟩
      by_contra hno
      push Not at hno
      obtain ⟨H0, ⟨hH0U, hH0nsat⟩, _⟩ := hUuniq z
      have hpick : ∀ j : ↥(B H0), ∃ i : Fin n, x (j.1, i) = false := by
        intro j
        obtain ⟨i, hi⟩ := hno j.1
        cases hx : x (j.1, i)
        · exact ⟨i, hx⟩
        · exact False.elim (hi hx)
      let f : ↥(B H0) → Fin n := fun j => Classical.choose (hpick j)
      have hf : ∀ j : ↥(B H0), x (j.1, f j) = false :=
        fun j => Classical.choose_spec (hpick j)
      have hmem : mkClause H0 (B H0) f ∈ (↑F : Set _) := by
        rw [Finset.mem_coe]
        exact Finset.mem_biUnion.mpr ⟨H0, hH0U, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩
      obtain ⟨l, hlC, hlsat⟩ := hz (mkClause H0 (B H0) f) hmem
      rw [mkClause] at hlC
      rcases Finset.mem_union.mp hlC with hl1 | hl2
      · rcases Finset.mem_image.mp hl1 with ⟨lh, hlh, rfl⟩
        exact hH0nsat ⟨lh, hlh, by simpa [Sum.elim] using hlsat⟩
      · rcases Finset.mem_image.mp hl2 with ⟨j, _, rfl⟩
        have hxtrue : x (j.1, f j) = true := by simpa [Sum.elim] using hlsat
        rw [hf j] at hxtrue
        cases hxtrue
  · rw [Finset.card_biUnion hdisj]
    have hfam_card : ∀ H ∈ U, (fam H).card = n ^ (g H) := by
      intro H hHU
      rw [Finset.card_image_of_injective _ (mkClause_inj H (B H)), Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hBcard H hHU]
    rw [Finset.sum_congr rfl hfam_card]
    exact hsum_split (fun k => n ^ k)
  · rw [Finset.sum_biUnion hdisj]
    have hfam_sum : ∀ H ∈ U, (∑ C ∈ fam H, posCount C) = g H * n ^ (g H) := by
      intro H hHU
      rw [Finset.sum_image (fun f1 _ f2 _ hEq => mkClause_inj H (B H) hEq)]
      have hconst : ∀ f : ↥(B H) → Fin n, posCount (mkClause H (B H) f) = g H := by
        intro f
        rw [posCount_mkClause, hBcard H hHU]
      simp_rw [hconst]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, hBcard H hHU, mul_comm]
    rw [Finset.sum_congr rfl hfam_sum]
    have h := hsum_split (fun k => k * n ^ k)
    rw [h]
    ring
  · intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨H, hHU, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [posCount_mkClause, hBcard H hHU]
    by_cases hHS : H ∈ S
    · have hs_pos : 0 < s := by
        rw [← hScard]
        exact Finset.card_pos.mpr ⟨H, hHS⟩
      simp only [g, hHS, ↓reduceIte]
      have h1 : (b + 1) * t ≤ m + t - 1 := by
        have hbt : (b + 1) * t = t * b + t := by ring
        omega
      exact (Nat.le_div_iff_mul_le ht_pos).mpr h1
    · simp only [g, hHS, ↓reduceIte]
      have h1 : b * t ≤ m + t - 1 := by
        have hbt : b * t = t * b := by ring
        omega
      exact (Nat.le_div_iff_mul_le ht_pos).mpr h1
  · intro C hC e hmem
    rcases Finset.mem_biUnion.mp hC with ⟨H, _, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [mkClause] at hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨_, _, hEq⟩
      cases hEq
    · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
      cases hEq

lemma exists_minimal_unsat {a : ℕ} :
    ∀ k : ℕ, ∀ U0 : Finset (Hid a), U0.card ≤ k → ¬ Consistent U0 →
      ∃ U ⊆ U0, ¬ Consistent U ∧ ∀ H ∈ U, Consistent (U.erase H) := by
  intro k
  induction k with
  | zero =>
    intro U0 hcard hunsat
    have hU0 : U0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exfalso
    apply hunsat
    refine ⟨fun _ => false, ?_⟩
    intro H hH
    rw [hU0] at hH
    simp at hH
  | succ k ih =>
    intro U0 hcard hunsat
    by_cases hmin : ∀ H ∈ U0, Consistent (U0.erase H)
    · exact ⟨U0, Finset.Subset.refl _, hunsat, hmin⟩
    · push Not at hmin
      obtain ⟨H, hHU0, her⟩ := hmin
      have hlt : (U0.erase H).card < U0.card := Finset.card_erase_lt_of_mem hHU0
      have hle : (U0.erase H).card ≤ k := by omega
      obtain ⟨U, hUsub, hUunsat, hUmin⟩ := ih (U0.erase H) hle her
      exact ⟨U, Finset.Subset.trans hUsub (Finset.erase_subset H U0), hUunsat, hUmin⟩

lemma card_minimal_unsat_le {a : ℕ} (U : Finset (Hid a))
    (hunsat : ¬ Consistent U) (hmin : ∀ H ∈ U, Consistent (U.erase H)) :
    U.card ≤ 2 ^ a := by
  let wit : Hid a → (Fin a → Bool) := fun H =>
    if hHU : H ∈ U then Classical.choose (hmin H hHU) else fun _ => false
  have hwit_sat : ∀ H ∈ U, Satisfies (wit H) (↑(U.erase H) : Set _) := by
    intro H hHU
    simp only [wit, hHU, ↓reduceDIte]
    exact Classical.choose_spec (hmin H hHU)
  have hwit_nsat : ∀ H ∈ U, ¬ ClauseSat (wit H) H := by
    intro H hHU hsat
    apply hunsat
    refine ⟨wit H, ?_⟩
    intro H' hH'
    have hH'U : H' ∈ U := Finset.mem_coe.mp hH'
    by_cases hEq : H' = H
    · subst hEq; exact hsat
    · exact hwit_sat H hHU H' (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hEq, hH'U⟩))
  have hinj : Set.InjOn wit (↑U : Set _) := by
    intro H1 h1 H2 h2 hEq
    have h1' : H1 ∈ U := Finset.mem_coe.mp h1
    have h2' : H2 ∈ U := Finset.mem_coe.mp h2
    by_contra hne
    have hsat : ClauseSat (wit H1) H2 :=
      hwit_sat H1 h1' H2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨Ne.symm hne, h2'⟩))
    rw [hEq] at hsat
    exact hwit_nsat H2 h2' hsat
  have hmaps : Set.MapsTo wit (↑U : Set _) (↑(Finset.univ : Finset (Fin a → Bool)) : Set _) :=
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hle := Finset.card_le_card_of_injOn wit hmaps hinj
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hle
  exact hle

def xAssign {m n : ℕ} (α : Fin m → Fin n) : Raw m n → Bool :=
  fun p => decide (p.2 ≠ α p.1)

def xFlip {m n : ℕ} (α : Fin m → Fin n) (j0 : Fin m) : Raw m n → Bool :=
  fun p => if p.1 = j0 then true else xAssign α p

lemma xAssign_eq_false {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = false ↔ i = α j := by
  simp [xAssign]

lemma xAssign_eq_true {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = true ↔ i ≠ α j := by
  simp [xAssign]

lemma rawSat_xFlip_of_not_xAssign {m n a : ℕ} (α : Fin m → Fin n) (j0 : Fin m)
    {C : Cl m n a} (hnot : ¬ RawSat (xAssign α) C) (hsat : RawSat (xFlip α j0) C) :
    (Sum.inl (j0, α j0), true) ∈ C := by
  obtain ⟨⟨j, i⟩, b, hmem, heq⟩ := hsat
  by_cases hj : j = j0
  · subst hj
    have hb : b = true := by
      simp [xFlip] at heq
      exact heq
    subst hb
    have hi : i = α j := by
      by_contra hne
      apply hnot
      refine ⟨(j, i), true, hmem, ?_⟩
      exact (xAssign_eq_true α j i).mpr hne
    subst hi
    exact hmem
  · exfalso
    apply hnot
    refine ⟨(j, i), b, hmem, ?_⟩
    simpa [xFlip, hj] using heq

lemma card_filter_not_rawSat_le {m n a : ℕ} (C : Cl m n a) :
    (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card ≤
      n ^ (m - (posBlocks C).card) := by
  let P := posBlocks C
  let S := Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)
  let T : Finset (↥(Pᶜ) → Fin n) := Finset.univ
  have hinj : Set.InjOn (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) (↑S : Set _) := by
    intro α1 h1 α2 h2 hfun
    have h1' : ¬ RawSat (xAssign α1) C := (Finset.mem_filter.mp h1).2
    have h2' : ¬ RawSat (xAssign α2) C := (Finset.mem_filter.mp h2).2
    funext j
    by_cases hj : j ∈ P
    · obtain ⟨i, hi⟩ := mem_posBlocks.mp hj
      have h1i : α1 j = i := by
        by_contra hne
        apply h1'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α1 j i).mpr (Ne.symm hne)⟩
      have h2i : α2 j = i := by
        by_contra hne
        apply h2'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α2 j i).mpr (Ne.symm hne)⟩
      rw [h1i, h2i]
    · have hjc : j ∈ Pᶜ := Finset.mem_compl.mpr hj
      exact congrFun hfun ⟨j, hjc⟩
  have hmaps : Set.MapsTo (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1)
      (↑S : Set _) (↑T : Set _) :=
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hle := Finset.card_le_card_of_injOn
    (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) hmaps hinj
  have hTcard : T.card = n ^ (Pᶜ).card := by
    change (Finset.univ : Finset (↥(Pᶜ) → Fin n)).card = n ^ (Pᶜ).card
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hPcompl : (Pᶜ).card = m - P.card := by
    have hsum : (Pᶜ).card + P.card = m := by
      have hd : Disjoint (Pᶜ) P := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_compl.mp hx1) hx2
      have hu : Pᶜ ∪ P = Finset.univ := by
        ext x
        by_cases hx : x ∈ P <;> simp
      have hc := Finset.card_union_of_disjoint hd
      rw [hu, Finset.card_univ, Fintype.card_fin] at hc
      exact hc.symm
    omega
  rw [hTcard, hPcompl] at hle
  exact hle

lemma convex_tangent (f : ℕ → ℕ)
    (hinc : ∀ k : ℕ, f k ≤ f (k + 1))
    (hconv : ∀ k : ℕ, f (k + 1) - f k ≤ f (k + 2) - f (k + 1))
    (b x : ℕ) :
    f b + x * (f (b + 1) - f b) ≤ f x + b * (f (b + 1) - f b) := by
  have hdiff_mono : ∀ d i : ℕ, f (i + 1) - f i ≤ f (i + d + 1) - f (i + d) := by
    intro d
    induction d with
    | zero => intro i; simp
    | succ d ih =>
      intro i
      have hEq : i + (d + 1) = i + d + 1 := by omega
      rw [hEq]
      exact le_trans (ih i) (hconv (i + d))
  have hdiff_le : ∀ i j : ℕ, i ≤ j → f (i + 1) - f i ≤ f (j + 1) - f j := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact hdiff_mono d i
  by_cases hbx : b ≤ x
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbx
    induction d with
    | zero => simp
    | succ d ih =>
      have hEq : b + (d + 1) = b + d + 1 := by omega
      have hstep : f (b + 1) - f b ≤ f (b + d + 1) - f (b + d) :=
        hdiff_le b (b + d) (by omega)
      have hle : f (b + d) ≤ f (b + d + 1) := hinc (b + d)
      have hmul : (b + (d + 1)) * (f (b + 1) - f b) =
          (b + d) * (f (b + 1) - f b) + (f (b + 1) - f b) := by ring
      rw [hmul, hEq]
      omega
  · have hxb : x ≤ b := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hxb
    have hback : ∀ d x : ℕ, x + d = b →
        f b + x * (f (b + 1) - f b) ≤ f x + b * (f (b + 1) - f b) := by
      intro d
      induction d with
      | zero =>
        intro x hx
        have hEq : x = b := by omega
        subst hEq
        exact le_refl _
      | succ d ih =>
        intro x hx
        have h1 := ih (x + 1) (by omega)
        have hstep : f (x + 1) - f x ≤ f (b + 1) - f b := hdiff_le x b (by omega)
        have hle : f x ≤ f (x + 1) := hinc x
        have hmul : (x + 1) * (f (b + 1) - f b) =
            x * (f (b + 1) - f b) + (f (b + 1) - f b) := by ring
        rw [hmul] at h1
        omega
    exact hback d x hd.symm

lemma convex_balanced_lower {α : Type*} (f : ℕ → ℕ)
    (hinc : ∀ k : ℕ, f k ≤ f (k + 1))
    (hconv : ∀ k : ℕ, f (k + 1) - f k ≤ f (k + 2) - f (k + 1))
    (t b s : ℕ) (hs : s ≤ t)
    (hsuper : f b ≤ b * (f (b + 1) - f b))
    (S : Finset α) (g : α → ℕ) (hSk : S.card ≤ t) (hsum : ∑ x ∈ S, g x = t * b + s) :
    (t - s) * f b + s * f (b + 1) ≤ ∑ x ∈ S, f (g x) := by
  let sl := f (b + 1) - f b
  have hfb_le : f b ≤ f (b + 1) := hinc b
  have hpt : ∀ x ∈ S, f b + g x * sl ≤ f (g x) + b * sl :=
    fun x _ => convex_tangent f hinc hconv b (g x)
  have hsum_le : ∑ x ∈ S, (f b + g x * sl) ≤ ∑ x ∈ S, (f (g x) + b * sl) :=
    Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← Finset.sum_mul, hsum] at hsum_le
  have hextra : (t - S.card) * f b ≤ (t - S.card) * (b * sl) :=
    Nat.mul_le_mul_left (t - S.card) hsuper
  have h1 : S.card * f b + (t - S.card) * f b = t * f b := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hSk]
  have h2 : S.card * (b * sl) + (t - S.card) * (b * sl) = t * (b * sl) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hSk]
  have h3 : (t * b + s) * sl = t * (b * sl) + s * sl := by ring
  have h4 : (t - s) * f b + s * f (b + 1) = t * f b + s * sl := by
    have hfb1 : f (b + 1) = f b + sl := (Nat.add_sub_of_le hfb_le).symm
    rw [hfb1, Nat.mul_add]
    have hts : (t - s) * f b + s * f b = t * f b := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hs]
    omega
  rw [h4]
  omega

lemma alpha_extract {n m a : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (G : Finset (Cl m n a))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin a → Bool, Satisfies (Sum.elim x z) (↑G : Set _))
    (α : Fin m → Fin n) :
    let t := min m (2 ^ a)
    let b := m / t
    let s := m % t
    let count := (t - s) * n ^ b + s * n ^ (b + 1)
    let lits := (t - s) * b * n ^ b + s * (b + 1) * n ^ (b + 1)
    let width := (m + t - 1) / t
    let Gα := G.filter (fun C => ¬ RawSat (xAssign α) C)
    count ≤ (∑ C ∈ Gα, n ^ (posBlocks C).card) ∧
    lits ≤ (∑ C ∈ Gα, posCount C * n ^ (posBlocks C).card) ∧
    (∃ D ∈ G, width ≤ posCount D) := by
  intro t b s count lits width Gα
  have hn1 : 0 < n := by omega
  have h2a_pos : 0 < 2 ^ a := Nat.pow_pos (by omega)
  have ht_pos : 0 < t := Nat.lt_min.mpr ⟨hm, h2a_pos⟩
  have ht_le_m : t ≤ m := Nat.min_le_left m (2 ^ a)
  have hb_pos : 1 ≤ b := Nat.div_pos ht_le_m ht_pos
  have hs_le : s ≤ t := le_of_lt (Nat.mod_lt m ht_pos)
  have hdiv : t * b + s = m := Nat.div_add_mod m t
  let Uα : Finset (Hid a) := Gα.image hidPart
  have hUα_unsat : ¬ Consistent Uα := by
    rintro ⟨z, hz⟩
    have hsatG : Satisfies (Sum.elim (xAssign α) z) (↑G : Set _) := by
      intro C hC
      have hCG : C ∈ G := Finset.mem_coe.mp hC
      by_cases hraw : RawSat (xAssign α) C
      · obtain ⟨p, bv, hmem, heq⟩ := hraw
        exact ⟨(Sum.inl p, bv), hmem, by simpa [Sum.elim] using heq⟩
      · have hCGα : C ∈ Gα := Finset.mem_filter.mpr ⟨hCG, hraw⟩
        have hHU : hidPart C ∈ (↑Uα : Set _) :=
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨C, hCGα, rfl⟩)
        obtain ⟨l, hl, hzl⟩ := hz (hidPart C) hHU
        exact ⟨(Sum.inr l.1, l.2), mem_hidPart.mp hl, by simpa [Sum.elim] using hzl⟩
    obtain ⟨j, hj⟩ := (henc (xAssign α)).mpr ⟨z, hsatG⟩
    have htrue := hj (α j)
    have hfalse : xAssign α (j, α j) = false := (xAssign_eq_false α j (α j)).mpr rfl
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨U, hUsub, hUunsat, hUmin⟩ :=
    exists_minimal_unsat Uα.card Uα (le_refl _) hUα_unsat
  have hU_le_2a : U.card ≤ 2 ^ a := card_minimal_unsat_le U hUunsat hUmin
  have hphi_ex : ∀ j : Fin m, ∃ H ∈ U, ∀ C ∈ Gα, hidPart C = H → (Sum.inl (j, α j), true) ∈ C := by
    intro j
    have hyes : ∃ j' : Fin m, ∀ i : Fin n, xFlip α j (j', i) = true :=
      ⟨j, fun i => by simp [xFlip]⟩
    obtain ⟨z, hz⟩ := (henc (xFlip α j)).mp hyes
    have hbad : ∃ H ∈ U, ¬ ClauseSat z H := by
      by_contra hall
      push Not at hall
      exact hUunsat ⟨z, fun H hH => hall H (Finset.mem_coe.mp hH)⟩
    obtain ⟨H, hHU, hHnsat⟩ := hbad
    refine ⟨H, hHU, ?_⟩
    intro C hCGα hhid
    have hCG : C ∈ (↑G : Set _) := Finset.mem_coe.mpr (Finset.mem_filter.mp hCGα).1
    have hnot : ¬ RawSat (xAssign α) C := (Finset.mem_filter.mp hCGα).2
    obtain ⟨l, hlC, hlsat⟩ := hz C hCG
    rcases l with ⟨v, bv⟩
    rcases v with p | hv
    · have hrawflip : RawSat (xFlip α j) C := ⟨p, bv, hlC, by simpa [Sum.elim] using hlsat⟩
      exact rawSat_xFlip_of_not_xAssign α j hnot hrawflip
    · exfalso
      apply hHnsat
      have hlH : (hv, bv) ∈ H := by
        rw [← hhid]
        exact mem_hidPart.mpr hlC
      exact ⟨(hv, bv), hlH, by simpa [Sum.elim] using hlsat⟩
  let φ : Fin m → Hid a := fun j => Classical.choose (hphi_ex j)
  have hφU : ∀ j : Fin m, φ j ∈ U := fun j => (Classical.choose_spec (hphi_ex j)).1
  have hφC : ∀ (j : Fin m) (C : Cl m n a), C ∈ Gα → hidPart C = φ j →
      (Sum.inl (j, α j), true) ∈ C :=
    fun j => (Classical.choose_spec (hphi_ex j)).2
  let g : Hid a → ℕ := fun H => (Finset.univ.filter (fun j : Fin m => φ j = H)).card
  have hgsumU : ∑ H ∈ U, g H = m := by
    have h1 : ∑ H ∈ U, (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
        (Finset.univ : Finset (Fin m)).card := by
      have hcard_eq : ∀ H : Hid a,
          (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
          ∑ j : Fin m, if φ j = H then 1 else 0 := by
        intro H; simp [Finset.sum_boole]
      simp_rw [hcard_eq]
      rw [Finset.sum_comm]
      have hinner : ∀ j : Fin m, (∑ H ∈ U, if φ j = H then 1 else 0) = 1 := by
        intro j
        rw [Finset.sum_ite_eq U (φ j) (fun _ => 1)]
        simp [hφU j]
      simp_rw [hinner]
      simp
    rw [h1, Finset.card_univ, Fintype.card_fin]
  let Up : Finset (Hid a) := U.filter (fun H => 0 < g H)
  have hUp_sub : Up ⊆ U := Finset.filter_subset _ U
  have hgsumUp : ∑ H ∈ Up, g H = m := by
    rw [← hgsumU]
    apply Finset.sum_subset hUp_sub
    intro H hHU hnotUp
    simp only [Up, Finset.mem_filter, hHU, true_and, not_lt, Nat.le_zero] at hnotUp
    exact hnotUp
  have hUp_le_m : Up.card ≤ m := by
    calc
      Up.card = ∑ _H ∈ Up, 1 := by simp
      _ ≤ ∑ H ∈ Up, g H := Finset.sum_le_sum (fun H hH => (Finset.mem_filter.mp hH).2)
      _ = m := hgsumUp
  have hUp_le_t : Up.card ≤ t :=
    Nat.le_min.mpr ⟨hUp_le_m, le_trans (Finset.card_le_card hUp_sub) hU_le_2a⟩
  have hpick_ex : ∀ H ∈ U, ∃ C ∈ Gα, hidPart C = H :=
    fun H hHU => Finset.mem_image.mp (hUsub hHU)
  let pickC : Hid a → Cl m n a := fun H =>
    if hHU : H ∈ U then Classical.choose (hpick_ex H hHU) else ∅
  have hpick_mem : ∀ H ∈ U, pickC H ∈ Gα := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).1
  have hpick_hid : ∀ H ∈ U, hidPart (pickC H) = H := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).2
  have hg_le_posBlocks : ∀ H ∈ U, g H ≤ (posBlocks (pickC H)).card := by
    intro H hHU
    apply Finset.card_le_card
    intro j hj
    have hjEq : φ j = H := (Finset.mem_filter.mp hj).2
    apply mem_posBlocks.mpr
    exact ⟨α j, hφC j (pickC H) (hpick_mem H hHU) (by rw [hpick_hid H hHU, hjEq])⟩
  have hinj : Set.InjOn pickC (↑Up : Set _) := by
    intro H1 h1 H2 h2 hEq
    have h1' : H1 ∈ U := hUp_sub (Finset.mem_coe.mp h1)
    have h2' : H2 ∈ U := hUp_sub (Finset.mem_coe.mp h2)
    rw [← hpick_hid H1 h1', ← hpick_hid H2 h2', hEq]
  have himg_sub : Up.image pickC ⊆ Gα := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨H, hHUp, rfl⟩
    exact hpick_mem H (hUp_sub hHUp)
  refine ⟨?_, ?_, ?_⟩
  · have hf1_inc : ∀ k : ℕ, n ^ k ≤ n ^ (k + 1) :=
      fun k => Nat.pow_le_pow_right hn1 (by omega)
    have hpow_sub : ∀ k : ℕ, n ^ (k + 1) - n ^ k = (n - 1) * n ^ k := by
      intro k
      rw [Nat.sub_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (n ^ k) n]
    have hf1_conv : ∀ k : ℕ, n ^ (k + 1) - n ^ k ≤ n ^ (k + 2) - n ^ (k + 1) := by
      intro k
      rw [hpow_sub k, hpow_sub (k + 1)]
      exact Nat.mul_le_mul_left (n - 1) (hf1_inc k)
    have hf1_super : n ^ b ≤ b * (n ^ (b + 1) - n ^ b) := by
      rw [hpow_sub b]
      have h2 : 1 ≤ b * (n - 1) := Nat.mul_pos hb_pos (by omega)
      calc
        n ^ b = 1 * n ^ b := (Nat.one_mul _).symm
        _ ≤ (b * (n - 1)) * n ^ b := Nat.mul_le_mul_right _ h2
        _ = b * ((n - 1) * n ^ b) := Nat.mul_assoc _ _ _
    have hlow := convex_balanced_lower (fun k => n ^ k) hf1_inc hf1_conv
      t b s hs_le hf1_super Up g hUp_le_t (hgsumUp.trans hdiv.symm)
    have hmid : ∑ H ∈ Up, n ^ (g H) ≤ ∑ H ∈ Up, n ^ (posBlocks (pickC H)).card :=
      Finset.sum_le_sum (fun H hH => Nat.pow_le_pow_right hn1 (hg_le_posBlocks H (hUp_sub hH)))
    have hup : ∑ H ∈ Up, n ^ (posBlocks (pickC H)).card ≤ ∑ C ∈ Gα, n ^ (posBlocks C).card := by
      have heq : ∑ C ∈ Up.image pickC, n ^ (posBlocks C).card =
          ∑ H ∈ Up, n ^ (posBlocks (pickC H)).card := Finset.sum_image hinj
      rw [← heq]
      exact Finset.sum_le_sum_of_subset himg_sub
    exact le_trans hlow (le_trans hmid hup)
  · have hf2_inc : ∀ k : ℕ, k * n ^ k ≤ (k + 1) * n ^ (k + 1) :=
      fun k => Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hn1 (by omega))
    have hf2_diff : ∀ k : ℕ, (k + 1) * n ^ (k + 1) - k * n ^ k = ((k + 1) * n - k) * n ^ k := by
      intro k
      rw [Nat.pow_succ, Nat.mul_comm (n ^ k) n, ← Nat.mul_assoc, ← Nat.sub_mul]
    have hf2_conv : ∀ k : ℕ,
        (k + 1) * n ^ (k + 1) - k * n ^ k ≤ (k + 2) * n ^ (k + 2) - (k + 1) * n ^ (k + 1) := by
      intro k
      rw [hf2_diff k, hf2_diff (k + 1)]
      apply Nat.mul_le_mul
      · have hmul : (k + 1 + 1) * n = (k + 1) * n + n := by ring
        have hge : k ≤ (k + 1) * n := by nlinarith
        omega
      · exact Nat.pow_le_pow_right hn1 (by omega)
    have hf2_super : b * n ^ b ≤ b * ((b + 1) * n ^ (b + 1) - b * n ^ b) := by
      rw [hf2_diff b]
      have hge : b + 1 ≤ (b + 1) * n := by nlinarith
      have h1 : 1 ≤ (b + 1) * n - b := by omega
      have h2 : n ^ b ≤ ((b + 1) * n - b) * n ^ b := by
        calc
          n ^ b = 1 * n ^ b := (Nat.one_mul _).symm
          _ ≤ ((b + 1) * n - b) * n ^ b := Nat.mul_le_mul_right _ h1
      exact Nat.mul_le_mul_left b h2
    have hlow := convex_balanced_lower (fun k => k * n ^ k) hf2_inc hf2_conv
      t b s hs_le hf2_super Up g hUp_le_t (hgsumUp.trans hdiv.symm)
    have hlow' : lits ≤ ∑ H ∈ Up, g H * n ^ (g H) := by
      have hEq : lits = (t - s) * (b * n ^ b) + s * ((b + 1) * n ^ (b + 1)) := by
        dsimp only [lits]; ring
      rw [hEq]
      exact hlow
    have hmid : ∑ H ∈ Up, g H * n ^ (g H) ≤
        ∑ H ∈ Up, posCount (pickC H) * n ^ (posBlocks (pickC H)).card := by
      apply Finset.sum_le_sum
      intro H hH
      have h1 := hg_le_posBlocks H (hUp_sub hH)
      have h2 := posBlocks_le_posCount hn1 (pickC H)
      exact Nat.mul_le_mul (le_trans h1 h2) (Nat.pow_le_pow_right hn1 h1)
    have hup : ∑ H ∈ Up, posCount (pickC H) * n ^ (posBlocks (pickC H)).card ≤
        ∑ C ∈ Gα, posCount C * n ^ (posBlocks C).card := by
      have heq : ∑ C ∈ Up.image pickC, posCount C * n ^ (posBlocks C).card =
          ∑ H ∈ Up, posCount (pickC H) * n ^ (posBlocks (pickC H)).card := Finset.sum_image hinj
      rw [← heq]
      exact Finset.sum_le_sum_of_subset himg_sub
    exact le_trans hlow' (le_trans hmid hup)
  · have hexH : ∃ H ∈ Up, width ≤ g H := by
      by_contra hall
      push Not at hall
      have hsum_lt : ∑ H ∈ Up, g H ≤ Up.card * (width - 1) := by
        calc
          ∑ H ∈ Up, g H ≤ ∑ _H ∈ Up, (width - 1) :=
            Finset.sum_le_sum (fun H hH => Nat.le_sub_one_of_lt (hall H hH))
          _ = Up.card * (width - 1) := by rw [Finset.sum_const, smul_eq_mul]
      have hw_pos : 1 ≤ width := by
        dsimp only [width]
        exact Nat.div_pos (by omega) ht_pos
      have htw : t * (width - 1) < m := by
        have h1 : width * t ≤ m + t - 1 := Nat.div_mul_le_self (m + t - 1) t
        have h2 : t * (width - 1) + t = width * t := by
          have : width - 1 + 1 = width := by omega
          calc
            t * (width - 1) + t = (width - 1 + 1) * t := by ring
            _ = width * t := by rw [this]
        omega
      have hle2 : Up.card * (width - 1) ≤ t * (width - 1) :=
        Nat.mul_le_mul_right _ hUp_le_t
      omega
    obtain ⟨H, hHUp, hHg⟩ := hexH
    have hHU : H ∈ U := hUp_sub hHUp
    refine ⟨pickC H, (Finset.mem_filter.mp (hpick_mem H hHU)).1, ?_⟩
    exact le_trans hHg (le_trans (hg_le_posBlocks H hHU) (posBlocks_le_posCount hn1 (pickC H)))

lemma lower_bound {n m a : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (G : Finset (Cl m n a))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin a → Bool, Satisfies (Sum.elim x z) (↑G : Set _)) :
    let t := min m (2 ^ a)
    let b := m / t
    let s := m % t
    let count := (t - s) * n ^ b + s * n ^ (b + 1)
    let lits := (t - s) * b * n ^ b + s * (b + 1) * n ^ (b + 1)
    let width := (m + t - 1) / t
    count ≤ G.card ∧ lits ≤ (∑ D ∈ G, posCount D) ∧ ∃ D ∈ G, width ≤ posCount D := by
  intro t b s count lits width
  have hn1 : 0 < n := by omega
  have hnm_pos : 0 < n ^ m := Nat.pow_pos hn1
  have hswap : ∀ f : Cl m n a → ℕ,
      (∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
        f C * n ^ (posBlocks C).card) ≤
      n ^ m * ∑ C ∈ G, f C := by
    intro f
    have h1 : (∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
        f C * n ^ (posBlocks C).card) =
        ∑ C ∈ G, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card *
          (f C * n ^ (posBlocks C).card) := by
      have h2 : ∀ α : Fin m → Fin n,
          (∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C), f C * n ^ (posBlocks C).card) =
          ∑ C ∈ G, if ¬ RawSat (xAssign α) C then f C * n ^ (posBlocks C).card else 0 := by
        intro α; simp [Finset.sum_filter]
      simp_rw [h2]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [h1]
    have hterm : ∀ C ∈ G,
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card *
          (f C * n ^ (posBlocks C).card) ≤ n ^ m * f C := by
      intro C _
      have hcard := card_filter_not_rawSat_le C
      have hp_le : (posBlocks C).card ≤ m := by
        calc
          (posBlocks C).card ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = m := by simp
      calc
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card *
            (f C * n ^ (posBlocks C).card)
          ≤ n ^ (m - (posBlocks C).card) * (f C * n ^ (posBlocks C).card) :=
            Nat.mul_le_mul_right _ hcard
        _ = (n ^ (m - (posBlocks C).card) * n ^ (posBlocks C).card) * f C := by ring
        _ = n ^ m * f C := by rw [← Nat.pow_add, Nat.sub_add_cancel hp_le]
    calc
      ∑ C ∈ G, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card *
          (f C * n ^ (posBlocks C).card)
        ≤ ∑ C ∈ G, n ^ m * f C := Finset.sum_le_sum hterm
      _ = n ^ m * ∑ C ∈ G, f C := by rw [← Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · have hsum_c : n ^ m * count ≤
        ∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
          1 * n ^ (posBlocks C).card := by
      calc
        n ^ m * count = ∑ _α : Fin m → Fin n, count := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin]
        _ ≤ ∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
            1 * n ^ (posBlocks C).card := by
          apply Finset.sum_le_sum
          intro α _
          simpa using (alpha_extract hn hm G henc α).1
    have htot := le_trans hsum_c (hswap (fun _ => 1))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at htot
    exact Nat.le_of_mul_le_mul_left htot hnm_pos
  · have hsum_l : n ^ m * lits ≤
        ∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
          posCount C * n ^ (posBlocks C).card := by
      calc
        n ^ m * lits = ∑ _α : Fin m → Fin n, lits := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin]
        _ ≤ ∑ α : Fin m → Fin n, ∑ C ∈ G.filter (fun C => ¬ RawSat (xAssign α) C),
            posCount C * n ^ (posBlocks C).card := by
          apply Finset.sum_le_sum
          intro α _
          exact (alpha_extract hn hm G henc α).2.1
    have htot := le_trans hsum_l (hswap posCount)
    exact Nat.le_of_mul_le_mul_left htot hnm_pos
  · exact (alpha_extract hn hm G henc (fun _ => ⟨0, hn1⟩)).2.2

end PEqualNP.Outside.L_pcx_273_aux

theorem PEqualNP.Outside.L_pcx_273 :
∀ (n m a : ℕ), 2 ≤ n → 0 < m →
  let Raw := Fin m × Fin n
  let Var := Sum Raw (Fin a)
  let Cl := PEqualNP.ProofComplexity.Clause Var
  let enc := fun F : Finset Cl => ∀ x : Raw → Bool,
    (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
      ∃ z : Fin a → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x z) (↑F : Set _)
  let pos := fun C : Cl => (C.filter (fun l =>
    l.2 = true ∧ ∃ e : Raw, l.1 = Sum.inl e)).card
  let t := min m (2^a)
  let b := m / t
  let s := m % t
  let count := (t-s) * n^b + s * n^(b+1)
  let lits := (t-s) * b * n^b + s * (b+1) * n^(b+1)
  let width := (m+t-1) / t
  (∃ F : Finset Cl, enc F ∧ F.card = count ∧ (∑ C ∈ F, pos C) = lits ∧
    (∀ C ∈ F, pos C ≤ width) ∧
    ∀ C ∈ F, ∀ e : Raw, (Sum.inl e, false) ∉ C) ∧
  ∀ G : Finset Cl, enc G → count ≤ G.card ∧
    lits ≤ (∑ D ∈ G, pos D) ∧ ∃ D ∈ G, width ≤ pos D := by
  intro n m a hn hm
  dsimp only
  exact ⟨PEqualNP.Outside.L_pcx_273_aux.upper_bound hm,
         fun G henc => PEqualNP.Outside.L_pcx_273_aux.lower_bound hn hm G henc⟩

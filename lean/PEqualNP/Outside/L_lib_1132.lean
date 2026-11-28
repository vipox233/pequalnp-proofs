import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1132_aux

abbrev boundary {n m : Nat} (u v : Fin m → Fin n) (x : Finset (Fin m)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j =>
    ((x.filter (fun i => u i = j)).card + (x.filter (fun i => v i = j)).card) % 2 = 1)

abbrev crossing {n m : Nat} (u v : Fin m → Fin n) (U : Finset (Fin n)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => decide (u i ∈ U) != decide (v i ∈ U))

abbrev models {n m : Nat} (u v : Fin m → Fin n) (a : Finset (Fin n)) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun z => boundary u v z = a)

theorem card_symmDiff_mod2 {α : Type*} [DecidableEq α] (s t : Finset α) :
    (symmDiff s t).card % 2 = (s.card + t.card) % 2 := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = symmDiff s t ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at h1 h2; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1
  omega

theorem inter_symmDiff_eq {α : Type*} [DecidableEq α] (s t b : Finset α) :
    symmDiff s t ∩ b = symmDiff (s ∩ b) (t ∩ b) := by
  ext x; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto

theorem card_inter_symmDiff_mod2 {α : Type*} [DecidableEq α] (s t b : Finset α) :
    (symmDiff s t ∩ b).card % 2 = ((s ∩ b).card + (t ∩ b).card) % 2 := by
  rw [inter_symmDiff_eq, card_symmDiff_mod2]

theorem filter_symmDiff_eq {α : Type*} [DecidableEq α] (s t : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (symmDiff s t).filter p = symmDiff (s.filter p) (t.filter p) := by
  ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto

theorem boundary_empty {n m : Nat} (u v : Fin m → Fin n) : boundary u v ∅ = ∅ := by
  ext j; simp [boundary]

theorem boundary_symmDiff {n m : Nat} (u v : Fin m → Fin n) (x y : Finset (Fin m)) :
    boundary u v (symmDiff x y) = symmDiff (boundary u v x) (boundary u v y) := by
  ext j
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    filter_symmDiff_eq]
  have h1 := card_symmDiff_mod2 (x.filter (fun i => u i = j)) (y.filter (fun i => u i = j))
  have h2 := card_symmDiff_mod2 (x.filter (fun i => v i = j)) (y.filter (fun i => v i = j))
  omega

theorem boundary_singleton {n m : Nat} (u v : Fin m → Fin n) (i : Fin m) :
    boundary u v {i} = symmDiff ({u i} : Finset (Fin n)) {v i} := by
  ext j
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    Finset.mem_singleton]
  have h1 : (({i} : Finset (Fin m)).filter (fun k => u k = j)).card = if u i = j then 1 else 0 := by
    rw [Finset.filter_singleton]; split_ifs <;> simp
  have h2 : (({i} : Finset (Fin m)).filter (fun k => v k = j)).card = if v i = j then 1 else 0 := by
    rw [Finset.filter_singleton]; split_ifs <;> simp
  rw [h1, h2]
  by_cases hu : u i = j <;> by_cases hv : v i = j
  · simp [hu, hv]
  · simp [hu, hv, Ne.symm hv]
  · simp [hu, hv, Ne.symm hu]
  · simp [hu, hv, Ne.symm hu, Ne.symm hv]

theorem crossing_symmDiff {n m : Nat} (u v : Fin m → Fin n) (U W : Finset (Fin n)) :
    crossing u v (symmDiff U W) = symmDiff (crossing u v U) (crossing u v W) := by
  ext i
  simp only [crossing, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  by_cases h1 : u i ∈ U <;> by_cases h2 : v i ∈ U <;>
    by_cases h3 : u i ∈ W <;> by_cases h4 : v i ∈ W <;>
    simp [h1, h2, h3, h4]

theorem sum_mod2_eq_card_filter {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Nat) :
    (∑ x ∈ S, f x) % 2 = (S.filter (fun x => f x % 2 = 1)).card % 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [ha])]; omega
    · omega

theorem sum_card_fiber_eq {n m : Nat} (f : Fin m → Fin n) (z : Finset (Fin m)) (W : Finset (Fin n)) :
    (∑ j ∈ W, (z.filter (fun i => f i = j)).card) = (z.filter (fun i => f i ∈ W)).card := by
  have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := z.filter (fun i => f i ∈ W)) (t := W)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [h1]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hiz, hij⟩ => ⟨⟨hiz, hij ▸ hj⟩, hij⟩, fun ⟨⟨hiz, _⟩, hij⟩ => ⟨hiz, hij⟩⟩

theorem cut_boundary_parity {n m : Nat} (u v : Fin m → Fin n)
    (z : Finset (Fin m)) (W : Finset (Fin n)) :
    (boundary u v z ∩ W).card % 2 = (z ∩ crossing u v W).card % 2 := by
  have h1 : boundary u v z ∩ W = W.filter (fun j =>
      ((z.filter (fun i => u i = j)).card + (z.filter (fun i => v i = j)).card) % 2 = 1) := by
    ext j; simp only [boundary, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [h1, ← sum_mod2_eq_card_filter, Finset.sum_add_distrib,
    sum_card_fiber_eq u z W, sum_card_fiber_eq v z W, ← card_symmDiff_mod2]
  have h2 : symmDiff (z.filter (fun i => u i ∈ W)) (z.filter (fun i => v i ∈ W)) =
      z ∩ crossing u v W := by
    ext i
    simp only [crossing, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_inter,
      Finset.mem_univ, true_and]
    by_cases hu : u i ∈ W <;> by_cases hv : v i ∈ W <;> simp [hu, hv]
  rw [h2]

theorem minimal_cut_atomic {n m : Nat} (u v : Fin m → Fin n) (T : Finset (Fin m)) (d e U : Finset (Fin n))
    (hUT : crossing u v U ⊆ T) (hUpar : (d ∩ U).card % 2 ≠ (e ∩ U).card % 2)
    (hUmin : ∀ V : Finset (Fin n), crossing u v V ⊆ T → (d ∩ V).card % 2 ≠ (e ∩ V).card % 2 →
      (crossing u v U).card ≤ (crossing u v V).card)
    (W : Finset (Fin n)) (hWK : crossing u v W ⊆ crossing u v U) :
    crossing u v W = ∅ ∨ crossing u v W = crossing u v U := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hne0, hneK⟩ := hboth
  have hWT : crossing u v W ⊆ T := hWK.trans hUT
  by_cases hWpar : (d ∩ W).card % 2 ≠ (e ∩ W).card % 2
  · have hle := hUmin W hWT hWpar
    exact hneK (Finset.eq_of_subset_of_card_le hWK hle)
  · push Not at hWpar
    let V := symmDiff U W
    have hVcross : crossing u v V = crossing u v U \ crossing u v W := by
      rw [crossing_symmDiff]
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      exact ⟨fun h => h.elim id (fun ⟨h1, h2⟩ => (h2 (hWK h1)).elim), Or.inl⟩
    have hVT : crossing u v V ⊆ T := (hVcross ▸ Finset.sdiff_subset).trans hUT
    have hVpar : (d ∩ V).card % 2 ≠ (e ∩ V).card % 2 := by
      have hd := card_inter_symmDiff_mod2 U W d
      have he := card_inter_symmDiff_mod2 U W e
      rw [Finset.inter_comm] at hd he
      have hd' : (d ∩ V).card % 2 = ((d ∩ U).card + (d ∩ W).card) % 2 := by
        simpa [V, Finset.inter_comm] using hd
      have he' : (e ∩ V).card % 2 = ((e ∩ U).card + (e ∩ W).card) % 2 := by
        simpa [V, Finset.inter_comm] using he
      omega
    have hle := hUmin V hVT hVpar
    obtain ⟨i0, hi0⟩ := hne0
    have hlt : (crossing u v V).card < (crossing u v U).card := by
      rw [hVcross]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,
        fun heq => (Finset.mem_sdiff.mp (heq.symm ▸ hWK hi0)).2 hi0⟩)
    omega

def ReachOut {n m : Nat} (u v : Fin m → Fin n) (K : Finset (Fin m)) (a b : Fin n) : Prop :=
  ∃ z : Finset (Fin m), Disjoint z K ∧ boundary u v z = symmDiff ({a} : Finset (Fin n)) {b}

theorem reachOut_refl {n m : Nat} (u v : Fin m → Fin n) (K : Finset (Fin m)) (a : Fin n) :
    ReachOut u v K a a :=
  ⟨∅, Finset.disjoint_empty_left K, by simp [boundary_empty]⟩

theorem reachOut_symm {n m : Nat} {u v : Fin m → Fin n} {K : Finset (Fin m)} {a b : Fin n}
    (h : ReachOut u v K a b) : ReachOut u v K b a := by
  obtain ⟨z, hdz, hbz⟩ := h
  exact ⟨z, hdz, by rw [hbz, symmDiff_comm]⟩

theorem reachOut_trans {n m : Nat} {u v : Fin m → Fin n} {K : Finset (Fin m)} {a b c : Fin n}
    (h1 : ReachOut u v K a b) (h2 : ReachOut u v K b c) : ReachOut u v K a c := by
  obtain ⟨z1, hd1, hb1⟩ := h1
  obtain ⟨z2, hd2, hb2⟩ := h2
  refine ⟨symmDiff z1 z2, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hiK
    rcases Finset.mem_symmDiff.mp hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact Finset.disjoint_left.mp hd1 h hiK
    · exact Finset.disjoint_left.mp hd2 h hiK
  · rw [boundary_symmDiff, hb1, hb2]
    ext j
    simp only [Finset.mem_symmDiff, Finset.mem_singleton]
    tauto

theorem reachOut_edge {n m : Nat} (u v : Fin m → Fin n) (K : Finset (Fin m))
    {i : Fin m} (hi : i ∉ K) : ReachOut u v K (u i) (v i) :=
  ⟨{i}, Finset.disjoint_singleton_left.mpr hi, boundary_singleton u v i⟩

theorem reachOut_same_side {n m : Nat} {u v : Fin m → Fin n} {U : Finset (Fin n)}
    {a b : Fin n} (h : ReachOut u v (crossing u v U) a b) : a ∈ U ↔ b ∈ U := by
  obtain ⟨z, hdz, hbz⟩ := h
  have hp := cut_boundary_parity u v z U
  have h0 : z ∩ crossing u v U = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdz
  rw [h0, Finset.card_empty, hbz] at hp
  have h1 : (symmDiff ({a} : Finset (Fin n)) {b} ∩ U).card % 2 =
      ((({a} : Finset (Fin n)) ∩ U).card + (({b} : Finset (Fin n)) ∩ U).card) % 2 :=
    card_inter_symmDiff_mod2 {a} {b} U
  have ha : (({a} : Finset (Fin n)) ∩ U).card = if a ∈ U then 1 else 0 := by
    by_cases haU : a ∈ U
    · have : ({a} : Finset (Fin n)) ∩ U = {a} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, h ▸ haU⟩⟩
      rw [this]; simp [haU]
    · have : ({a} : Finset (Fin n)) ∩ U = ∅ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hx⟩; exact haU hx
      rw [this]; simp [haU]
  have hb : (({b} : Finset (Fin n)) ∩ U).card = if b ∈ U then 1 else 0 := by
    by_cases hbU : b ∈ U
    · have : ({b} : Finset (Fin n)) ∩ U = {b} := by
        ext x; simp only [Finset.mem_inter, Finset.mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hbU⟩⟩
      rw [this]; simp [hbU]
    · have : ({b} : Finset (Fin n)) ∩ U = ∅ := by
        ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hx⟩; exact hbU hx
      rw [this]; simp [hbU]
  rw [ha, hb] at h1
  by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU] at h1 hp ⊢ <;> omega

theorem exists_cycle_pair {n m : Nat} (u v : Fin m → Fin n) (U : Finset (Fin n))
    (hatom : ∀ W : Finset (Fin n), crossing u v W ⊆ crossing u v U →
      crossing u v W = ∅ ∨ crossing u v W = crossing u v U)
    {i j : Fin m} (hi : i ∈ crossing u v U) (hj : j ∈ crossing u v U) :
    ∃ z : Finset (Fin m), boundary u v z = ∅ ∧ z ∩ crossing u v U = symmDiff ({i} : Finset (Fin m)) {j} := by
  classical
  let K := crossing u v U
  by_cases hij : i = j
  · subst hij; exact ⟨∅, boundary_empty u v, by simp⟩
  have hi_xor : (u i ∈ U ∧ v i ∉ U) ∨ (u i ∉ U ∧ v i ∈ U) := by
    have h := (Finset.mem_filter.mp hi).2
    by_cases h1 : u i ∈ U <;> by_cases h2 : v i ∈ U <;> simp [h1, h2] at h ⊢
  have hj_xor : (u j ∈ U ∧ v j ∉ U) ∨ (u j ∉ U ∧ v j ∈ U) := by
    have h := (Finset.mem_filter.mp hj).2
    by_cases h1 : u j ∈ U <;> by_cases h2 : v j ∈ U <;> simp [h1, h2] at h ⊢
  let ai : Fin n := if u i ∈ U then u i else v i
  let bi : Fin n := if u i ∈ U then v i else u i
  let aj : Fin n := if u j ∈ U then u j else v j
  let bj : Fin n := if u j ∈ U then v j else u j
  have haiU : ai ∈ U := by dsimp [ai]; rcases hi_xor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hbiU : bi ∉ U := by dsimp [bi]; rcases hi_xor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hajU : aj ∈ U := by dsimp [aj]; rcases hj_xor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hbjU : bj ∉ U := by dsimp [bj]; rcases hj_xor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hbi_eq : boundary u v {i} = symmDiff ({ai} : Finset (Fin n)) {bi} := by
    rw [boundary_singleton]
    dsimp [ai, bi]
    split_ifs
    · rfl
    · exact symmDiff_comm _ _
  have hbj_eq : boundary u v {j} = symmDiff ({aj} : Finset (Fin n)) {bj} := by
    rw [boundary_singleton]
    dsimp [aj, bj]
    split_ifs
    · rfl
    · exact symmDiff_comm _ _
  have hreach_same : ∀ (p q : Fin n), (p ∈ U ↔ q ∈ U) →
      (p = ai ∨ p = bi) → (q = aj ∨ q = bj) → ReachOut u v K p q := by
    intro p q hpq hp hq
    let W := (Finset.univ : Finset (Fin n)).filter (fun w => ReachOut u v K p w)
    have hWK : crossing u v W ⊆ K := by
      intro e he
      by_contra heK
      have hr : ReachOut u v K (u e) (v e) := reachOut_edge u v K heK
      have hiff : u e ∈ W ↔ v e ∈ W := by
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => reachOut_trans h hr, fun h => reachOut_trans h (reachOut_symm hr)⟩
      have hc := (Finset.mem_filter.mp he).2
      by_cases hu : u e ∈ W
      · have hv := hiff.mp hu; simp [hu, hv] at hc
      · have hv : v e ∉ W := fun h => hu (hiff.mpr h); simp [hu, hv] at hc
    have hWside : ∀ w ∈ W, w ∈ U ↔ p ∈ U := by
      intro w hw
      exact (reachOut_same_side (Finset.mem_filter.mp hw).2).symm
    have hiW : i ∈ crossing u v W := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      rcases hp with rfl | rfl
      · have haW : ai ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachOut_refl u v K ai⟩
        have hbW : bi ∉ W := fun h => hbiU ((hWside bi h).mpr haiU)
        dsimp [ai, bi] at haW hbW
        split_ifs at haW hbW <;> simp [haW, hbW]
      · have hbW : bi ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachOut_refl u v K bi⟩
        have haW : ai ∉ W := fun h => hbiU ((hWside ai h).mp haiU)
        dsimp [ai, bi] at haW hbW
        split_ifs at haW hbW <;> simp [haW, hbW]
    have hWfull : crossing u v W = K := by
      rcases hatom W hWK with h0 | hfull
      · exact (Finset.notMem_empty i (h0 ▸ hiW)).elim
      · exact hfull
    have hjW : j ∈ crossing u v W := hWfull ▸ hj
    have hjc := (Finset.mem_filter.mp hjW).2
    have hqW : q ∈ W := by
      rcases hq with rfl | rfl
      · have hbjW : bj ∉ W := fun h => hbjU ((hWside bj h).mpr (hpq.mpr hajU))
        dsimp [aj, bj] at hbjW ⊢
        by_cases huj : u j ∈ U
        · simp only [huj, ↓reduceIte] at hbjW ⊢
          by_contra huW; simp [huW, hbjW] at hjc
        · simp only [huj, ↓reduceIte] at hbjW ⊢
          by_contra hvW; simp [hbjW, hvW] at hjc
      · have hajW : aj ∉ W := fun h => hbjU (hpq.mp ((hWside aj h).mp hajU))
        dsimp [aj, bj] at hajW ⊢
        by_cases huj : u j ∈ U
        · simp only [huj, ↓reduceIte] at hajW ⊢
          by_contra hvW; simp [hajW, hvW] at hjc
        · simp only [huj, ↓reduceIte] at hajW ⊢
          by_contra huW; simp [huW, hajW] at hjc
    exact (Finset.mem_filter.mp hqW).2
  obtain ⟨za, hdza, hbza⟩ := hreach_same ai aj (by simp [haiU, hajU]) (Or.inl rfl) (Or.inl rfl)
  obtain ⟨zb, hdzb, hbz_b⟩ := hreach_same bi bj (by simp [hbiU, hbjU]) (Or.inr rfl) (Or.inr rfl)
  let z := symmDiff (symmDiff za zb) (symmDiff ({i} : Finset (Fin m)) {j})
  refine ⟨z, ?_, ?_⟩
  · simp only [z, boundary_symmDiff, hbza, hbz_b, hbi_eq, hbj_eq]
    have hswap : ∀ (A B C D : Finset (Fin n)),
        symmDiff (symmDiff A B) (symmDiff C D) = symmDiff (symmDiff A C) (symmDiff B D) := by
      intro A B C D
      rw [symmDiff_assoc, ← symmDiff_assoc B C D, symmDiff_comm B C,
        symmDiff_assoc C B D, ← symmDiff_assoc A C (symmDiff B D)]
    rw [hswap {ai} {aj} {bi} {bj}, symmDiff_self]; rfl
  · simp only [z, inter_symmDiff_eq]
    have h1 : za ∩ K = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdza
    have h2 : zb ∩ K = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdzb
    have h3 : ({i} : Finset (Fin m)) ∩ K = {i} := by
      ext e; simp only [Finset.mem_inter, Finset.mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hi⟩⟩
    have h4 : ({j} : Finset (Fin m)) ∩ K = {j} := by
      ext e; simp only [Finset.mem_inter, Finset.mem_singleton]; exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hj⟩⟩
    rw [h1, h2, h3, h4]
    simp

theorem exists_cycle_of_even_subset {n m : Nat} (u v : Fin m → Fin n) (U : Finset (Fin n))
    (hatom : ∀ W : Finset (Fin n), crossing u v W ⊆ crossing u v U →
      crossing u v W = ∅ ∨ crossing u v W = crossing u v U)
    (S : Finset (Fin m)) (hSK : S ⊆ crossing u v U) (heven : S.card % 2 = 0) :
    ∃ z : Finset (Fin m), boundary u v z = ∅ ∧ z ∩ crossing u v U = S := by
  have hstrong : ∀ k : Nat, ∀ S : Finset (Fin m), S.card = k → S ⊆ crossing u v U →
      S.card % 2 = 0 → ∃ z : Finset (Fin m), boundary u v z = ∅ ∧ z ∩ crossing u v U = S := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro S hSk hSK hev
      by_cases hS0 : S = ∅
      · subst hS0; exact ⟨∅, boundary_empty u v, by simp⟩
      · obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
        have hge2 : 2 ≤ S.card := by omega
        have hne2 : (S.erase i).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hiS]; omega
        obtain ⟨j, hjS⟩ := hne2
        obtain ⟨hji, hjS'⟩ := Finset.mem_erase.mp hjS
        let S' := (S.erase i).erase j
        have hS'card : S'.card = k - 2 := by
          dsimp [S']
          rw [Finset.card_erase_of_mem hjS, Finset.card_erase_of_mem hiS]; omega
        have hS'sub : S' ⊆ crossing u v U :=
          (Finset.erase_subset _ _).trans ((Finset.erase_subset _ _).trans hSK)
        obtain ⟨z', hbz', hz'K⟩ := ih (k - 2) (by omega) S' hS'card hS'sub (by omega)
        obtain ⟨zij, hbzij, hzijK⟩ := exists_cycle_pair u v U hatom (hSK hiS) (hSK hjS')
        refine ⟨symmDiff z' zij, ?_, ?_⟩
        · rw [boundary_symmDiff, hbz', hbzij]; simp
        · rw [inter_symmDiff_eq, hz'K, hzijK]
          ext e
          simp only [S', Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
          by_cases hei : e = i
          · subst hei; simp [hiS, hji.symm]
          · by_cases hej : e = j
            · subst hej; simp [hjS', hji]
            · simp [hei, hej]
  exact hstrong S.card S rfl hSK heven

theorem card_even_powerset {α : Type*} [DecidableEq α] (K : Finset α) (hne : K.Nonempty) :
    (K.powerset.filter (fun S => S.card % 2 = 0)).card = 2 ^ (K.card - 1) := by
  obtain ⟨i0, hi0⟩ := hne
  let Ev := K.powerset.filter (fun S => S.card % 2 = 0)
  let Od := K.powerset.filter (fun S => S.card % 2 = 1)
  have hbij : Ev.card = Od.card := by
    refine Finset.card_bij (fun S _ => symmDiff S {i0}) ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSp, hSe⟩ := Finset.mem_filter.mp hS
      have hSK := Finset.mem_powerset.mp hSp
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_symmDiff.mp hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact hSK h
        · exact (Finset.mem_singleton.mp h) ▸ hi0
      · have hc := card_symmDiff_mod2 S {i0}
        rw [Finset.card_singleton] at hc; omega
    · intro S1 _ S2 _ heq
      have h := congrArg (fun S => symmDiff S {i0}) heq
      simpa [symmDiff_assoc] using h
    · intro S hS
      obtain ⟨hSp, hSo⟩ := Finset.mem_filter.mp hS
      have hSK := Finset.mem_powerset.mp hSp
      refine ⟨symmDiff S {i0}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, by simp⟩
      · intro x hx
        rcases Finset.mem_symmDiff.mp hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact hSK h
        · exact (Finset.mem_singleton.mp h) ▸ hi0
      · have hc := card_symmDiff_mod2 S {i0}
        rw [Finset.card_singleton] at hc; omega
  have hdisj : Disjoint Ev Od := by
    rw [Finset.disjoint_left]; intro S h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    omega
  have hunion : Ev ∪ Od = K.powerset := by
    ext S; simp only [Ev, Od, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : S.card % 2 = 0
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, by omega⟩
  have hsum : Ev.card + Od.card = 2 ^ K.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_powerset]
  have hpos : 1 ≤ K.card := Finset.card_pos.mpr ⟨i0, hi0⟩
  have hpow : 2 ^ K.card = 2 * 2 ^ (K.card - 1) := by
    have hk : K.card = (K.card - 1) + 1 := by omega
    conv_lhs => rw [hk, pow_succ]
    ring
  change Ev.card = 2 ^ (K.card - 1)
  omega

theorem sum_powerset_neg_one {α : Type*} [DecidableEq α] (B : Finset α) (hne : B.Nonempty) :
    B.powerset.sum (fun R => (-1 : Int) ^ R.card) = 0 := by
  obtain ⟨i0, hi0⟩ := hne
  let Ev := B.powerset.filter (fun R => R.card % 2 = 0)
  let Od := B.powerset.filter (fun R => R.card % 2 = 1)
  have hdisj : Disjoint Ev Od := by
    rw [Finset.disjoint_left]; intro S h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2; omega
  have hunion : Ev ∪ Od = B.powerset := by
    ext S; simp only [Ev, Od, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : S.card % 2 = 0
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, by omega⟩
  rw [← hunion, Finset.sum_union hdisj]
  have hEv : Ev.sum (fun R => (-1 : Int) ^ R.card) = (Ev.card : Int) := by
    have h1 : ∀ R ∈ Ev, (-1 : Int) ^ R.card = 1 := by
      intro R hR
      have he : Even R.card := Nat.even_iff.mpr (Finset.mem_filter.mp hR).2
      exact Even.neg_one_pow he
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hOd : Od.sum (fun R => (-1 : Int) ^ R.card) = -(Od.card : Int) := by
    have h1 : ∀ R ∈ Od, (-1 : Int) ^ R.card = -1 := by
      intro R hR
      have ho : Odd R.card := Nat.odd_iff.mpr (Finset.mem_filter.mp hR).2
      exact Odd.neg_one_pow ho
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard : Ev.card = Od.card := by
    have h1 : Ev.card = 2 ^ (B.card - 1) := card_even_powerset B ⟨i0, hi0⟩
    have hsum : Ev.card + Od.card = 2 ^ B.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_powerset]
    have hpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨i0, hi0⟩
    have hpow : 2 ^ B.card = 2 * 2 ^ (B.card - 1) := by
      have hk : B.card = (B.card - 1) + 1 := by omega
      conv_lhs => rw [hk, pow_succ]
      ring
    omega
  rw [hEv, hOd, hcard]
  ring

theorem sum_neg_one_good {m : Nat} (x : Finset (Fin m)) (P : Finset (Finset (Fin m)))
    (hne : ∀ B ∈ P, B.Nonempty)
    (hdisj : Set.PairwiseDisjoint (P : Set (Finset (Fin m))) id) :
    ((P.biUnion id).powerset.filter (fun S => ∀ B ∈ P, S ∩ B ≠ x ∩ B)).sum
      (fun S => (-1 : Int) ^ S.card) =
    (-1 : Int) ^ P.card * (-1 : Int) ^ (x ∩ P.biUnion id).card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert B P' hBP' ih =>
    have hne' : ∀ B' ∈ P', B'.Nonempty := fun B' hB' => hne B' (Finset.mem_insert_of_mem hB')
    have hdisj' : Set.PairwiseDisjoint (P' : Set (Finset (Fin m))) id :=
      hdisj.subset (Finset.subset_insert B P')
    have hBK' : Disjoint B (P'.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro B' hB'
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self B P'))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hB')) (fun h => hBP' (h ▸ hB'))
    let K' := P'.biUnion id
    have hbiU : (insert B P').biUnion id = B ∪ K' := by simp [K']
    let G1 := B.powerset.erase (x ∩ B)
    let G2 := K'.powerset.filter (fun S' => ∀ B' ∈ P', S' ∩ B' ≠ x ∩ B')
    let Gall := (B ∪ K').powerset.filter (fun S => ∀ B' ∈ insert B P', S ∩ B' ≠ x ∩ B')
    have hsum_eq : Gall.sum (fun S => (-1 : Int) ^ S.card) =
        (G1 ×ˢ G2).sum (fun p => (-1 : Int) ^ (p.1 ∪ p.2).card) := by
      symm
      refine Finset.sum_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
      · rintro ⟨R, S'⟩ hp
        obtain ⟨hR, hS'⟩ := Finset.mem_product.mp hp
        obtain ⟨hRne, hRp⟩ := Finset.mem_erase.mp hR
        obtain ⟨hS'p, hS'good⟩ := Finset.mem_filter.mp hS'
        have hRB := Finset.mem_powerset.mp hRp
        have hS'K := Finset.mem_powerset.mp hS'p
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset_union hRB hS'K), ?_⟩
        intro B' hB'
        rcases Finset.mem_insert.mp hB' with hEq | hB'P
        · rw [hEq]
          have heq : (R ∪ S') ∩ B = R := by
            ext e; simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨heR | heS', heB⟩
              · exact heR
              · exact (Finset.disjoint_left.mp hBK' heB (hS'K heS')).elim
            · intro heR; exact ⟨Or.inl heR, hRB heR⟩
          rw [heq]; exact hRne
        · have hB'K : B' ⊆ K' := Finset.subset_biUnion_of_mem id hB'P
          have heq : (R ∪ S') ∩ B' = S' ∩ B' := by
            ext e; simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨heR | heS', heB'⟩
              · exact (Finset.disjoint_left.mp hBK' (hRB heR) (hB'K heB')).elim
              · exact ⟨heS', heB'⟩
            · rintro ⟨heS', heB'⟩; exact ⟨Or.inr heS', heB'⟩
          rw [heq]; exact hS'good B' hB'P
      · rintro ⟨R1, S1⟩ hp1 ⟨R2, S2⟩ hp2 heq
        have hR1 : R1 ⊆ B := Finset.mem_powerset.mp (Finset.mem_erase.mp (Finset.mem_product.mp hp1).1).2
        have hS1 : S1 ⊆ K' := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp1).2).1
        have hR2 : R2 ⊆ B := Finset.mem_powerset.mp (Finset.mem_erase.mp (Finset.mem_product.mp hp2).1).2
        have hS2 : S2 ⊆ K' := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp2).2).1
        apply Prod.ext
        · ext e
          constructor <;> intro he
          · have h1 : e ∈ R2 ∪ S2 := heq ▸ Finset.mem_union_left _ he
            rcases Finset.mem_union.mp h1 with h | h
            · exact h
            · exact (Finset.disjoint_left.mp hBK' (hR1 he) (hS2 h)).elim
          · have h1 : e ∈ R1 ∪ S1 := heq.symm ▸ Finset.mem_union_left _ he
            rcases Finset.mem_union.mp h1 with h | h
            · exact h
            · exact (Finset.disjoint_left.mp hBK' (hR2 he) (hS1 h)).elim
        · ext e
          constructor <;> intro he
          · have h1 : e ∈ R2 ∪ S2 := heq ▸ Finset.mem_union_right _ he
            rcases Finset.mem_union.mp h1 with h | h
            · exact (Finset.disjoint_left.mp hBK' (hR2 h) (hS1 he)).elim
            · exact h
          · have h1 : e ∈ R1 ∪ S1 := heq.symm ▸ Finset.mem_union_right _ he
            rcases Finset.mem_union.mp h1 with h | h
            · exact (Finset.disjoint_left.mp hBK' (hR1 h) (hS2 he)).elim
            · exact h
      · intro S hS
        obtain ⟨hSp, hSgood⟩ := Finset.mem_filter.mp hS
        have hSsub := Finset.mem_powerset.mp hSp
        refine ⟨(S ∩ B, S ∩ K'), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_erase.mpr ⟨hSgood B (Finset.mem_insert_self B P'),
            Finset.mem_powerset.mpr Finset.inter_subset_right⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
          intro B' hB'
          have hB'K : B' ⊆ K' := Finset.subset_biUnion_of_mem id hB'
          have heq : (S ∩ K') ∩ B' = S ∩ B' := by
            ext e; simp only [Finset.mem_inter]
            exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, hB'K h2⟩, h2⟩⟩
          rw [heq]; exact hSgood B' (Finset.mem_insert_of_mem hB')
        · ext e; simp only [Finset.mem_union, Finset.mem_inter]
          exact ⟨fun h => h.elim And.left And.left,
            fun he => (Finset.mem_union.mp (hSsub he)).elim (fun hb => Or.inl ⟨he, hb⟩) (fun hk => Or.inr ⟨he, hk⟩)⟩
      · intro p _; rfl
    have hprod : (G1 ×ˢ G2).sum (fun p => (-1 : Int) ^ (p.1 ∪ p.2).card) =
        G1.sum (fun R => (-1 : Int) ^ R.card) * G2.sum (fun S' => (-1 : Int) ^ S'.card) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R hR
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S' hS'
      have hRB : R ⊆ B := Finset.mem_powerset.mp (Finset.mem_erase.mp hR).2
      have hS'K : S' ⊆ K' := Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1
      have hd : Disjoint R S' := (hBK'.mono_left hRB).mono_right hS'K
      rw [Finset.card_union_of_disjoint hd, pow_add]
    have hG1 : G1.sum (fun R => (-1 : Int) ^ R.card) = -((-1 : Int) ^ (x ∩ B).card) := by
      have hmem : x ∩ B ∈ B.powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
      have h0 := sum_powerset_neg_one B (hne B (Finset.mem_insert_self B P'))
      have hadd := Finset.add_sum_erase B.powerset (fun R => (-1 : Int) ^ R.card) hmem
      change (-1 : Int) ^ (x ∩ B).card + G1.sum (fun R => (-1 : Int) ^ R.card) = _ at hadd
      omega
    have hcard_x : (x ∩ (B ∪ K')).card = (x ∩ B).card + (x ∩ K').card := by
      rw [Finset.inter_union_distrib_left]
      exact Finset.card_union_of_disjoint
        ((hBK'.mono_left Finset.inter_subset_right).mono_right Finset.inter_subset_right)
    rw [hbiU]
    change Gall.sum (fun S => (-1 : Int) ^ S.card) = _
    rw [hsum_eq, hprod, hG1, ih hne' hdisj', Finset.card_insert_of_notMem hBP', hcard_x,
      pow_succ, pow_add]
    ring

theorem main : ∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)),
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))


  ∀ (d e : Finset (Fin n)) (x : Finset (Fin m)), boundary x = d →
    (∃ y ∈ cube, boundary y = e) →
    let odd := fun (U : Finset (Fin n)) =>
      crossing U ⊆ T ∧ (d ∩ U).card % 2 ≠ (e ∩ U).card % 2
    ∀ U ∈ vertices, odd U → (∀ V ∈ vertices, odd V → (crossing U).card ≤ (crossing V).card) →
      let K := crossing U
      ∀ packets : Finset (Finset (Fin m)),
        (∀ B ∈ packets, B.Nonempty ∧ B ⊆ K) →
        (∀ j ∈ K, ∃! B : Finset (Fin m), B ∈ packets ∧ j ∈ B) →
        let accept := fun (z : Finset (Fin m)) => ∀ B ∈ packets, z ∩ B ≠ x ∩ B
        let models := fun (a : Finset (Fin n)) => cube.filter (fun z => boundary z = a)
        let lhs := ((models d).filter accept).card
        let rhs := ((models e).filter accept).card
        (2 : Int) ^ (K.card - 1) * ((lhs : Int) - (rhs : Int)) =
          (-1 : Int) ^ packets.card * ((models d).card : Int) := by
  classical
  intro n m u v T cube0 verts0 bd0 cr0 d e x hbx ⟨y, _, hby⟩ odd0 U _ hUodd hUmin K packets hpack_sub hpack_part accept0 mods0 lhs0 rhs0
  have hatom : ∀ W : Finset (Fin n), crossing u v W ⊆ crossing u v U →
      crossing u v W = ∅ ∨ crossing u v W = crossing u v U :=
    minimal_cut_atomic u v T d e U hUodd.1 hUodd.2 (fun V hVT hVp => hUmin V (Finset.mem_univ V) ⟨hVT, hVp⟩)
  have hbx' : boundary u v x = d := hbx
  have hby' : boundary u v y = e := hby
  have hxd_par : (x ∩ K).card % 2 = (d ∩ U).card % 2 := by
    have := cut_boundary_parity u v x U; rw [hbx'] at this; exact this.symm
  have hye_par : (y ∩ K).card % 2 = (e ∩ U).card % 2 := by
    have := cut_boundary_parity u v y U; rw [hby'] at this; exact this.symm
  have hKne : K.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h1 : (x ∩ K).card = 0 := by simp [hemp]
    have h2 : (y ∩ K).card = 0 := by simp [hemp]
    have hpar := hUodd.2
    omega
  -- F0 = cycles disjoint from K
  let F0 := (models u v ∅).filter (fun z => z ∩ K = ∅)
  let c0 := F0.card
  -- For any target a with boundary w = a, every S in K.powerset with S.card % 2 = (w ∩ K).card % 2 has fiber size c0!
  have hfiber_gen : ∀ (a : Finset (Fin n)) (w : Finset (Fin m)), boundary u v w = a →
      ∀ S ∈ K.powerset,
        ((models u v a).filter (fun z => z ∩ K = S)).card =
          if S.card % 2 = (w ∩ K).card % 2 then c0 else 0 := by
    intro a w hbw S hSp
    have hSK : S ⊆ K := Finset.mem_powerset.mp hSp
    split_ifs with hpar
    · let S0 := symmDiff S (w ∩ K)
      have hS0K : S0 ⊆ K := by
        intro i hi
        rcases Finset.mem_symmDiff.mp hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact hSK h
        · exact (Finset.mem_inter.mp h).2
      have hS0ev : S0.card % 2 = 0 := by
        have hc := card_symmDiff_mod2 S (w ∩ K); dsimp only [S0]; omega
      obtain ⟨z0, hbz0, hz0K⟩ := exists_cycle_of_even_subset u v U hatom S0 hS0K hS0ev
      let z_base := symmDiff z0 w
      have hbz_base : boundary u v z_base = a := by
        rw [boundary_symmDiff, hbz0, hbw]; simp
      have hz_baseK : z_base ∩ K = S := by
        rw [inter_symmDiff_eq, hz0K]
        simp [S0]
      symm
      refine Finset.card_bij (fun z _ => symmDiff z z_base) ?_ ?_ ?_
      · intro z hz
        obtain ⟨hzmod, hzK⟩ := Finset.mem_filter.mp hz
        have hbz : boundary u v z = ∅ := (Finset.mem_filter.mp hzmod).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [boundary_symmDiff, hbz, hbz_base]; simp
        · rw [inter_symmDiff_eq, hzK, hz_baseK]; simp
      · intro z1 _ z2 _ heq
        have h := congrArg (fun t => symmDiff t z_base) heq
        simpa [symmDiff_assoc] using h
      · intro z hz
        obtain ⟨hzmod, hzK⟩ := Finset.mem_filter.mp hz
        have hbz : boundary u v z = a := (Finset.mem_filter.mp hzmod).2
        refine ⟨symmDiff z z_base, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩, by simp⟩
        · rw [boundary_symmDiff, hbz, hbz_base]; simp
        · rw [inter_symmDiff_eq, hzK, hz_baseK]; simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hzmod hzK
      have hbz : boundary u v z = a := (Finset.mem_filter.mp hzmod).2
      have hp1 := cut_boundary_parity u v z U
      have hp2 := cut_boundary_parity u v w U
      rw [hbz] at hp1; rw [hbw] at hp2
      change (a ∩ U).card % 2 = (z ∩ K).card % 2 at hp1
      change (a ∩ U).card % 2 = (w ∩ K).card % 2 at hp2
      rw [hzK] at hp1
      exact hpar (hp1.symm.trans hp2)
  -- Card of models d = c0 * 2^(K.card - 1)
  have hmod_d : (models u v d).card = c0 * 2 ^ (K.card - 1) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun z => z ∩ K)
      (s := models u v d) (t := K.powerset) (fun z _ => Finset.mem_powerset.mpr Finset.inter_subset_right)
    rw [h1]
    have h2 : ∑ S ∈ K.powerset, ((models u v d).filter (fun z => z ∩ K = S)).card =
        ∑ S ∈ K.powerset, if S.card % 2 = (x ∩ K).card % 2 then c0 else 0 :=
      Finset.sum_congr rfl (fun S hS => hfiber_gen d x hbx S hS)
    rw [h2, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hpar_card : (K.powerset.filter (fun S => S.card % 2 = (x ∩ K).card % 2)).card =
        2 ^ (K.card - 1) := by
      by_cases hx0 : (x ∩ K).card % 2 = 0
      · simp only [hx0]; exact card_even_powerset K hKne
      · have hx1 : (x ∩ K).card % 2 = 1 := by omega
        simp only [hx1]
        have hev := card_even_powerset K hKne
        have hdisj : Disjoint (K.powerset.filter (fun S => S.card % 2 = 0))
            (K.powerset.filter (fun S => S.card % 2 = 1)) := by
          rw [Finset.disjoint_left]; intro S h1 h2
          have a := (Finset.mem_filter.mp h1).2; have b := (Finset.mem_filter.mp h2).2; omega
        have hunion : K.powerset.filter (fun S => S.card % 2 = 0) ∪
            K.powerset.filter (fun S => S.card % 2 = 1) = K.powerset := by
          ext S; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            by_cases he : S.card % 2 = 0
            · exact Or.inl ⟨h, he⟩
            · exact Or.inr ⟨h, by omega⟩
        have hsum := Finset.card_union_of_disjoint hdisj
        rw [hunion, Finset.card_powerset] at hsum
        have hpos : 1 ≤ K.card := Finset.card_pos.mpr hKne
        have hpow : 2 ^ K.card = 2 * 2 ^ (K.card - 1) := by
          have hk : K.card = (K.card - 1) + 1 := by omega
          conv_lhs => rw [hk, pow_succ]
          ring
        omega
    rw [hpar_card, mul_comm]
  -- Partition properties of packets
  have hpack_biU : packets.biUnion id = K := by
    ext j
    simp only [Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨B, hBp, hjB⟩; exact (hpack_sub B hBp).2 hjB
    · intro hjK; obtain ⟨B, ⟨hBp, hjB⟩, _⟩ := hpack_part j hjK; exact ⟨B, hBp, hjB⟩
  have hpack_disj : Set.PairwiseDisjoint (packets : Set (Finset (Fin m))) id := by
    intro B1 hB1 B2 hB2 hne
    change Disjoint B1 B2
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hjK : j ∈ K := (hpack_sub B1 hB1).2 hj1
    obtain ⟨B, _, huniq⟩ := hpack_part j hjK
    exact hne ((huniq B1 ⟨hB1, hj1⟩).trans (huniq B2 ⟨hB2, hj2⟩).symm)
  let goodS := K.powerset.filter (fun S => ∀ B ∈ packets, S ∩ B ≠ x ∩ B)
  -- Express lhs and rhs via goodS
  have haccept_K : ∀ z : Finset (Fin m), accept0 z ↔ (z ∩ K) ∈ goodS := by
    intro z
    simp only [accept0, goodS, Finset.mem_filter, Finset.mem_powerset, Finset.inter_subset_right, true_and]
    apply forall₂_congr
    intro B hBp
    have hBK : B ⊆ K := (hpack_sub B hBp).2
    have h1 : (z ∩ K) ∩ B = z ∩ B := by
      ext i; simp only [Finset.mem_inter]
      exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, hBK h2⟩, h2⟩⟩
    rw [h1]
  have hcard_acc : ∀ (a : Finset (Fin n)) (w : Finset (Fin m)), boundary u v w = a →
      ((models u v a).filter accept0).card =
        c0 * (goodS.filter (fun S => S.card % 2 = (w ∩ K).card % 2)).card := by
    intro a w hbw
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun z => z ∩ K)
      (s := (models u v a).filter accept0) (t := goodS)
      (fun z hz => (haccept_K z).mp (Finset.mem_filter.mp hz).2)
    rw [h1]
    have h2 : ∑ S ∈ goodS, (((models u v a).filter accept0).filter (fun z => z ∩ K = S)).card =
        ∑ S ∈ goodS, if S.card % 2 = (w ∩ K).card % 2 then c0 else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hfeq : ((models u v a).filter accept0).filter (fun z => z ∩ K = S) =
          (models u v a).filter (fun z => z ∩ K = S) := by
        ext z; simp only [Finset.mem_filter]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, (haccept_K z).mpr (h2 ▸ hS)⟩, h2⟩⟩
      rw [hfeq]
      exact hfiber_gen a w hbw S (Finset.mem_filter.mp hS).1
    rw [h2, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hlhs : ((models u v d).filter accept0).card =
      c0 * (goodS.filter (fun S => S.card % 2 = (x ∩ K).card % 2)).card :=
    hcard_acc d x hbx
  have hrhs : ((models u v e).filter accept0).card =
      c0 * (goodS.filter (fun S => S.card % 2 ≠ (x ∩ K).card % 2)).card := by
    rw [hcard_acc e y hby]
    congr 2
    apply Finset.filter_congr
    intro S _
    have hne_par : (y ∩ K).card % 2 ≠ (x ∩ K).card % 2 := by
      have hU := hUodd.2; omega
    omega
  -- Compute signed difference of goodS!
  have hdiff_good :
      ((goodS.filter (fun S => S.card % 2 = (x ∩ K).card % 2)).card : Int) -
      ((goodS.filter (fun S => S.card % 2 ≠ (x ∩ K).card % 2)).card : Int) =
      (-1 : Int) ^ (x ∩ K).card * goodS.sum (fun S => (-1 : Int) ^ S.card) := by
    let Gsame := goodS.filter (fun S => S.card % 2 = (x ∩ K).card % 2)
    let Gdiff := goodS.filter (fun S => S.card % 2 ≠ (x ∩ K).card % 2)
    have hdisj : Disjoint Gsame Gdiff := by
      rw [Finset.disjoint_left]; intro S h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : Gsame ∪ Gdiff = goodS := by
      ext S; simp only [Gsame, Gdiff, Finset.mem_union, Finset.mem_filter]
      by_cases h : S.card % 2 = (x ∩ K).card % 2 <;> simp [h]
    have hsum : goodS.sum (fun S => (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ S.card) =
        (Gsame.card : Int) - (Gdiff.card : Int) := by
      rw [← hunion, Finset.sum_union hdisj]
      have h1 : Gsame.sum (fun S => (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ S.card) = (Gsame.card : Int) := by
        have hc : ∀ S ∈ Gsame, (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ S.card = 1 := by
          intro S hS
          rw [← pow_add]
          have heq := (Finset.mem_filter.mp hS).2
          exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : Gdiff.sum (fun S => (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ S.card) = -(Gdiff.card : Int) := by
        have hc : ∀ S ∈ Gdiff, (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ S.card = -1 := by
          intro S hS
          rw [← pow_add]
          have hne := (Finset.mem_filter.mp hS).2
          exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [h1, h2]; ring
    rw [Finset.mul_sum, hsum]
  have hsum_good : goodS.sum (fun S => (-1 : Int) ^ S.card) =
      (-1 : Int) ^ packets.card * (-1 : Int) ^ (x ∩ K).card := by
    have h := sum_neg_one_good x packets (fun B hB => (hpack_sub B hB).1) hpack_disj
    rwa [hpack_biU] at h
  have hsq : (-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ (x ∩ K).card = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  have hdiff_final : ((lhs0 : Int) - (rhs0 : Int)) = (c0 : Int) * (-1 : Int) ^ packets.card := by
    change (((models u v d).filter accept0).card : Int) - (((models u v e).filter accept0).card : Int) = _
    rw [hlhs, hrhs]
    push_cast
    rw [← mul_sub, hdiff_good, hsum_good]
    calc
      (c0 : Int) * ((-1 : Int) ^ (x ∩ K).card * ((-1 : Int) ^ packets.card * (-1 : Int) ^ (x ∩ K).card))
          = (c0 : Int) * (-1 : Int) ^ packets.card * ((-1 : Int) ^ (x ∩ K).card * (-1 : Int) ^ (x ∩ K).card) := by ring
      _ = (c0 : Int) * (-1 : Int) ^ packets.card := by rw [hsq, mul_one]
  change (2 : Int) ^ (K.card - 1) * ((lhs0 : Int) - (rhs0 : Int)) =
    (-1 : Int) ^ packets.card * ((models u v d).card : Int)
  rw [hdiff_final, hmod_d]
  push_cast
  ring

end PEqualNP.Outside.L_lib_1132_aux

theorem PEqualNP.Outside.L_lib_1132 : ∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)),
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))


  ∀ (d e : Finset (Fin n)) (x : Finset (Fin m)), boundary x = d →
    (∃ y ∈ cube, boundary y = e) →
    let odd := fun (U : Finset (Fin n)) =>
      crossing U ⊆ T ∧ (d ∩ U).card % 2 ≠ (e ∩ U).card % 2
    ∀ U ∈ vertices, odd U → (∀ V ∈ vertices, odd V → (crossing U).card ≤ (crossing V).card) →
      let K := crossing U
      ∀ packets : Finset (Finset (Fin m)),
        (∀ B ∈ packets, B.Nonempty ∧ B ⊆ K) →
        (∀ j ∈ K, ∃! B : Finset (Fin m), B ∈ packets ∧ j ∈ B) →
        let accept := fun (z : Finset (Fin m)) => ∀ B ∈ packets, z ∩ B ≠ x ∩ B
        let models := fun (a : Finset (Fin n)) => cube.filter (fun z => boundary z = a)
        let lhs := ((models d).filter accept).card
        let rhs := ((models e).filter accept).card
        (2 : Int) ^ (K.card - 1) * ((lhs : Int) - (rhs : Int)) =
          (-1 : Int) ^ packets.card * ((models d).card : Int) :=
  PEqualNP.Outside.L_lib_1132_aux.main

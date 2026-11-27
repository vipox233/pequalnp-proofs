import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25513_aux

def sigs {n : ℕ} (rows cols : Finset (Fin n)) (u v : Fin n) : Finset (Fin 3 × Fin n) :=
  (Finset.univ : Finset (Fin 3 × Fin n)).filter (fun s =>
      if s.1 = 0 then s.2 = u ∨ s.2 = v
      else if s.1 = 1 then s.2 ∈ rows ∧ s.2 = u
      else s.2 ∈ cols ∧ s.2 = v)

lemma mem0 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((0 : Fin 3), a) ∈ sigs rows cols u v ↔ (a = u ∨ a = v) := by
  simp [sigs]

lemma mem1 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((1 : Fin 3), a) ∈ sigs rows cols u v ↔ (a ∈ rows ∧ a = u) := by
  simp [sigs]

lemma mem2 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((2 : Fin 3), a) ∈ sigs rows cols u v ↔ (a ∈ cols ∧ a = v) := by
  simp [sigs]

lemma sigs_swap {n : ℕ} (rows cols : Finset (Fin n)) (i j : Fin n)
    (hi : i ∉ rows) (hj : j ∉ cols) (hj' : j ∉ rows) (hi' : i ∉ cols) :
    sigs rows cols i j = sigs rows cols j i := by
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  ext ⟨k, a⟩
  rcases hk k with rfl | rfl | rfl
  · rw [mem0, mem0]
    exact or_comm
  · rw [mem1, mem1]
    constructor
    · rintro ⟨h, rfl⟩
      exact absurd h hi
    · rintro ⟨h, rfl⟩
      exact absurd h hj'
  · rw [mem2, mem2]
    constructor
    · rintro ⟨h, rfl⟩
      exact absurd h hj
    · rintro ⟨h, rfl⟩
      exact absurd h hi'

def tm {n : ℕ} (rows cols : Finset (Fin n)) (a b : Fin n) :
    (Fin 3 × Fin n) × (Fin 3 × Fin n) :=
  if a ∈ rows then ((1, a), (0, b))
  else if b ∈ cols then ((0, a), (2, b))
  else ((0, a), (0, b))

def tag {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n) : ℕ :=
  if G a b = true then
    (if a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true) then 0 else 1)
  else (if a = b then 3 else 2)

def isOn {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n) : Prop :=
  (tm rows cols a b).1 ∈ sigs rows cols u v ∧ (tm rows cols a b).2 ∈ sigs rows cols u v

lemma isOn_self {n : ℕ} (rows cols : Finset (Fin n)) (u v : Fin n) :
    isOn rows cols u v u v := by
  unfold isOn tm
  split_ifs with h1 h2
  · exact ⟨(mem1 rows cols u u v).mpr ⟨h1, rfl⟩, (mem0 rows cols v u v).mpr (Or.inr rfl)⟩
  · exact ⟨(mem0 rows cols u u v).mpr (Or.inl rfl), (mem2 rows cols v u v).mpr ⟨h2, rfl⟩⟩
  · exact ⟨(mem0 rows cols u u v).mpr (Or.inl rfl), (mem0 rows cols v u v).mpr (Or.inr rfl)⟩

lemma isOn_gen {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n)
    (h : isOn rows cols a b u v) : (a = u ∨ a = v) ∧ (b = u ∨ b = v) := by
  unfold isOn tm at h
  split_ifs at h with h1 h2
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem1 rows cols a u v).mp h3
    have h4' := (mem0 rows cols b u v).mp h4
    exact ⟨Or.inl h3'.2, h4'⟩
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem0 rows cols a u v).mp h3
    have h4' := (mem2 rows cols b u v).mp h4
    exact ⟨h3', Or.inr h4'.2⟩
  · obtain ⟨h3, h4⟩ := h
    exact ⟨(mem0 rows cols a u v).mp h3, (mem0 rows cols b u v).mp h4⟩

lemma isOn_X {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n)
    (h : isOn rows cols a b u v) (hab : a ≠ b) (hX : a ∈ rows ∨ b ∈ cols) :
    a = u ∧ b = v := by
  unfold isOn tm at h
  split_ifs at h with h1 h2
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem1 rows cols a u v).mp h3
    have h4' := (mem0 rows cols b u v).mp h4
    rcases h4' with h5 | h5
    · exact absurd (h3'.2.trans h5.symm) hab
    · exact ⟨h3'.2, h5⟩
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem0 rows cols a u v).mp h3
    have h4' := (mem2 rows cols b u v).mp h4
    rcases h3' with h5 | h5
    · exact ⟨h5, h4'.2⟩
    · exact absurd (h5.trans h4'.2.symm) hab
  · rcases hX with hX | hX
    · exact absurd hX h1
    · exact absurd hX h2

lemma tag0 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 0) :
    G a b = true ∧ a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true) := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h2⟩

lemma tag1 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 1) :
    G a b = true ∧ ¬ (a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true)) := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  all_goals first | exact ⟨h1, h2⟩ | omega

lemma tag2 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 2) :
    G a b = false ∧ a ≠ b := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  all_goals first | omega | exact ⟨by simpa using h1, by assumption⟩

lemma tag2' {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (hG : G a b = false) (hab : a ≠ b) : tag G rows cols a b = 2 := by
  unfold tag
  split_ifs with h1 h2
  all_goals first | rfl | exact absurd h1 (by simp [hG])

lemma tag01 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (hG : G a b = true) : tag G rows cols a b = 0 ∨ tag G rows cols a b = 1 := by
  unfold tag
  split_ifs with h1
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

lemma correct {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n))
    (hcov : ∀ i j, G i j = true → G j i = false → i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols)
    (u v : Fin n) :
    G u v = true ↔ ((∃ a b, tag G rows cols a b = 0 ∧ isOn rows cols a b u v) ∨
      ((∃ a b, tag G rows cols a b = 1 ∧ isOn rows cols a b u v) ∧
        ¬ ∃ a b, tag G rows cols a b = 2 ∧ isOn rows cols a b u v)) := by
  constructor
  · intro hG
    rcases tag01 G rows cols u v hG with h0 | h1
    · exact Or.inl ⟨u, v, h0, isOn_self rows cols u v⟩
    · refine Or.inr ⟨⟨u, v, h1, isOn_self rows cols u v⟩, ?_⟩
      rintro ⟨a, b, h2, hon⟩
      obtain ⟨hGab, hab⟩ := tag2 G rows cols a b h2
      obtain ⟨-, hn⟩ := tag1 G rows cols u v h1
      obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hab (ha.trans hb.symm)
      · rw [ha, hb, hG] at hGab
        exact absurd hGab (by simp)
      · rw [ha, hb] at hGab hab hon
        have hc := hcov u v hG hGab
        have hX : v ∈ rows ∨ u ∈ cols := by
          rcases hc with h | h | h | h
          · exact absurd ⟨Ne.symm hab, Or.inl h⟩ hn
          · exact absurd ⟨Ne.symm hab, Or.inr (Or.inl h)⟩ hn
          · exact Or.inl h
          · exact Or.inr h
        have h3 := isOn_X rows cols v u u v hon hab hX
        exact hab h3.1
      · exact hab (ha.trans hb.symm)
  · rintro (⟨a, b, h0, hon⟩ | ⟨⟨a, b, h1, hon⟩, hH⟩)
    · obtain ⟨hGab, hab, hX⟩ := tag0 G rows cols a b h0
      obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb] at hGab
        exact hGab
      · rcases hX with hX | hX | hX
        · have h := isOn_X rows cols a b u v hon hab (Or.inl hX)
          rw [h.1, h.2] at hGab
          exact hGab
        · have h := isOn_X rows cols a b u v hon hab (Or.inr hX)
          rw [h.1, h.2] at hGab
          exact hGab
        · rw [ha, hb] at hX
          exact hX
      · exact absurd (ha.trans hb.symm) hab
    · by_contra hG
      have hG' : G u v = false := by simpa using hG
      by_cases huv : u = v
      · obtain ⟨hGab, -⟩ := tag1 G rows cols a b h1
        obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
        have ha' : a = u := by
          rcases ha with h | h
          · exact h
          · exact h.trans huv.symm
        have hb' : b = v := by
          rcases hb with h | h
          · exact h.trans huv
          · exact h
        rw [ha', hb'] at hGab
        exact hG hGab
      · exact hH ⟨u, v, tag2' G rows cols u v hG' huv, isOn_self rows cols u v⟩

def cellSet {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (k : ℕ) :
    Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun c => tag G rows cols c.1 c.2 = k)).image
    (fun c => tm rows cols c.1 c.2)

lemma hit_iff {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (k : ℕ)
    (u v : Fin n) :
    (∃ t ∈ cellSet G rows cols k, t.1 ∈ sigs rows cols u v ∧ t.2 ∈ sigs rows cols u v) ↔
      ∃ a b, tag G rows cols a b = k ∧ isOn rows cols a b u v := by
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨c.1, c.2, (Finset.mem_filter.mp hc).2, h1, h2⟩
  · rintro ⟨a, b, hk, h1, h2⟩
    exact ⟨tm rows cols a b,
      Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩, h1, h2⟩

lemma count_le {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) :
    (cellSet G rows cols 0).card + (cellSet G rows cols 1).card + (cellSet G rows cols 2).card
      ≤ n * n := by
  have h0 : ∀ k, (cellSet G rows cols k).card ≤
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun c => tag G rows cols c.1 c.2 = k)).card := fun k => Finset.card_image_le
  have hsum : ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun c => tag G rows cols c.1 c.2 = 0)).card +
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun c => tag G rows cols c.1 c.2 = 1)).card +
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun c => tag G rows cols c.1 c.2 = 2)).card ≤
      (Finset.univ : Finset (Fin n × Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro c _
    split_ifs <;> omega
  have hcard : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
  have e0 := h0 0
  have e1 := h0 1
  have e2 := h0 2
  omega

lemma main (n : ℕ) (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) :
    (∀ i j, G i j = true → G j i = false → i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols) ↔
    ∃ A B H : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)),
      A.card + B.card + H.card ≤ n * n ∧
      ∀ u v, G u v = true ↔
        ((∃ t ∈ A, t.1 ∈ sigs rows cols u v ∧ t.2 ∈ sigs rows cols u v) ∨
          ((∃ t ∈ B, t.1 ∈ sigs rows cols u v ∧ t.2 ∈ sigs rows cols u v) ∧
            ¬ (∃ t ∈ H, t.1 ∈ sigs rows cols u v ∧ t.2 ∈ sigs rows cols u v))) := by
  constructor
  · intro hcov
    refine ⟨cellSet G rows cols 0, cellSet G rows cols 1, cellSet G rows cols 2,
      count_le G rows cols, ?_⟩
    intro u v
    rw [hit_iff, hit_iff, hit_iff]
    exact correct G rows cols hcov u v
  · rintro ⟨A, B, H, -, hspec⟩ i j hij hji
    by_contra hc
    have e := sigs_swap rows cols i j (fun h => hc (Or.inl h))
      (fun h => hc (Or.inr (Or.inl h))) (fun h => hc (Or.inr (Or.inr (Or.inl h))))
      (fun h => hc (Or.inr (Or.inr (Or.inr h))))
    have h1 := (hspec i j).mp hij
    rw [e] at h1
    have h2 := (hspec j i).mpr h1
    rw [hji] at h2
    exact absurd h2 (by simp)

end PEqualNP.Outside.L_meta_25513_aux

theorem PEqualNP.Outside.L_meta_25513 : (∀ (n : ℕ) (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)),
  let signals := fun (u v : Fin n) =>
    (Finset.univ : Finset (Fin 3 × Fin n)).filter (fun s =>
      if s.1 = 0 then s.2 = u ∨ s.2 = v
      else if s.1 = 1 then s.2 ∈ rows ∧ s.2 = u
      else s.2 ∈ cols ∧ s.2 = v)
  let covers := ∀ i j, G i j = true → G j i = false →
    i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols
  let hit := fun (T : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)))
      (u v : Fin n) =>
    ∃ t ∈ T, t.1 ∈ signals u v ∧ t.2 ∈ signals u v
  covers ↔ ∃ A B H : Finset ((Fin 3 × Fin n) × (Fin 3 × Fin n)),
    A.card + B.card + H.card ≤ n * n ∧
    ∀ u v, G u v = true ↔ (hit A u v ∨ (hit B u v ∧ ¬ hit H u v))) := by
  intro n G rows cols signals covers hit
  exact PEqualNP.Outside.L_meta_25513_aux.main n G rows cols

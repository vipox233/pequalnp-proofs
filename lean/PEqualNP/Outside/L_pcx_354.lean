import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_354
def h_box (a b : ℕ) (π : Bool) : Finset (ℕ × ℕ) :=
  ((Finset.range (a+1)) ×ˢ (Finset.range (b+1))).filter (fun d => (d.1 + d.2) % 2 = (if π then 1 else 0))
def h_add (S T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (S ×ˢ T).image (fun p => (p.1.1 + p.2.1, p.1.2 + p.2.2))
def h_BoxSum (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ L : List (ℕ × ℕ × Bool), (∀ t ∈ L, t.1 ≤ t.2.1 + 1 ∧ t.2.1 ≤ t.1 + 1) ∧
    S = L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) {(0,0)}
theorem p_mem_add {S T : Finset (ℕ × ℕ)} {x1 x2 : ℕ} :
    (x1, x2) ∈ h_add S T ↔ ∃ y1 y2 z1 z2 : ℕ, (y1, y2) ∈ S ∧ (z1, z2) ∈ T ∧ x1 = y1 + z1 ∧ x2 = y2 + z2 := by
  constructor
  · intro h
    obtain ⟨⟨⟨y1, y2⟩, ⟨z1, z2⟩⟩, hm, he⟩ := Finset.mem_image.1 h
    rw [Finset.mem_product] at hm
    simp only [Prod.mk.injEq] at he
    exact ⟨y1, y2, z1, z2, hm.1, hm.2, he.1.symm, he.2.symm⟩
  · rintro ⟨y1, y2, z1, z2, hy, hz, rfl, rfl⟩
    exact Finset.mem_image.2 ⟨((y1, y2), (z1, z2)), Finset.mem_product.2 ⟨hy, hz⟩, rfl⟩
theorem p_mem_box {a b : ℕ} {π : Bool} {x1 x2 : ℕ} :
    (x1, x2) ∈ h_box a b π ↔ x1 ≤ a ∧ x2 ≤ b ∧ (x1 + x2) % 2 = if π then 1 else 0 := by
  simp only [h_box, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff, and_assoc]
theorem p_add_zero (S : Finset (ℕ × ℕ)) : h_add S {(0,0)} = S := by
  ext ⟨x1, x2⟩
  rw [p_mem_add]
  constructor
  · rintro ⟨y1, y2, z1, z2, hy, hz, rfl, rfl⟩
    rw [Finset.mem_singleton, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    simpa using hy
  · intro h
    exact ⟨x1, x2, 0, 0, h, Finset.mem_singleton_self _, rfl, rfl⟩
theorem p_zero_add (S : Finset (ℕ × ℕ)) : h_add {(0,0)} S = S := by
  ext ⟨x1, x2⟩
  rw [p_mem_add]
  constructor
  · rintro ⟨y1, y2, z1, z2, hy, hz, rfl, rfl⟩
    rw [Finset.mem_singleton, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using hz
  · intro h
    exact ⟨0, 0, x1, x2, Finset.mem_singleton_self _, h, by omega, by omega⟩
theorem p_add_assoc (A B C : Finset (ℕ × ℕ)) : h_add (h_add A B) C = h_add A (h_add B C) := by
  ext ⟨x1, x2⟩
  constructor
  · intro h
    obtain ⟨y1, y2, z1, z2, hy, hz, rfl, rfl⟩ := p_mem_add.1 h
    obtain ⟨a1, a2, b1, b2, ha, hb, rfl, rfl⟩ := p_mem_add.1 hy
    exact p_mem_add.2 ⟨a1, a2, b1 + z1, b2 + z2, ha, p_mem_add.2 ⟨b1, b2, z1, z2, hb, hz, rfl, rfl⟩,
      by omega, by omega⟩
  · intro h
    obtain ⟨a1, a2, y1, y2, ha, hy, rfl, rfl⟩ := p_mem_add.1 h
    obtain ⟨b1, b2, z1, z2, hb, hz, rfl, rfl⟩ := p_mem_add.1 hy
    exact p_mem_add.2 ⟨a1 + b1, a2 + b2, z1, z2, p_mem_add.2 ⟨a1, a2, b1, b2, ha, hb, rfl, rfl⟩, hz,
      by omega, by omega⟩
def p_F (L : List (ℕ × ℕ × Bool)) : Finset (ℕ × ℕ) :=
  L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) {(0,0)}
theorem p_foldr_init (L : List (ℕ × ℕ × Bool)) (X : Finset (ℕ × ℕ)) :
    L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) X = h_add X (p_F L) := by
  induction L with
  | nil => exact (p_add_zero X).symm
  | cons t L ih =>
    simp only [List.foldr_cons, p_F] at ih ⊢
    rw [ih, p_add_assoc]
theorem p_bs_add {S T : Finset (ℕ × ℕ)} (hS : h_BoxSum S) (hT : h_BoxSum T) : h_BoxSum (h_add S T) := by
  obtain ⟨L1, h1, rfl⟩ := hS
  obtain ⟨L2, h2, rfl⟩ := hT
  refine ⟨L2 ++ L1, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact h2 t h
    · exact h1 t h
  · symm
    rw [List.foldr_append]
    exact p_foldr_init L2 _
theorem p_bs_box {a b : ℕ} (π : Bool) (h1 : a ≤ b + 1) (h2 : b ≤ a + 1) : h_BoxSum (h_box a b π) := by
  refine ⟨[(a, b, π)], ?_, ?_⟩
  · intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨h1, h2⟩
  · show h_box a b π = h_add {(0,0)} (h_box a b π)
    rw [p_zero_add]
theorem p_bs_F {L : List (ℕ × ℕ × Bool)} (h : ∀ t ∈ L, t.1 ≤ t.2.1 + 1 ∧ t.2.1 ≤ t.1 + 1) :
    h_BoxSum (p_F L) := ⟨L, h, rfl⟩
theorem p_pin (S : Finset (ℕ × ℕ)) (p v : Bool) (x1 x2 : ℕ) :
    (x1, x2) ∈ h_add S (h_box 0 0 (p != v)) ↔ v = p ∧ (x1, x2) ∈ S := by
  rw [p_mem_add]
  constructor
  · rintro ⟨y1, y2, z1, z2, hy, hz, rfl, rfl⟩
    rw [p_mem_box] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    have e1 : z1 = 0 := by omega
    have e2 : z2 = 0 := by omega
    subst e1 e2
    refine ⟨?_, by simpa using hy⟩
    cases p <;> cases v <;> simp_all
  · rintro ⟨rfl, h⟩
    exact ⟨x1, x2, 0, 0, h, by rw [p_mem_box]; simp, rfl, rfl⟩
theorem p_step_box (j a b : ℕ) (c v : Bool) (z1 z2 : ℕ) :
    (z1, z2) ∈ h_box (a + (1 - j % 2)) (b + j % 2) (c != v) ↔
    ∃ v' : Bool, ∃ w1 w2 : ℕ, (w1, w2) ∈ h_box a b (c != v') ∧
      z1 = w1 + (if j % 2 = 0 ∧ v' ≠ v then 1 else 0) ∧
      z2 = w2 + (if j % 2 = 1 ∧ v' ≠ v then 1 else 0) := by
  simp only [p_mem_box]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · by_cases hz : z1 = 0
      · exact ⟨v, z1, z2, ⟨by omega, by omega, h3⟩, by simp, by simp⟩
      · refine ⟨!v, z1 - 1, z2, ⟨by omega, by omega, ?_⟩, ?_, ?_⟩
        · cases c <;> cases v <;> simp at h3 ⊢ <;> omega
        · cases v <;> simp [hj] <;> omega
        · cases v <;> simp [hj]
    · by_cases hz : z2 = 0
      · exact ⟨v, z1, z2, ⟨by omega, by omega, h3⟩, by simp, by simp⟩
      · refine ⟨!v, z1, z2 - 1, ⟨by omega, by omega, ?_⟩, ?_, ?_⟩
        · cases c <;> cases v <;> simp at h3 ⊢ <;> omega
        · cases v <;> simp [hj]
        · cases v <;> simp [hj] <;> omega
  · rintro ⟨v', w1, w2, ⟨h1, h2, h3⟩, rfl, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> cases c <;> cases v <;> cases v' <;>
      simp [hj] at h3 ⊢ <;> omega
theorem p_merge (a1 b1 a2 b2 : ℕ) (p c : Bool) (y1 y2 : ℕ) :
    (y1, y2) ∈ h_box (a1 + a2) (b1 + b2) (p != c) ↔
    ∃ u : Bool, ∃ s1 s2 t1 t2 : ℕ, (s1, s2) ∈ h_box a1 b1 (u != p) ∧ (t1, t2) ∈ h_box a2 b2 (c != u) ∧
      y1 = s1 + t1 ∧ y2 = s2 + t2 := by
  simp only [p_mem_box]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hq : (min y1 a1 + min y2 b1) % 2 = 0
    · refine ⟨p, min y1 a1, min y2 b1, y1 - min y1 a1, y2 - min y2 b1, ⟨by omega, by omega, ?_⟩,
        ⟨by omega, by omega, ?_⟩, by omega, by omega⟩
      · cases p <;> simp <;> omega
      · cases p <;> cases c <;> simp at h3 ⊢ <;> omega
    · refine ⟨!p, min y1 a1, min y2 b1, y1 - min y1 a1, y2 - min y2 b1, ⟨by omega, by omega, ?_⟩,
        ⟨by omega, by omega, ?_⟩, by omega, by omega⟩
      · cases p <;> simp <;> omega
      · cases p <;> cases c <;> simp at h3 ⊢ <;> omega
  · rintro ⟨u, s1, s2, t1, t2, ⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    cases u <;> cases p <;> cases c <;> simp at h3 h6 ⊢ <;> omega
def p_A (f : ℕ → Bool) (r j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => i % 2 = r ∧ f i ≠ f (i+1))).card
theorem p_A_succ (f : ℕ → Bool) (r j : ℕ) :
    p_A f r (j+1) = p_A f r j + (if j % 2 = r ∧ f j ≠ f (j+1) then 1 else 0) := by
  simp only [p_A, Finset.card_filter, Finset.sum_range_succ]
theorem p_A_congr (f g : ℕ → Bool) (r j : ℕ) (h : ∀ i ≤ j, f i = g i) : p_A f r j = p_A g r j := by
  unfold p_A
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  rw [h i (by omega), h (i+1) (by omega)]
def p_R (P : ℕ → Option Bool) (j : ℕ) (u v : Bool) (x1 x2 : ℕ) : Prop :=
  ∃ f : ℕ → Bool, f 0 = u ∧ f j = v ∧ (∀ i, 0 < i → i ≤ j → P i = none ∨ P i = some (f i)) ∧
    x1 = p_A f 0 j ∧ x2 = p_A f 1 j
theorem p_R_zero (P : ℕ → Option Bool) (u v : Bool) (x1 x2 : ℕ) :
    p_R P 0 u v x1 x2 ↔ (x1, x2) ∈ h_add {(0,0)} (h_box 0 0 (u != v)) := by
  rw [p_zero_add, p_mem_box]
  constructor
  · rintro ⟨f, hf0, hfj, -, rfl, rfl⟩
    subst hf0 hfj
    simp [p_A]
  · rintro ⟨h1, h2, h3⟩
    have e1 : x1 = 0 := by omega
    have e2 : x2 = 0 := by omega
    subst e1 e2
    have huv : u = v := by cases u <;> cases v <;> simp_all
    subst huv
    exact ⟨fun _ => u, rfl, rfl, fun i h1 h2 => absurd h2 (by omega), by simp [p_A], by simp [p_A]⟩
theorem p_R_succ (P : ℕ → Option Bool) (j : ℕ) (u v : Bool) (x1 x2 : ℕ) :
    p_R P (j+1) u v x1 x2 ↔ (P (j+1) = none ∨ P (j+1) = some v) ∧
      ∃ v' : Bool, ∃ y1 y2 : ℕ, p_R P j u v' y1 y2 ∧
        x1 = y1 + (if j % 2 = 0 ∧ v' ≠ v then 1 else 0) ∧
        x2 = y2 + (if j % 2 = 1 ∧ v' ≠ v then 1 else 0) := by
  constructor
  · rintro ⟨f, hf0, hfj, hP, rfl, rfl⟩
    refine ⟨by rw [← hfj]; exact hP (j+1) (by omega) le_rfl, f j, p_A f 0 j, p_A f 1 j,
      ⟨f, hf0, rfl, fun i h1 h2 => hP i h1 (by omega), rfl, rfl⟩, ?_, ?_⟩
    · rw [p_A_succ, hfj]
    · rw [p_A_succ, hfj]
  · rintro ⟨hPj, v', y1, y2, ⟨f, hf0, hfj, hP, rfl, rfl⟩, rfl, rfl⟩
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → Bool, (∀ i ≤ j, g i = f i) ∧ g (j+1) = v :=
      ⟨fun i => if i = j+1 then v else f i, fun i hi => by simp [show i ≠ j + 1 by omega], by simp⟩
    refine ⟨g, by rw [hg1 0 (Nat.zero_le _), hf0], hg2, ?_, ?_, ?_⟩
    · intro i h1 h2
      rcases Nat.lt_or_ge i (j+1) with h | h
      · rw [hg1 i (by omega)]
        exact hP i h1 (by omega)
      · have e : i = j + 1 := by omega
        subst e
        rw [hg2]
        exact hPj
    · rw [p_A_succ, p_A_congr g f 0 j hg1, hg1 j le_rfl, hg2, hfj]
    · rw [p_A_succ, p_A_congr g f 1 j hg1, hg1 j le_rfl, hg2, hfj]
theorem p_ext (P : ℕ → Option Bool) (j : ℕ) (u : Bool) (G : Finset (ℕ × ℕ)) (c : Bool) (a b : ℕ)
    (hR : ∀ v x1 x2, p_R P j u v x1 x2 ↔ (x1, x2) ∈ h_add G (h_box a b (c != v)))
    (v : Bool) (x1 x2 : ℕ) :
    (∃ v' : Bool, ∃ y1 y2 : ℕ, p_R P j u v' y1 y2 ∧
        x1 = y1 + (if j % 2 = 0 ∧ v' ≠ v then 1 else 0) ∧
        x2 = y2 + (if j % 2 = 1 ∧ v' ≠ v then 1 else 0)) ↔
      (x1, x2) ∈ h_add G (h_box (a + (1 - j % 2)) (b + j % 2) (c != v)) := by
  rw [p_mem_add]
  constructor
  · rintro ⟨v', y1, y2, hy, rfl, rfl⟩
    obtain ⟨g1, g2, z1, z2, hg, hz, rfl, rfl⟩ := p_mem_add.1 ((hR v' y1 y2).1 hy)
    exact ⟨g1, g2, z1 + (if j % 2 = 0 ∧ v' ≠ v then 1 else 0), z2 + (if j % 2 = 1 ∧ v' ≠ v then 1 else 0),
      hg, (p_step_box j a b c v _ _).2 ⟨v', z1, z2, hz, rfl, rfl⟩, by omega, by omega⟩
  · rintro ⟨g1, g2, z1', z2', hg, hz', rfl, rfl⟩
    obtain ⟨v', z1, z2, hz, rfl, rfl⟩ := (p_step_box j a b c v _ _).1 hz'
    exact ⟨v', g1 + z1, g2 + z2, (hR v' _ _).2 (p_mem_add.2 ⟨g1, g2, z1, z2, hg, hz, rfl, rfl⟩),
      by omega, by omega⟩
def p_Inv (P : ℕ → Option Bool) (j : ℕ) : Prop :=
  (∃ a b : ℕ, a = b + j % 2 ∧
    ∀ u v x1 x2, p_R P j u v x1 x2 ↔ (x1, x2) ∈ h_add {(0,0)} (h_box a b (u != v))) ∨
  (∃ a1 b1 : ℕ, ∃ p1 : Bool, ∃ L : List (ℕ × ℕ × Bool), ∃ a b : ℕ, ∃ c : Bool,
    (∀ t ∈ L, t.1 ≤ t.2.1 + 1 ∧ t.2.1 ≤ t.1 + 1) ∧ b1 ≤ a1 ∧ a1 ≤ b1 + 1 ∧
    a ≤ b + j % 2 ∧ b + j % 2 ≤ a + 1 ∧
    ∀ u v x1 x2, p_R P j u v x1 x2 ↔
      (x1, x2) ∈ h_add (h_add (h_box a1 b1 (u != p1)) (p_F L)) (h_box a b (c != v)))
theorem p_inv (P : ℕ → Option Bool) (j : ℕ) : p_Inv P j := by
  induction j with
  | zero => exact Or.inl ⟨0, 0, by omega, p_R_zero P⟩
  | succ j ih =>
    rcases ih with ⟨a, b, hab, hR⟩ | ⟨a1, b1, p1, L, a, b, c, hL, h1, h2, h3, h4, hR⟩
    · rcases hP : P (j+1) with _ | p
      · refine Or.inl ⟨a + (1 - j % 2), b + j % 2, by omega, fun u v x1 x2 => ?_⟩
        rw [p_R_succ, ← p_ext P j u {(0,0)} u a b (hR u) v x1 x2]
        exact ⟨fun h => h.2, fun h => ⟨Or.inl hP, h⟩⟩
      · refine Or.inr ⟨a + (1 - j % 2), b + j % 2, p, [], 0, 0, p, by simp, by omega, by omega,
          by omega, by omega, fun u v x1 x2 => ?_⟩
        rw [p_R_succ, p_pin, show p_F [] = ({(0,0)} : Finset (ℕ × ℕ)) from rfl, p_add_zero,
          ← p_zero_add (h_box (a + (1 - j % 2)) (b + j % 2) (u != p)),
          ← p_ext P j u {(0,0)} u a b (hR u) p x1 x2, hP]
        constructor
        · rintro ⟨h, hex⟩
          have hpv : p = v := by simpa using h
          subst hpv
          exact ⟨rfl, hex⟩
        · rintro ⟨rfl, hex⟩
          exact ⟨Or.inr rfl, hex⟩
    · rcases hP : P (j+1) with _ | p
      · refine Or.inr ⟨a1, b1, p1, L, a + (1 - j % 2), b + j % 2, c, hL, h1, h2, by omega, by omega,
          fun u v x1 x2 => ?_⟩
        rw [p_R_succ, ← p_ext P j u _ c a b (hR u) v x1 x2]
        exact ⟨fun h => h.2, fun h => ⟨Or.inl hP, h⟩⟩
      · refine Or.inr ⟨a1, b1, p1, (a + (1 - j % 2), b + j % 2, c != p) :: L, 0, 0, p, ?_, h1, h2,
          by omega, by omega, fun u v x1 x2 => ?_⟩
        · intro t ht
          rcases List.mem_cons.1 ht with rfl | ht
          · constructor <;> dsimp only <;> omega
          · exact hL t ht
        · rw [p_R_succ, p_pin, show p_F ((a + (1 - j % 2), b + j % 2, c != p) :: L) =
            h_add (p_F L) (h_box (a + (1 - j % 2)) (b + j % 2) (c != p)) from rfl, ← p_add_assoc,
            ← p_ext P j u _ c a b (hR u) p x1 x2, hP]
          constructor
          · rintro ⟨h, hex⟩
            have hpv : p = v := by simpa using h
            subst hpv
            exact ⟨rfl, hex⟩
          · rintro ⟨rfl, hex⟩
            exact ⟨Or.inr rfl, hex⟩
theorem p_final (n : ℕ) (hn : n % 2 = 0) (P : ℕ → Option Bool) (o : Option Bool) (S : Finset (ℕ × ℕ))
    (hS : ∀ x1 x2, (x1, x2) ∈ S ↔ ∃ u : Bool, (o = none ∨ o = some u) ∧ p_R P n u u x1 x2) :
    h_BoxSum S := by
  rcases p_inv P n with ⟨a, b, hab, hR⟩ | ⟨a1, b1, p1, L, a, b, c, hL, h1, h2, h3, h4, hR⟩
  · have hS' : S = h_box a b false := by
      ext ⟨x1, x2⟩
      rw [hS]
      constructor
      · rintro ⟨u, -, hu⟩
        rw [hR, p_zero_add, bne_self_eq_false] at hu
        exact hu
      · intro hx
        refine ⟨o.getD false, ?_, ?_⟩
        · cases o <;> simp
        · rw [hR, p_zero_add, bne_self_eq_false]
          exact hx
    rw [hS']
    exact p_bs_box false (by omega) (by omega)
  · rcases o with _ | u0
    · have hS' : S = h_add (p_F L) (h_box (a1 + a) (b1 + b) (p1 != c)) := by
        ext ⟨x1, x2⟩
        rw [hS, p_mem_add]
        constructor
        · rintro ⟨u, -, hu⟩
          rw [hR, p_mem_add] at hu
          obtain ⟨g1, g2, z1, z2, hg, hz, rfl, rfl⟩ := hu
          obtain ⟨s1, s2, f1, f2, hs, hf, rfl, rfl⟩ := p_mem_add.1 hg
          exact ⟨f1, f2, s1 + z1, s2 + z2, hf,
            (p_merge a1 b1 a b p1 c _ _).2 ⟨u, s1, s2, z1, z2, hs, hz, rfl, rfl⟩, by omega, by omega⟩
        · rintro ⟨f1, f2, y1, y2, hf, hy, rfl, rfl⟩
          obtain ⟨u, s1, s2, z1, z2, hs, hz, rfl, rfl⟩ := (p_merge a1 b1 a b p1 c _ _).1 hy
          refine ⟨u, Or.inl rfl, ?_⟩
          rw [hR, p_mem_add]
          exact ⟨s1 + f1, s2 + f2, z1, z2, p_mem_add.2 ⟨s1, s2, f1, f2, hs, hf, rfl, rfl⟩, hz,
            by omega, by omega⟩
      rw [hS']
      exact p_bs_add (p_bs_F hL) (p_bs_box _ (by omega) (by omega))
    · have hS' : S = h_add (h_add (h_box a1 b1 (u0 != p1)) (p_F L)) (h_box a b (c != u0)) := by
        ext ⟨x1, x2⟩
        rw [hS]
        constructor
        · rintro ⟨u, hu, hx⟩
          have e : u0 = u := by simpa using hu
          subst e
          exact (hR _ _ _ _).1 hx
        · intro hx
          exact ⟨u0, Or.inr rfl, (hR _ _ _ _).2 hx⟩
      rw [hS']
      exact p_bs_add (p_bs_add (p_bs_box _ (by omega) (by omega)) (p_bs_F hL))
        (p_bs_box _ (by omega) (by omega))
theorem p_count (n : ℕ) (hn : 0 < n) (s : Fin n → Bool) (g : ℕ → Bool)
    (hsg : ∀ t : Fin n, s t = g t.val) (hg : g n = g 0) (r : ℕ) :
    (Finset.univ.filter (fun t : Fin n => t.val % 2 = r ∧ s t ≠ s ⟨(t.val+1) % n, Nat.mod_lt _ hn⟩)).card
      = p_A g r n := by
  unfold p_A
  rw [Finset.card_filter, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have e : g ((t.val + 1) % n) = g (t.val + 1) := by
    rcases Nat.lt_or_ge (t.val + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have e2 : t.val + 1 = n := by omega
      rw [e2, Nat.mod_self, hg]
  simp only [hsg, e]
theorem h_cyc (l : ℕ) (hl : 0 < l) (pin : Fin (2*l) → Option Bool) :
    h_BoxSum (((Finset.univ : Finset (Fin (2*l) → Bool)).filter
      (fun s => ∀ t, pin t = none ∨ pin t = some (s t))).image
      (fun s => ((Finset.univ.filter (fun t : Fin (2*l) => t.val % 2 = 0 ∧
          s t ≠ s ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩)).card,
        (Finset.univ.filter (fun t : Fin (2*l) => t.val % 2 = 1 ∧
          s t ≠ s ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩)).card))) := by
  refine p_final (2*l) (by omega) (fun i => pin ⟨i % (2*l), Nat.mod_lt _ (by omega)⟩)
    (pin ⟨0, by omega⟩) _ ?_
  intro x1 x2
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    have hsf : ∀ t : Fin (2*l), s t = s ⟨t.val % (2*l), Nat.mod_lt _ (by omega)⟩ := fun t =>
      congrArg s (Fin.ext (Nat.mod_eq_of_lt t.isLt).symm)
    have hg : s ⟨(2*l) % (2*l), Nat.mod_lt _ (by omega)⟩ = s ⟨0 % (2*l), Nat.mod_lt _ (by omega)⟩ :=
      congrArg s (Fin.ext (by simp))
    refine ⟨s ⟨0, by omega⟩, hs _, fun i => s ⟨i % (2*l), Nat.mod_lt _ (by omega)⟩,
      congrArg s (Fin.ext (Nat.zero_mod _)), congrArg s (Fin.ext (Nat.mod_self _)),
      fun i _ _ => hs _, ?_, ?_⟩
    · rw [← h1]
      exact p_count (2*l) (by omega) s _ hsf hg 0
    · rw [← h2]
      exact p_count (2*l) (by omega) s _ hsf hg 1
  · rintro ⟨u, hu, f, hf0, hfn, hP, rfl, rfl⟩
    refine ⟨fun t => f t.val, ?_, ?_, ?_⟩
    · intro t
      rcases Nat.eq_zero_or_pos t.val with h | h
      · have e : t = ⟨0, by omega⟩ := Fin.ext h
        rw [e]
        show pin ⟨0, _⟩ = none ∨ pin ⟨0, _⟩ = some (f 0)
        rw [hf0]
        exact hu
      · have h3 := hP t.val h (by omega)
        have ht : pin ⟨t.val % (2*l), Nat.mod_lt _ (by omega)⟩ = pin t :=
          congrArg pin (Fin.ext (Nat.mod_eq_of_lt t.isLt))
        simp only [ht] at h3
        exact h3
    · exact p_count (2*l) (by omega) (fun t => f t.val) f (fun t => rfl) (hfn.trans hf0.symm) 0
    · exact p_count (2*l) (by omega) (fun t => f t.val) f (fun t => rfl) (hfn.trans hf0.symm) 1
theorem c_mem_add (S T : Finset (ℕ × ℕ)) (p : ℕ × ℕ) :
    p ∈ h_add S T ↔ ∃ a ∈ S, ∃ b ∈ T, p = a + b := by
  unfold h_add
  simp only [Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
theorem c_zero_add (T : Finset (ℕ × ℕ)) : h_add {(0,0)} T = T := by
  ext p
  rw [c_mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    have e : ((0,0) : ℕ × ℕ) + b = b := Prod.ext (zero_add _) (zero_add _)
    rw [e]
    exact hb
  · intro hp
    exact ⟨(0,0), Finset.mem_singleton_self _, p, hp, (Prod.ext (zero_add _) (zero_add _)).symm⟩
theorem c_rc (X Y Z : Finset (ℕ × ℕ)) : h_add (h_add X Y) Z = h_add (h_add X Z) Y := by
  ext p
  simp only [c_mem_add]
  constructor
  · rintro ⟨a, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩
    exact ⟨x + z, ⟨x, hx, z, hz, rfl⟩, y, hy, add_right_comm x y z⟩
  · rintro ⟨a, ⟨x, hx, z, hz, rfl⟩, y, hy, rfl⟩
    exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, z, hz, add_right_comm x z y⟩
theorem c_fold (L : List (ℕ × ℕ × Bool)) (X T : Finset (ℕ × ℕ)) :
    L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) (h_add X T) =
      h_add (L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) X) T := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [List.foldr_cons]
    rw [ih, c_rc]
theorem c_closed (S T : Finset (ℕ × ℕ)) (hS : h_BoxSum S) (hT : h_BoxSum T) :
    h_BoxSum (h_add S T) := by
  obtain ⟨L1, h1, rfl⟩ := hS
  obtain ⟨L2, h2, rfl⟩ := hT
  unfold h_BoxSum
  refine ⟨L1 ++ L2, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact h1 t h
    · exact h2 t h
  · rw [List.foldr_append, ← c_fold, c_zero_add]
theorem c_zero : h_BoxSum {(0,0)} := by
  unfold h_BoxSum
  exact ⟨[], fun t ht => by simp at ht, rfl⟩
def c_img {V : Type} [Fintype V] [DecidableEq V] (pin : V → Option Bool)
    (F : (V → Bool) → ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.univ : Finset (V → Bool)).filter
    (fun x => ∀ v, pin v = none ∨ pin v = some (x v))).image F
theorem c_transport {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (φ : W → V) (hφ : Function.Injective φ) (pin : V → Option Bool)
    (F : (V → Bool) → ℕ × ℕ) (G : (W → Bool) → ℕ × ℕ) (hFG : ∀ x, F x = G (x ∘ φ)) :
    c_img pin F = c_img (pin ∘ φ) G := by
  classical
  ext p
  simp only [c_img, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x ∘ φ, fun w => hx (φ w), (hFG x).symm⟩
  · rintro ⟨s, hs, rfl⟩
    let x : V → Bool := fun v => if h : ∃ w, φ w = v then s h.choose else (pin v).getD false
    have hxs : ∀ w, x (φ w) = s w := by
      intro w
      have h : ∃ w', φ w' = φ w := ⟨w, rfl⟩
      show (if h : ∃ w', φ w' = φ w then s h.choose else (pin (φ w)).getD false) = s w
      rw [dite_eq_left h]
      exact congrArg s (hφ h.choose_spec)
    have hxs' : x ∘ φ = s := funext hxs
    refine ⟨x, ?_, by rw [hFG, hxs']⟩
    intro v
    by_cases h : ∃ w, φ w = v
    · obtain ⟨w, rfl⟩ := h
      rw [hxs w]
      exact hs w
    · rcases hp : pin v with _ | b
      · exact Or.inl rfl
      · right
        show some b = some (if h : ∃ w, φ w = v then s h.choose else (pin v).getD false)
        simp only [dite_eq_right h, hp, Option.getD_some]
def c_F {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm ι) (A : Finset ι)
    (x : Bool × ι → Bool) : ℕ × ℕ :=
  ((A.filter (fun i => x (false,i) ≠ x (true,i))).card,
    (A.filter (fun i => x (false,i) ≠ x (true, ρ i))).card)
theorem c_split {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm ι)
    (pin : Bool × ι → Option Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, ρ i ∈ A) (hB : ∀ i ∈ B, ρ i ∈ B) :
    c_img pin (c_F ρ (A ∪ B)) = h_add (c_img pin (c_F ρ A)) (c_img pin (c_F ρ B)) := by
  have hsum : ∀ x, c_F ρ (A ∪ B) x = c_F ρ A x + c_F ρ B x := by
    intro x
    simp only [c_F, Finset.filter_union, Prod.mk_add_mk]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hAB),
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hAB)]
  ext p
  rw [c_mem_add]
  simp only [c_img, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x, hx, rfl⟩, hsum x⟩
  · rintro ⟨a, ⟨x1, hx1, rfl⟩, b, ⟨x2, hx2, rfl⟩, rfl⟩
    let x : Bool × ι → Bool := fun v => if v.2 ∈ A then x1 v else x2 v
    have h1 : ∀ i ∈ A, ∀ c : Bool, x (c, i) = x1 (c, i) := fun i hi c => ite_eq_left hi
    have h2 : ∀ i ∈ B, ∀ c : Bool, x (c, i) = x2 (c, i) :=
      fun i hi c => ite_eq_right (Finset.disjoint_right.1 hAB hi)
    refine ⟨x, ?_, ?_⟩
    · intro v
      by_cases h : v.2 ∈ A
      · have e : x v = x1 v := ite_eq_left h
        rw [e]
        exact hx1 v
      · have e : x v = x2 v := ite_eq_right h
        rw [e]
        exact hx2 v
    · rw [hsum]
      have eA : c_F ρ A x = c_F ρ A x1 := by
        unfold c_F
        congr 1
        · congr 1
          apply Finset.filter_congr
          intro i hi
          rw [h1 i hi false, h1 i hi true]
        · congr 1
          apply Finset.filter_congr
          intro i hi
          rw [h1 i hi false, h1 (ρ i) (hA i hi) true]
      have eB : c_F ρ B x = c_F ρ B x2 := by
        unfold c_F
        congr 1
        · congr 1
          apply Finset.filter_congr
          intro i hi
          rw [h2 i hi false, h2 i hi true]
        · congr 1
          apply Finset.filter_congr
          intro i hi
          rw [h2 i hi false, h2 (ρ i) (hB i hi) true]
      rw [eA, eB]
theorem c_empty {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm ι)
    (pin : Bool × ι → Option Bool) : c_img pin (c_F ρ ∅) = {(0,0)} := by
  ext p
  simp only [c_img, c_F, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.filter_empty, Finset.card_empty, Finset.mem_singleton]
  constructor
  · rintro ⟨x, _, rfl⟩
    rfl
  · rintro rfl
    refine ⟨fun v => (pin v).getD false, ?_, rfl⟩
    intro v
    rcases h : pin v with _ | b
    · exact Or.inl rfl
    · right
      simp [h]
def c_orb {ι : Type} [DecidableEq ι] (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) : Finset ι :=
  (Finset.range l).image (fun j => (ρ ^ j) i0)
theorem c_mem_orb {ι : Type} [DecidableEq ι] (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) (i : ι) :
    i ∈ c_orb ρ i0 l ↔ ∃ j, j < l ∧ (ρ ^ j) i0 = i := by
  simp only [c_orb, Finset.mem_image, Finset.mem_range]
theorem c_inj {ι : Type} (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ)
    (hmin : ∀ k, 0 < k → k < l → (ρ ^ k) i0 ≠ i0) :
    ∀ a b, a < l → b < l → (ρ ^ a) i0 = (ρ ^ b) i0 → a = b := by
  have key : ∀ a b, a < b → b < l → (ρ ^ a) i0 = (ρ ^ b) i0 → False := by
    intro a b hab hbl h
    apply hmin (b - a) (by omega) (by omega)
    have e : ρ ^ b = ρ ^ a * ρ ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e, Equiv.Perm.mul_apply] at h
    exact (ρ ^ a).injective h.symm
  intro a b ha hb h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hb h).elim
  · exact hab
  · exact (key b a hab ha h.symm).elim
theorem c_orb_inv {ι : Type} [DecidableEq ι] (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) (hl : 0 < l)
    (hper : (ρ ^ l) i0 = i0) : ∀ i ∈ c_orb ρ i0 l, ρ i ∈ c_orb ρ i0 l := by
  intro i hi
  rw [c_mem_orb] at hi ⊢
  obtain ⟨j, hj, rfl⟩ := hi
  by_cases h : j + 1 < l
  · exact ⟨j + 1, h, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
  · refine ⟨0, hl, ?_⟩
    have e : j + 1 = l := by omega
    rw [pow_zero, Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← pow_succ', e, hper]
theorem c_orb_back {ι : Type} [DecidableEq ι] (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) (hl : 0 < l)
    (hper : (ρ ^ l) i0 = i0) : ∀ i, ρ i ∈ c_orb ρ i0 l → i ∈ c_orb ρ i0 l := by
  intro i hi
  rw [c_mem_orb] at hi ⊢
  obtain ⟨j, hj, hji⟩ := hi
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    refine ⟨l - 1, by omega, ρ.injective ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (show 1 ≤ l by omega), hper,
      ← hji, pow_zero, Equiv.Perm.one_apply]
  · refine ⟨j - 1, by omega, ρ.injective ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (show 1 ≤ j by omega), hji]
theorem c_orb_sub {ι : Type} [DecidableEq ι] (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) (A : Finset ι)
    (hi0 : i0 ∈ A) (hA : ∀ i ∈ A, ρ i ∈ A) : c_orb ρ i0 l ⊆ A := by
  intro i hi
  rw [c_mem_orb] at hi
  obtain ⟨j, -, rfl⟩ := hi
  induction j with
  | zero => simpa using hi0
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hA _ ih
theorem c_even (l t : ℕ) (ht : t < 2*l) (h : t % 2 = 0) :
    (t+1) % (2*l) % 2 = 1 ∧ (t+1) % (2*l) / 2 = t / 2 := by
  rw [Nat.mod_eq_of_lt (by omega : t + 1 < 2*l)]
  omega
theorem c_odd {ι : Type} (ρ : Equiv.Perm ι) (i0 : ι) (l t : ℕ) (hper : (ρ ^ l) i0 = i0)
    (ht : t < 2*l) (h : t % 2 = 1) :
    (t+1) % (2*l) % 2 = 0 ∧ (ρ ^ ((t+1) % (2*l) / 2)) i0 = ρ ((ρ ^ (t / 2)) i0) := by
  rcases Nat.lt_or_ge (t+1) (2*l) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    refine ⟨by omega, ?_⟩
    rw [show (t+1)/2 = t/2 + 1 by omega, pow_succ', Equiv.Perm.mul_apply]
  · have e : t + 1 = 2*l := by omega
    rw [e, Nat.mod_self]
    refine ⟨Nat.zero_mod 2, ?_⟩
    rw [Nat.zero_div, pow_zero, Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← pow_succ',
      show t/2 + 1 = l by omega, hper]
def c_phi {ι : Type} (ρ : Equiv.Perm ι) (i0 : ι) (l : ℕ) (t : Fin (2*l)) : Bool × ι :=
  if t.val % 2 = 0 then (true, (ρ ^ (t.val / 2)) i0) else (false, (ρ ^ (t.val / 2)) i0)
def c_G (l : ℕ) (hl : 0 < l) (s : Fin (2*l) → Bool) : ℕ × ℕ :=
  ((Finset.univ.filter (fun t : Fin (2*l) => t.val % 2 = 0 ∧
          s t ≠ s ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩)).card,
        (Finset.univ.filter (fun t : Fin (2*l) => t.val % 2 = 1 ∧
          s t ≠ s ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩)).card)
theorem c_cycle {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm ι)
    (pin : Bool × ι → Option Bool) (i0 : ι) (l : ℕ) (hl : 0 < l) (hper : (ρ ^ l) i0 = i0)
    (hmin : ∀ k, 0 < k → k < l → (ρ ^ k) i0 ≠ i0) :
    h_BoxSum (c_img pin (c_F ρ (c_orb ρ i0 l))) := by
  have hinj := c_inj ρ i0 l hmin
  have hφ : Function.Injective (c_phi ρ i0 l) := by
    intro t1 t2 h
    have a1 := t1.isLt
    have a2 := t2.isLt
    unfold c_phi at h
    by_cases h1 : t1.val % 2 = 0 <;> by_cases h2 : t2.val % 2 = 0
    · rw [ite_eq_left h1, ite_eq_left h2] at h
      have := hinj _ _ (by omega) (by omega) (Prod.mk.inj h).2
      exact Fin.ext (by omega)
    · rw [ite_eq_left h1, ite_eq_right h2] at h
      simp at h
    · rw [ite_eq_right h1, ite_eq_left h2] at h
      simp at h
    · rw [ite_eq_right h1, ite_eq_right h2] at h
      have := hinj _ _ (by omega) (by omega) (Prod.mk.inj h).2
      exact Fin.ext (by omega)
  have hE : ∀ t : Fin (2*l), t.val % 2 = 0 →
      c_phi ρ i0 l t = (true, (ρ ^ (t.val / 2)) i0) ∧
      c_phi ρ i0 l ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩ =
        (false, (ρ ^ (t.val / 2)) i0) := by
    intro t ht
    obtain ⟨e1, e2⟩ := c_even l t.val t.isLt ht
    constructor
    · show (if t.val % 2 = 0 then (true, (ρ ^ (t.val / 2)) i0)
        else (false, (ρ ^ (t.val / 2)) i0)) = _
      rw [ite_eq_left ht]
    · show (if (t.val+1) % (2*l) % 2 = 0 then (true, (ρ ^ ((t.val+1) % (2*l) / 2)) i0)
          else (false, (ρ ^ ((t.val+1) % (2*l) / 2)) i0)) = _
      rw [ite_eq_right (show ¬ ((t.val+1) % (2*l) % 2 = 0) by omega), e2]
  have hO : ∀ t : Fin (2*l), t.val % 2 = 1 →
      c_phi ρ i0 l t = (false, (ρ ^ (t.val / 2)) i0) ∧
      c_phi ρ i0 l ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩ =
        (true, ρ ((ρ ^ (t.val / 2)) i0)) := by
    intro t ht
    obtain ⟨e1, e2⟩ := c_odd ρ i0 l t.val hper t.isLt ht
    constructor
    · show (if t.val % 2 = 0 then (true, (ρ ^ (t.val / 2)) i0)
        else (false, (ρ ^ (t.val / 2)) i0)) = _
      rw [ite_eq_right (show ¬ (t.val % 2 = 0) by omega)]
    · show (if (t.val+1) % (2*l) % 2 = 0 then (true, (ρ ^ ((t.val+1) % (2*l) / 2)) i0)
          else (false, (ρ ^ ((t.val+1) % (2*l) / 2)) i0)) = _
      rw [ite_eq_left e1, e2]
  have hFG : ∀ x, c_F ρ (c_orb ρ i0 l) x = c_G l hl (x ∘ c_phi ρ i0 l) := by
    intro x
    unfold c_F c_G
    congr 1
    · symm
      apply Finset.card_bij (fun t _ => (ρ ^ (t.val / 2)) i0)
      · intro t ht
        rw [Finset.mem_filter] at ht ⊢
        have hev : t.val % 2 = 0 := ht.2.1
        have hne : x (c_phi ρ i0 l t) ≠
            x (c_phi ρ i0 l ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩) := ht.2.2
        rw [(hE t hev).1, (hE t hev).2] at hne
        exact ⟨(c_mem_orb ρ i0 l _).2 ⟨t.val / 2, by have := t.isLt; omega, rfl⟩,
          fun h => hne h.symm⟩
      · intro t1 ht1 t2 ht2 h
        rw [Finset.mem_filter] at ht1 ht2
        have p1 : t1.val % 2 = 0 := ht1.2.1
        have p2 : t2.val % 2 = 0 := ht2.2.1
        have a1 := t1.isLt
        have a2 := t2.isLt
        have := hinj _ _ (by omega) (by omega) h
        exact Fin.ext (by omega)
      · intro m hm
        rw [Finset.mem_filter, c_mem_orb] at hm
        obtain ⟨⟨j, hj, rfl⟩, hne⟩ := hm
        have hj2 : 2 * j < 2 * l := by omega
        have hev : (⟨2*j, hj2⟩ : Fin (2*l)).val % 2 = 0 := by
          show 2 * j % 2 = 0
          omega
        have hdiv : (⟨2*j, hj2⟩ : Fin (2*l)).val / 2 = j := by
          show 2 * j / 2 = j
          omega
        obtain ⟨e1, e2⟩ := hE ⟨2*j, hj2⟩ hev
        rw [hdiv] at e1 e2
        refine ⟨⟨2*j, hj2⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, hev, ?_⟩
          show x (c_phi ρ i0 l ⟨2*j, hj2⟩) ≠ x (c_phi ρ i0 l
            ⟨((⟨2*j, hj2⟩ : Fin (2*l)).val + 1) % (2*l), Nat.mod_lt _ (by omega)⟩)
          rw [e1, e2]
          exact fun h => hne h.symm
        · show (ρ ^ ((⟨2*j, hj2⟩ : Fin (2*l)).val / 2)) i0 = (ρ ^ j) i0
          rw [hdiv]
    · symm
      apply Finset.card_bij (fun t _ => (ρ ^ (t.val / 2)) i0)
      · intro t ht
        rw [Finset.mem_filter] at ht ⊢
        have hod : t.val % 2 = 1 := ht.2.1
        have hne : x (c_phi ρ i0 l t) ≠
            x (c_phi ρ i0 l ⟨(t.val+1) % (2*l), Nat.mod_lt _ (by omega)⟩) := ht.2.2
        rw [(hO t hod).1, (hO t hod).2] at hne
        exact ⟨(c_mem_orb ρ i0 l _).2 ⟨t.val / 2, by have := t.isLt; omega, rfl⟩, hne⟩
      · intro t1 ht1 t2 ht2 h
        rw [Finset.mem_filter] at ht1 ht2
        have p1 : t1.val % 2 = 1 := ht1.2.1
        have p2 : t2.val % 2 = 1 := ht2.2.1
        have a1 := t1.isLt
        have a2 := t2.isLt
        have := hinj _ _ (by omega) (by omega) h
        exact Fin.ext (by omega)
      · intro m hm
        rw [Finset.mem_filter, c_mem_orb] at hm
        obtain ⟨⟨j, hj, rfl⟩, hne⟩ := hm
        have hj2 : 2 * j + 1 < 2 * l := by omega
        have hod : (⟨2*j+1, hj2⟩ : Fin (2*l)).val % 2 = 1 := by
          show (2 * j + 1) % 2 = 1
          omega
        have hdiv : (⟨2*j+1, hj2⟩ : Fin (2*l)).val / 2 = j := by
          show (2 * j + 1) / 2 = j
          omega
        obtain ⟨e1, e2⟩ := hO ⟨2*j+1, hj2⟩ hod
        rw [hdiv] at e1 e2
        refine ⟨⟨2*j+1, hj2⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, hod, ?_⟩
          show x (c_phi ρ i0 l ⟨2*j+1, hj2⟩) ≠ x (c_phi ρ i0 l
            ⟨((⟨2*j+1, hj2⟩ : Fin (2*l)).val + 1) % (2*l), Nat.mod_lt _ (by omega)⟩)
          rw [e1, e2]
          exact hne
        · show (ρ ^ ((⟨2*j+1, hj2⟩ : Fin (2*l)).val / 2)) i0 = (ρ ^ j) i0
          rw [hdiv]
  have e : c_img (pin ∘ c_phi ρ i0 l) (c_G l hl) =
      ((Finset.univ : Finset (Fin (2*l) → Bool)).filter (fun s => ∀ t,
        (pin ∘ c_phi ρ i0 l) t = none ∨ (pin ∘ c_phi ρ i0 l) t = some (s t))).image
        (c_G l hl) := by
    ext p
    simp only [c_img, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [c_transport (c_phi ρ i0 l) hφ pin _ (c_G l hl) hFG, e]
  exact h_cyc l hl (pin ∘ c_phi ρ i0 l)
theorem c_main {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Equiv.Perm ι)
    (pin : Bool × ι → Option Bool) :
    ∀ (N : ℕ) (A : Finset ι), A.card = N → (∀ i ∈ A, ρ i ∈ A) →
      h_BoxSum (c_img pin (c_F ρ A)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A hcard hA
    rcases A.eq_empty_or_nonempty with h | ⟨i0, hi0⟩
    · subst h
      rw [c_empty]
      exact c_zero
    · have hex : ∃ k, 0 < k ∧ (ρ ^ k) i0 = i0 :=
        ⟨orderOf ρ, orderOf_pos ρ, by rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]⟩
      obtain ⟨hl, hper⟩ := Nat.find_spec hex
      have hmin : ∀ k, 0 < k → k < Nat.find hex → (ρ ^ k) i0 ≠ i0 :=
        fun k hk hkl heq => absurd (Nat.find_min' hex ⟨hk, heq⟩) (by omega)
      have hsub := c_orb_sub ρ i0 (Nat.find hex) A hi0 hA
      have hinv := c_orb_inv ρ i0 (Nat.find hex) hl hper
      have hback := c_orb_back ρ i0 (Nat.find hex) hl hper
      have hmem : i0 ∈ c_orb ρ i0 (Nat.find hex) := (c_mem_orb ρ i0 _ i0).2 ⟨0, hl, by simp⟩
      have hinvc : ∀ i ∈ A \ c_orb ρ i0 (Nat.find hex),
          ρ i ∈ A \ c_orb ρ i0 (Nat.find hex) := by
        intro i hi
        rw [Finset.mem_sdiff] at hi ⊢
        exact ⟨hA i hi.1, fun h => hi.2 (hback i h)⟩
      have hlt : (A \ c_orb ρ i0 (Nat.find hex)).card < N := by
        have h1 := Finset.card_sdiff_add_card_eq_card hsub
        have h2 : 0 < (c_orb ρ i0 (Nat.find hex)).card := Finset.card_pos.2 ⟨i0, hmem⟩
        omega
      rw [← Finset.union_sdiff_of_subset hsub, c_split ρ pin _ _ Finset.disjoint_sdiff hinv hinvc]
      exact c_closed _ _ (c_cycle ρ pin i0 (Nat.find hex) hl hper hmin) (ih _ hlt _ rfl hinvc)
theorem c_first {V : Type} [Fintype V] [DecidableEq V] (n : ℕ) (pin : V → Option Bool)
    (F1 F2 : (V → Bool) → ℕ) (h1 : ∀ x, F1 x ≤ n) (h2 : ∀ x, F2 x ≤ n)
    (h : h_BoxSum (c_img pin (fun x => (F1 x, F2 x)))) :
    h_BoxSum (((Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun d =>
      0 < ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧ F1 x = d.1.val ∧ F2 x = d.2.val)).card)).image
      (fun d => (d.1.val, d.2.val))) := by
  have e : ((Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun d =>
      0 < ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧ F1 x = d.1.val ∧ F2 x = d.2.val)).card)).image
      (fun d => (d.1.val, d.2.val)) = c_img pin (fun x => (F1 x, F2 x)) := by
    ext p
    simp only [c_img, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.card_pos, Finset.Nonempty]
    constructor
    · rintro ⟨d, ⟨x, hx, e1, e2⟩, rfl⟩
      exact ⟨x, hx, by rw [e1, e2]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨F1 x, Nat.lt_succ_of_le (h1 x)⟩, ⟨F2 x, Nat.lt_succ_of_le (h2 x)⟩),
        ⟨x, hx, rfl, rfl⟩, rfl⟩
  rw [e]
  exact h
theorem h_bridge (n : ℕ) (M : Bool → Equiv.Perm (Fin n)) (pin : Bool × Fin n → Option Bool) :
    h_BoxSum (((Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun d =>
      0 < ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card = d.2.val)).card)).image
      (fun d => (d.1.val, d.2.val))) := by
  refine c_first n pin
    (fun x => (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card)
    (fun x => (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card)
    (fun x => (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n))
    (fun x => (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)) ?_
  have he : Function.Injective (fun v : Bool × Fin n => (v.1, cond v.1 (M false v.2) v.2)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have h1 : a = b := congrArg Prod.fst h
    subst h1
    have h2 : cond a (M false i) i = cond a (M false j) j := congrArg Prod.snd h
    cases a
    · exact Prod.ext rfl h2
    · have h3 : M false i = M false j := h2
      exact Prod.ext rfl ((M false).injective h3)
  rw [c_transport _ he pin _ (c_F ((M true).trans (M false).symm) Finset.univ) ?_]
  · exact c_main _ _ _ Finset.univ rfl (fun i _ => Finset.mem_univ _)
  · intro x
    show ((Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card,
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card) =
      ((Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card,
        (Finset.univ.filter (fun i : Fin n =>
          x (false,i) ≠ x (true,M false ((M false).symm (M true i))))).card)
    simp only [Equiv.apply_symm_apply]
abbrev o_iz (m1 M1 m2 M2 ms Ms md Md x y : ℤ) : Prop :=
  (x + y - ms) % 2 = 0 ∧ m1 ≤ x ∧ x ≤ M1 ∧ m2 ≤ y ∧ y ≤ M2 ∧
  ms ≤ x + y ∧ x + y ≤ Ms ∧ md ≤ x - y ∧ x - y ≤ Md
abbrev o_in (m1 M1 m2 M2 ms Ms md Md : ℤ) (x : ℕ × ℕ) : Prop :=
  o_iz m1 M1 m2 M2 ms Ms md Md x.1 x.2
def o_sat (S : Finset (ℕ × ℕ)) (m1 M1 m2 M2 ms Ms md Md : ℤ) : Prop :=
  (∀ x, x ∈ S ↔ o_in m1 M1 m2 M2 ms Ms md Md x) ∧
  (∃ x ∈ S, (x.1 : ℤ) = m1) ∧ (∃ x ∈ S, (x.1 : ℤ) = M1) ∧
  (∃ x ∈ S, (x.2 : ℤ) = m2) ∧ (∃ x ∈ S, (x.2 : ℤ) = M2) ∧
  (∃ x ∈ S, (x.1 : ℤ) + x.2 = ms) ∧ (∃ x ∈ S, (x.1 : ℤ) + x.2 = Ms) ∧
  (∃ x ∈ S, (x.1 : ℤ) - x.2 = md) ∧ (∃ x ∈ S, (x.1 : ℤ) - x.2 = Md)
theorem o_mem_box (a b : ℕ) (π : Bool) (q : ℕ) (hq : (if π then 1 else 0) = q) (e : ℕ × ℕ) :
    e ∈ h_box a b π ↔ e.1 ≤ a ∧ e.2 ≤ b ∧ (e.1 + e.2) % 2 = q := by
  unfold h_box
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range, hq]
  omega
theorem o_mem_add (S T : Finset (ℕ × ℕ)) (z : ℕ × ℕ) :
    z ∈ h_add S T ↔ ∃ s ∈ S, ∃ e ∈ T, z = (s.1 + e.1, s.2 + e.2) := by
  unfold h_add
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨s, e⟩, h, rfl⟩
    rw [Finset.mem_product] at h
    exact ⟨s, h.1, e, h.2, rfl⟩
  · rintro ⟨s, hs, e, he, rfl⟩
    exact ⟨(s, e), Finset.mem_product.2 ⟨hs, he⟩, rfl⟩
theorem o_pt (A1 B1 A2 B2 S1 S2 D1 D2 p : ℤ)
    (q1 : (S1 - p) % 2 = 0) (q2 : (S2 - p) % 2 = 0) (q3 : (D1 - p) % 2 = 0) (q4 : (D2 - p) % 2 = 0)
    (h1 : A1 ≤ B1) (h2 : A2 ≤ B2) (h3 : D1 ≤ D2)
    (hs : max (max S1 (2*A1 - D2)) (max (2*A2 + D1) (A1 + A2 + (A1 + A2 - p) % 2)) ≤
          min (min S2 (2*B1 - D1)) (min (2*B2 + D2) (B1 + B2 - (B1 + B2 - p) % 2))) :
    ∃ y1 y2 : ℤ, A1 ≤ y1 ∧ y1 ≤ B1 ∧ A2 ≤ y2 ∧ y2 ≤ B2 ∧ S1 ≤ y1 + y2 ∧ y1 + y2 ≤ S2 ∧
      D1 ≤ y1 - y2 ∧ y1 - y2 ≤ D2 ∧ (y1 + y2 - p) % 2 = 0 := by
  obtain ⟨s, hsd⟩ : ∃ s, s = max (max S1 (2*A1 - D2)) (max (2*A2 + D1) (A1 + A2 + (A1 + A2 - p) % 2)) :=
    ⟨_, rfl⟩
  have e1 : S1 ≤ s := by rw [hsd]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : 2*A1 - D2 ≤ s := by rw [hsd]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : 2*A2 + D1 ≤ s := by rw [hsd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : A1 + A2 + (A1 + A2 - p) % 2 ≤ s := by
    rw [hsd]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  rw [← hsd] at hs
  have f1 : s ≤ S2 := le_trans hs (le_trans (min_le_left _ _) (min_le_left _ _))
  have f2 : s ≤ 2*B1 - D1 := le_trans hs (le_trans (min_le_left _ _) (min_le_right _ _))
  have f3 : s ≤ 2*B2 + D2 := le_trans hs (le_trans (min_le_right _ _) (min_le_left _ _))
  have f4 : s ≤ B1 + B2 - (B1 + B2 - p) % 2 :=
    le_trans hs (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsp : (s - p) % 2 = 0 := by
    rcases max_choice (max S1 (2*A1 - D2)) (max (2*A2 + D1) (A1 + A2 + (A1 + A2 - p) % 2)) with h | h <;>
      rw [h] at hsd
    · rcases max_choice S1 (2*A1 - D2) with h' | h' <;> rw [h'] at hsd <;> omega
    · rcases max_choice (2*A2 + D1) (A1 + A2 + (A1 + A2 - p) % 2) with h' | h' <;> rw [h'] at hsd <;> omega
  clear hs
  obtain ⟨d, hdd⟩ : ∃ d, d = max D1 (max (2*A1 - s) (s - 2*B2)) := ⟨_, rfl⟩
  have g1 : D1 ≤ d := by rw [hdd]; exact le_max_left _ _
  have g2 : 2*A1 - s ≤ d := by rw [hdd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have g3 : s - 2*B2 ≤ d := by rw [hdd]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hd : d ≤ D2 ∧ d ≤ 2*B1 - s ∧ d ≤ s - 2*A2 ∧ (d - p) % 2 = 0 := by
    rcases max_choice D1 (max (2*A1 - s) (s - 2*B2)) with h | h <;> rw [h] at hdd
    · omega
    · rcases max_choice (2*A1 - s) (s - 2*B2) with h' | h' <;> rw [h'] at hdd <;> omega
  clear hsd hdd
  refine ⟨(s + d) / 2, (s - d) / 2, ?_⟩
  omega
theorem o_pt2 (A1 B1 A2 B2 S1 S2 D1 D2 p : ℤ)
    (q1 : (S1 - p) % 2 = 0) (q2 : (S2 - p) % 2 = 0) (q3 : (D1 - p) % 2 = 0) (q4 : (D2 - p) % 2 = 0)
    (h1 : A1 ≤ B1) (h2 : A2 ≤ B2) (h3 : D1 ≤ D2)
    (c1 : max (max S1 (2*A1 - D2)) (max (2*A2 + D1) (A1 + A2)) ≤
      min (min S2 (2*B1 - D1)) (min (2*B2 + D2) (B1 + B2)))
    (c2 : A1 + A2 = B1 + B2 → (A1 + A2 - p) % 2 = 0) :
    ∃ y1 y2 : ℤ, A1 ≤ y1 ∧ y1 ≤ B1 ∧ A2 ≤ y2 ∧ y2 ≤ B2 ∧ S1 ≤ y1 + y2 ∧ y1 + y2 ≤ S2 ∧
      D1 ≤ y1 - y2 ∧ y1 - y2 ≤ D2 ∧ (y1 + y2 - p) % 2 = 0 := by
  simp only [max_le_iff, le_min_iff] at c1
  apply o_pt A1 B1 A2 B2 S1 S2 D1 D2 p q1 q2 q3 q4 h1 h2 h3
  simp only [max_le_iff, le_min_iff]
  omega
theorem o_pt3 (A1 B1 A2 B2 S1 S2 D1 D2 p : ℤ)
    (q1 : (S1 - p) % 2 = 0) (q2 : (S2 - p) % 2 = 0) (q3 : (D1 - p) % 2 = 0) (q4 : (D2 - p) % 2 = 0)
    (h1 : A1 ≤ B1) (h2 : A2 ≤ B2) (h3 : D1 ≤ D2)
    (c11 : S1 ≤ S2) (c12 : S1 ≤ 2*B1 - D1) (c13 : S1 ≤ 2*B2 + D2) (c14 : S1 ≤ B1 + B2)
    (c21 : 2*A1 - D2 ≤ S2) (c22 : 2*A1 - D2 ≤ 2*B1 - D1) (c23 : 2*A1 - D2 ≤ 2*B2 + D2)
    (c24 : 2*A1 - D2 ≤ B1 + B2)
    (c31 : 2*A2 + D1 ≤ S2) (c32 : 2*A2 + D1 ≤ 2*B1 - D1) (c33 : 2*A2 + D1 ≤ 2*B2 + D2)
    (c34 : 2*A2 + D1 ≤ B1 + B2)
    (c41 : A1 + A2 ≤ S2) (c42 : A1 + A2 ≤ 2*B1 - D1) (c43 : A1 + A2 ≤ 2*B2 + D2)
    (c5 : A1 + A2 = B1 + B2 → (A1 + A2 - p) % 2 = 0) :
    ∃ y1 y2 : ℤ, A1 ≤ y1 ∧ y1 ≤ B1 ∧ A2 ≤ y2 ∧ y2 ≤ B2 ∧ S1 ≤ y1 + y2 ∧ y1 + y2 ≤ S2 ∧
      D1 ≤ y1 - y2 ∧ y1 - y2 ≤ D2 ∧ (y1 + y2 - p) % 2 = 0 := by
  apply o_pt2 A1 B1 A2 B2 S1 S2 D1 D2 p q1 q2 q3 q4 h1 h2 h3 _ c5
  simp only [max_le_iff, le_min_iff]
  omega
abbrev o_cl (m1 M1 m2 M2 ms Ms md Md : ℤ) : Prop :=
  m2 ≤ M2 ∧ m2 ≤ Ms - m1 ∧ m2 ≤ m1 - md ∧ ms - m1 ≤ M2 ∧ ms - m1 ≤ Ms - m1 ∧ ms - m1 ≤ m1 - md ∧ m1 - Md ≤ M2 ∧ m1 - Md ≤ Ms - m1 ∧ m1 - Md ≤ m1 - md ∧
  m2 ≤ Ms - M1 ∧ m2 ≤ M1 - md ∧ ms - M1 ≤ M2 ∧ ms - M1 ≤ Ms - M1 ∧ ms - M1 ≤ M1 - md ∧ M1 - Md ≤ M2 ∧ M1 - Md ≤ Ms - M1 ∧ M1 - Md ≤ M1 - md ∧
  m1 ≤ M1 ∧ m1 ≤ Ms - m2 ∧ m1 ≤ Md + m2 ∧ ms - m2 ≤ M1 ∧ ms - m2 ≤ Ms - m2 ∧ ms - m2 ≤ Md + m2 ∧ md + m2 ≤ M1 ∧ md + m2 ≤ Ms - m2 ∧ md + m2 ≤ Md + m2 ∧
  m1 ≤ Ms - M2 ∧ m1 ≤ Md + M2 ∧ ms - M2 ≤ M1 ∧ ms - M2 ≤ Ms - M2 ∧ ms - M2 ≤ Md + M2 ∧ md + M2 ≤ M1 ∧ md + M2 ≤ Ms - M2 ∧ md + M2 ≤ Md + M2 ∧
  m1 ≤ ms - m2 ∧ ms - M2 ≤ ms - m2 ∧ 2 * (m1) ≤ ms + Md ∧ 2 * (ms - M2) ≤ ms + Md ∧ ms + md ≤ 2 * (M1) ∧ ms + md ≤ 2 * (ms - m2) ∧ ms + md ≤ ms + Md ∧
  Ms - M2 ≤ M1 ∧ Ms - M2 ≤ Ms - m2 ∧ 2 * (m1) ≤ Ms + Md ∧ 2 * (Ms - M2) ≤ Ms + Md ∧ Ms + md ≤ 2 * (M1) ∧ Ms + md ≤ 2 * (Ms - m2) ∧ Ms + md ≤ Ms + Md ∧ (Ms - ms) % 2 = 0 ∧
  m1 ≤ md + M2 ∧ md + m2 ≤ md + M2 ∧ 2 * (m1) ≤ Ms + md ∧ 2 * (md + m2) ≤ Ms + md ∧ ms + md ≤ 2 * (md + M2) ∧ ms + md ≤ Ms + md ∧ (md - ms) % 2 = 0 ∧
  Md + m2 ≤ M1 ∧ Md + m2 ≤ Md + M2 ∧ 2 * (Md + m2) ≤ Ms + Md ∧ ms + Md ≤ 2 * (M1) ∧ ms + Md ≤ 2 * (Md + M2) ∧ ms + Md ≤ Ms + Md ∧ (Md - ms) % 2 = 0
theorem o_c1 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x = m1) :
    m2 ≤ M2 ∧ m2 ≤ Ms - m1 ∧ m2 ≤ m1 - md ∧ ms - m1 ≤ M2 ∧ ms - m1 ≤ Ms - m1 ∧ ms - m1 ≤ m1 - md ∧ m1 - Md ≤ M2 ∧ m1 - Md ≤ Ms - m1 ∧ m1 - Md ≤ m1 - md := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c2 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x = M1) :
    m2 ≤ Ms - M1 ∧ m2 ≤ M1 - md ∧ ms - M1 ≤ M2 ∧ ms - M1 ≤ Ms - M1 ∧ ms - M1 ≤ M1 - md ∧ M1 - Md ≤ M2 ∧ M1 - Md ≤ Ms - M1 ∧ M1 - Md ≤ M1 - md := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c3 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : y = m2) :
    m1 ≤ M1 ∧ m1 ≤ Ms - m2 ∧ m1 ≤ Md + m2 ∧ ms - m2 ≤ M1 ∧ ms - m2 ≤ Ms - m2 ∧ ms - m2 ≤ Md + m2 ∧ md + m2 ≤ M1 ∧ md + m2 ≤ Ms - m2 ∧ md + m2 ≤ Md + m2 := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c4 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : y = M2) :
    m1 ≤ Ms - M2 ∧ m1 ≤ Md + M2 ∧ ms - M2 ≤ M1 ∧ ms - M2 ≤ Ms - M2 ∧ ms - M2 ≤ Md + M2 ∧ md + M2 ≤ M1 ∧ md + M2 ≤ Ms - M2 ∧ md + M2 ≤ Md + M2 := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c5 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x + y = ms) :
    m1 ≤ ms - m2 ∧ ms - M2 ≤ ms - m2 ∧ 2 * (m1) ≤ ms + Md ∧ 2 * (ms - M2) ≤ ms + Md ∧ ms + md ≤ 2 * (M1) ∧ ms + md ≤ 2 * (ms - m2) ∧ ms + md ≤ ms + Md := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c6 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x + y = Ms) :
    Ms - M2 ≤ M1 ∧ Ms - M2 ≤ Ms - m2 ∧ 2 * (m1) ≤ Ms + Md ∧ 2 * (Ms - M2) ≤ Ms + Md ∧ Ms + md ≤ 2 * (M1) ∧ Ms + md ≤ 2 * (Ms - m2) ∧ Ms + md ≤ Ms + Md ∧ (Ms - ms) % 2 = 0 := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c7 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x - y = md) :
    m1 ≤ md + M2 ∧ md + m2 ≤ md + M2 ∧ 2 * (m1) ≤ Ms + md ∧ 2 * (md + m2) ≤ Ms + md ∧ ms + md ≤ 2 * (md + M2) ∧ ms + md ≤ Ms + md ∧ (md - ms) % 2 = 0 := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_c8 (m1 M1 m2 M2 ms Ms md Md x y : ℤ) (k : o_iz m1 M1 m2 M2 ms Ms md Md x y) (e : x - y = Md) :
    Md + m2 ≤ M1 ∧ Md + m2 ≤ Md + M2 ∧ 2 * (Md + m2) ≤ Ms + Md ∧ ms + Md ≤ 2 * (M1) ∧ ms + Md ≤ 2 * (Md + M2) ∧ ms + Md ≤ Ms + Md ∧ (Md - ms) % 2 = 0 := by
  unfold o_iz at k
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem o_clos (m1 M1 m2 M2 ms Ms md Md x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 x8 y8 : ℤ)
    (k1 : o_iz m1 M1 m2 M2 ms Ms md Md x1 y1) (e1 : x1 = m1)
    (k2 : o_iz m1 M1 m2 M2 ms Ms md Md x2 y2) (e2 : x2 = M1)
    (k3 : o_iz m1 M1 m2 M2 ms Ms md Md x3 y3) (e3 : y3 = m2)
    (k4 : o_iz m1 M1 m2 M2 ms Ms md Md x4 y4) (e4 : y4 = M2)
    (k5 : o_iz m1 M1 m2 M2 ms Ms md Md x5 y5) (e5 : x5 + y5 = ms)
    (k6 : o_iz m1 M1 m2 M2 ms Ms md Md x6 y6) (e6 : x6 + y6 = Ms)
    (k7 : o_iz m1 M1 m2 M2 ms Ms md Md x7 y7) (e7 : x7 - y7 = md)
    (k8 : o_iz m1 M1 m2 M2 ms Ms md Md x8 y8) (e8 : x8 - y8 = Md)
    : o_cl m1 M1 m2 M2 ms Ms md Md := by
  obtain ⟨f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f1_7, f1_8, f1_9⟩ := o_c1 m1 M1 m2 M2 ms Ms md Md x1 y1 k1 e1
  obtain ⟨f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7, f2_8⟩ := o_c2 m1 M1 m2 M2 ms Ms md Md x2 y2 k2 e2
  obtain ⟨f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f3_7, f3_8, f3_9⟩ := o_c3 m1 M1 m2 M2 ms Ms md Md x3 y3 k3 e3
  obtain ⟨f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f4_7, f4_8⟩ := o_c4 m1 M1 m2 M2 ms Ms md Md x4 y4 k4 e4
  obtain ⟨f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f5_7⟩ := o_c5 m1 M1 m2 M2 ms Ms md Md x5 y5 k5 e5
  obtain ⟨f6_1, f6_2, f6_3, f6_4, f6_5, f6_6, f6_7, f6_8⟩ := o_c6 m1 M1 m2 M2 ms Ms md Md x6 y6 k6 e6
  obtain ⟨f7_1, f7_2, f7_3, f7_4, f7_5, f7_6, f7_7⟩ := o_c7 m1 M1 m2 M2 ms Ms md Md x7 y7 k7 e7
  obtain ⟨f8_1, f8_2, f8_3, f8_4, f8_5, f8_6, f8_7⟩ := o_c8 m1 M1 m2 M2 ms Ms md Md x8 y8 k8 e8
  unfold o_cl
  exact ⟨f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f1_7, f1_8, f1_9, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7, f2_8, f3_1, f3_2, f3_3, f3_4, f3_5, f3_6, f3_7, f3_8, f3_9, f4_1, f4_2, f4_3, f4_4, f4_5, f4_6, f4_7, f4_8, f5_1, f5_2, f5_3, f5_4, f5_5, f5_6, f5_7, f6_1, f6_2, f6_3, f6_4, f6_5, f6_6, f6_7, f6_8, f7_1, f7_2, f7_3, f7_4, f7_5, f7_6, f7_7, f8_1, f8_2, f8_3, f8_4, f8_5, f8_6, f8_7⟩
theorem o_wit (m1 M1 m2 M2 ms Ms md Md z1 z2 a b q : ℤ) (hc : o_cl m1 M1 m2 M2 ms Ms md Md)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha : 1 ≤ a) (hb : 1 ≤ b) (_hab : a ≤ b + 1) (_hba : b ≤ a + 1)
    (hz : o_iz m1 (M1 + a) m2 (M2 + b) (ms + q) (Ms + (a + b - (a + b + q) % 2)) (md - b + (b + q) % 2)
      (Md + a - (a + q) % 2) z1 z2) :
    ∃ w1 w2 : ℤ, o_iz m1 M1 m2 M2 ms Ms md Md w1 w2 ∧ 0 ≤ z1 - w1 ∧ z1 - w1 ≤ a ∧ 0 ≤ z2 - w2 ∧
      z2 - w2 ≤ b ∧ (z1 - w1 + (z2 - w2) - q) % 2 = 0 := by
  unfold o_cl at hc
  unfold o_iz at hz
  obtain ⟨hzp, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8⟩ := hz
  have p1 : ms ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p2 : ms + md ≤ 2 * M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p3 : ms + md ≤ 2 * m1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p4 : ms - Md ≤ 2 * M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p5 : ms - Md ≤ 2 * m2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p6 : ms ≤ M1 + M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p7 : ms ≤ M1 + m2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p8 : ms ≤ m1 + M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p9 : 2 * m1 ≤ Ms + Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p10 : 2 * M1 ≤ Ms + Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p11 : m1 ≤ M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p12 : md ≤ Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p13 : m1 - M2 ≤ Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p14 : m1 - m2 ≤ Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p15 : M1 - M2 ≤ Md := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p16 : 2 * m2 + md ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p17 : 2 * M2 + md ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p18 : m2 + md ≤ M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p19 : m2 + md ≤ m1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p20 : M2 + md ≤ M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p21 : m1 + m2 ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p22 : m1 + M2 ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p23 : M1 + m2 ≤ Ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p24 : Ms + md ≤ 2 * M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p25 : Ms - Md ≤ 2 * M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p26 : m2 ≤ M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have p27 : m1 + m2 ≤ ms := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have r1 : m1 ≤ Ms - M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have r2 : Ms - M2 ≤ M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have r3 : m1 ≤ md + M2 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have r4 : m2 ≤ Ms - M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have r5 : Md + m2 ≤ M1 := by clear hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8; omega
  have g5 : ms ≤ z1 + z2 := by clear * - hz5 hq0; omega
  have g6 : z1 + z2 ≤ Ms + a + b := by clear * - hz6; omega
  have g7 : md - b ≤ z1 - z2 := by clear * - hz7; omega
  have g8 : z1 - z2 ≤ Md + a := by clear * - hz8; omega
  have q2 : (Ms - ms) % 2 = 0 := by clear * - hc; omega
  have q3 : (md - ms) % 2 = 0 := by clear * - hc; omega
  have q4 : (Md - ms) % 2 = 0 := by clear * - hc; omega
  have c5 : max m1 (z1 - a) + max m2 (z2 - b) = min M1 z1 + min M2 z2 → (max m1 (z1 - a) + max m2 (z2 - b) - ms) % 2 = 0 := by
    clear * - p27 p6 p7 p8 r1 r2 r3 r4 r5 q2 q3 q4 hzp hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hq0 hq1 ha hb
    omega
  obtain ⟨w1, w2, h⟩ := o_pt3 (max m1 (z1 - a)) (min M1 z1) (max m2 (z2 - b)) (min M2 z2) ms Ms md Md ms
    (by omega)
    q2
    q3
    q4
    (by clear * - p11 hz1 hz2 ha; omega)
    (by clear * - p26 hz3 hz4 hb; omega)
    p12
    (show ms ≤ Ms by clear * - p1; omega)
    (show ms ≤ 2 * min M1 z1 - md by clear * - p2 p3 hz1; omega)
    (show ms ≤ 2 * min M2 z2 + Md by clear * - p4 p5 hz3; omega)
    (show ms ≤ min M1 z1 + min M2 z2 by clear * - p6 p7 p8 hz1 hz3 g5; omega)
    (show 2 * max m1 (z1 - a) - Md ≤ Ms by clear * - p9 p10 hz2; omega)
    (show 2 * max m1 (z1 - a) - Md ≤ 2 * min M1 z1 - md by clear * - p11 p12 hz1 hz2 ha; omega)
    (show 2 * max m1 (z1 - a) - Md ≤ 2 * min M2 z2 + Md by clear * - p13 p14 p15 hz2 hz3 g8; omega)
    (show 2 * max m1 (z1 - a) - Md ≤ min M1 z1 + min M2 z2 by clear * - p11 p13 p14 p15 hz1 hz2 hz3 g8 ha; omega)
    (show 2 * max m2 (z2 - b) + md ≤ Ms by clear * - p16 p17 hz4; omega)
    (show 2 * max m2 (z2 - b) + md ≤ 2 * min M1 z1 - md by clear * - p18 p19 p20 hz1 hz4 g7; omega)
    (show 2 * max m2 (z2 - b) + md ≤ 2 * min M2 z2 + Md by clear * - p26 p12 hz3 hz4 hb; omega)
    (show 2 * max m2 (z2 - b) + md ≤ min M1 z1 + min M2 z2 by clear * - p26 p18 p19 p20 hz1 hz3 hz4 g7 hb; omega)
    (show max m1 (z1 - a) + max m2 (z2 - b) ≤ Ms by clear * - p21 p22 p23 hz2 hz4 g6; omega)
    (show max m1 (z1 - a) + max m2 (z2 - b) ≤ 2 * min M1 z1 - md by clear * - p11 p18 p19 p20 p24 hz1 hz2 hz4 g6 g7 ha hb; omega)
    (show max m1 (z1 - a) + max m2 (z2 - b) ≤ 2 * min M2 z2 + Md by clear * - p26 p13 p14 p15 p25 hz2 hz3 hz4 g6 g8 ha hb; omega)
    c5
  simp only [max_le_iff, le_min_iff] at h
  refine ⟨w1, w2, ?_⟩
  clear * - h hzp hq0 hq1
  unfold o_iz
  omega
set_option maxHeartbeats 1000000 in
theorem o_key (S : Finset (ℕ × ℕ)) (m1 M1 m2 M2 ms Ms md Md : ℤ)
    (hS : o_sat S m1 M1 m2 M2 ms Ms md Md) (a b q : ℕ) (π : Bool) (hq : (if π then 1 else 0) = q)
    (hq1 : q ≤ 1) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    o_sat (h_add S (h_box a b π)) m1 (M1 + a) m2 (M2 + b) (ms + q)
      (Ms + (a + b - ((a:ℤ) + b + q) % 2)) (md - b + ((b:ℤ) + q) % 2)
      (Md + a - ((a:ℤ) + q) % 2) := by
  obtain ⟨hmem, ⟨u1, hu1, eu1⟩, ⟨u2, hu2, eu2⟩, ⟨u3, hu3, eu3⟩, ⟨u4, hu4, eu4⟩,
    ⟨u5, hu5, eu5⟩, ⟨u6, hu6, eu6⟩, ⟨u7, hu7, eu7⟩, ⟨u8, hu8, eu8⟩⟩ := hS
  have k1 := (hmem u1).1 hu1
  have hbox := o_mem_box a b π q hq
  refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o_mem_add] at hz
    obtain ⟨s, hs, e, he, rfl⟩ := hz
    have ks := (hmem s).1 hs
    rw [hbox] at he
    clear k1
    simp only [o_in, o_iz] at ks ⊢
    push_cast
    omega
  · obtain ⟨z1, z2⟩ := z
    have k2 := (hmem u2).1 hu2
    have k3 := (hmem u3).1 hu3
    have k4 := (hmem u4).1 hu4
    have k5 := (hmem u5).1 hu5
    have k6 := (hmem u6).1 hu6
    have k7 := (hmem u7).1 hu7
    have k8 := (hmem u8).1 hu8
    obtain ⟨w1, w2, hw, h1, h2, h3, h4, h5⟩ := o_wit m1 M1 m2 M2 ms Ms md Md z1 z2 a b q
      (o_clos m1 M1 m2 M2 ms Ms md Md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        k1 eu1 k2 eu2 k3 eu3 k4 eu4 k5 eu5 k6 eu6 k7 eu7 k8 eu8)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz
    simp only [o_iz] at hw k1
    have hy1 : ((w1.toNat : ℕ) : ℤ) = w1 := Int.toNat_of_nonneg (by omega)
    have hy2 : ((w2.toNat : ℕ) : ℤ) = w2 := Int.toNat_of_nonneg (by omega)
    rw [o_mem_add]
    refine ⟨(w1.toNat, w2.toNat), (hmem _).2 ?_, (z1 - w1.toNat, z2 - w2.toNat), (hbox _).2 ?_, ?_⟩
    · simp only [o_in, o_iz, hy1, hy2]
      omega
    · simp only
      omega
    · simp only [Prod.mk.injEq]
      omega
  · exact ⟨(u1.1 + 0, u1.2 + q), (o_mem_add _ _ _).2 ⟨u1, hu1, (0, q), (hbox _).2 (by simp only; omega), rfl⟩,
      by push_cast; omega⟩
  · exact ⟨(u2.1 + a, u2.2 + (a + q) % 2), (o_mem_add _ _ _).2 ⟨u2, hu2, (a, (a + q) % 2),
      (hbox _).2 (by simp only; omega), rfl⟩, by push_cast; omega⟩
  · exact ⟨(u3.1 + q, u3.2 + 0), (o_mem_add _ _ _).2 ⟨u3, hu3, (q, 0), (hbox _).2 (by simp only; omega), rfl⟩,
      by push_cast; omega⟩
  · exact ⟨(u4.1 + (b + q) % 2, u4.2 + b), (o_mem_add _ _ _).2 ⟨u4, hu4, ((b + q) % 2, b),
      (hbox _).2 (by simp only; omega), rfl⟩, by push_cast; omega⟩
  · exact ⟨(u5.1 + q, u5.2 + 0), (o_mem_add _ _ _).2 ⟨u5, hu5, (q, 0), (hbox _).2 (by simp only; omega), rfl⟩,
      by push_cast; omega⟩
  · exact ⟨(u6.1 + a, u6.2 + (b - (a + b + q) % 2)), (o_mem_add _ _ _).2 ⟨u6, hu6, (a, b - (a + b + q) % 2),
      (hbox _).2 (by simp only; omega), rfl⟩, by push_cast; omega⟩
  · exact ⟨(u7.1 + (b + q) % 2, u7.2 + b), (o_mem_add _ _ _).2 ⟨u7, hu7, ((b + q) % 2, b),
      (hbox _).2 (by simp only; omega), rfl⟩, by push_cast; omega⟩
  · exact ⟨(u8.1 + a, u8.2 + (a + q) % 2), (o_mem_add _ _ _).2 ⟨u8, hu8, (a, (a + q) % 2),
      (hbox _).2 (by simp only; omega), rfl⟩, by push_cast; omega⟩
set_option maxHeartbeats 1000000 in
theorem o_shift (S T : Finset (ℕ × ℕ)) (m1 M1 m2 M2 ms Ms md Md : ℤ)
    (hS : o_sat S m1 M1 m2 M2 ms Ms md Md) (c1 c2 : ℕ) (hT : ∀ e, e ∈ T ↔ e = (c1, c2)) :
    o_sat (h_add S T) (m1 + c1) (M1 + c1) (m2 + c2) (M2 + c2) (ms + c1 + c2) (Ms + c1 + c2)
      (md + c1 - c2) (Md + c1 - c2) := by
  obtain ⟨hmem, ⟨u1, hu1, eu1⟩, ⟨u2, hu2, eu2⟩, ⟨u3, hu3, eu3⟩, ⟨u4, hu4, eu4⟩,
    ⟨u5, hu5, eu5⟩, ⟨u6, hu6, eu6⟩, ⟨u7, hu7, eu7⟩, ⟨u8, hu8, eu8⟩⟩ := hS
  have hc : (c1, c2) ∈ T := (hT _).2 rfl
  refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩,
    ⟨(u1.1 + c1, u1.2 + c2), (o_mem_add _ _ _).2 ⟨u1, hu1, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u2.1 + c1, u2.2 + c2), (o_mem_add _ _ _).2 ⟨u2, hu2, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u3.1 + c1, u3.2 + c2), (o_mem_add _ _ _).2 ⟨u3, hu3, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u4.1 + c1, u4.2 + c2), (o_mem_add _ _ _).2 ⟨u4, hu4, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u5.1 + c1, u5.2 + c2), (o_mem_add _ _ _).2 ⟨u5, hu5, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u6.1 + c1, u6.2 + c2), (o_mem_add _ _ _).2 ⟨u6, hu6, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u7.1 + c1, u7.2 + c2), (o_mem_add _ _ _).2 ⟨u7, hu7, (c1, c2), hc, rfl⟩, by push_cast; omega⟩,
    ⟨(u8.1 + c1, u8.2 + c2), (o_mem_add _ _ _).2 ⟨u8, hu8, (c1, c2), hc, rfl⟩, by push_cast; omega⟩⟩
  · rw [o_mem_add] at hz
    obtain ⟨s, hs, e, he, rfl⟩ := hz
    rw [hT] at he
    subst he
    have ks := (hmem s).1 hs
    simp only [o_in, o_iz] at ks ⊢
    push_cast
    omega
  · obtain ⟨z1, z2⟩ := z
    simp only [o_in, o_iz] at hz
    have l1 : c1 ≤ z1 := by omega
    have l2 : c2 ≤ z2 := by omega
    rw [o_mem_add]
    refine ⟨(z1 - c1, z2 - c2), (hmem _).2 ?_, (c1, c2), hc, ?_⟩
    · simp only [o_in, o_iz]
      push_cast [l1, l2]
      omega
    · simp only [Prod.mk.injEq]
      omega
theorem o_step (S : Finset (ℕ × ℕ)) (a b : ℕ) (π : Bool) (hab : a ≤ b + 1) (hba : b ≤ a + 1)
    (hS : S = ∅ ∨ ∃ m1 M1 m2 M2 ms Ms md Md : ℤ, o_sat S m1 M1 m2 M2 ms Ms md Md) :
    h_add S (h_box a b π) = ∅ ∨
      ∃ m1 M1 m2 M2 ms Ms md Md : ℤ, o_sat (h_add S (h_box a b π)) m1 M1 m2 M2 ms Ms md Md := by
  obtain ⟨q, hq, hq1⟩ : ∃ q : ℕ, (if π then 1 else 0) = q ∧ q ≤ 1 := ⟨_, rfl, by split <;> omega⟩
  have hbox := o_mem_box a b π q hq
  rcases hS with hS | ⟨m1, M1, m2, M2, ms, Ms, md, Md, hS⟩
  · left
    subst hS
    unfold h_add
    simp
  · by_cases h1 : 1 ≤ a ∧ 1 ≤ b
    · right
      exact ⟨_, _, _, _, _, _, _, _, o_key S m1 M1 m2 M2 ms Ms md Md hS a b q π hq hq1 h1.1 h1.2 hab hba⟩
    · by_cases h0 : a = 0 ∧ b = 0 ∧ q = 1
      · left
        have he : h_box a b π = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro e he
          rw [hbox] at he
          omega
        rw [he]
        unfold h_add
        simp
      · right
        exact ⟨_, _, _, _, _, _, _, _, o_shift S _ m1 M1 m2 M2 ms Ms md Md hS (min a q) (min b q)
          (fun e => by rw [hbox, Prod.ext_iff]; dsimp only; omega)⟩
theorem o_fold (L : List (ℕ × ℕ × Bool)) (hL : ∀ t ∈ L, t.1 ≤ t.2.1 + 1 ∧ t.2.1 ≤ t.1 + 1) :
    L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) {(0,0)} = ∅ ∨
    ∃ m1 M1 m2 M2 ms Ms md Md : ℤ,
      o_sat (L.foldr (fun t acc => h_add acc (h_box t.1 t.2.1 t.2.2)) {(0,0)}) m1 M1 m2 M2 ms Ms md Md := by
  induction L with
  | nil =>
    right
    refine ⟨0, 0, 0, 0, 0, 0, 0, 0, fun x => ?_, ⟨(0,0), by simp, by simp⟩, ⟨(0,0), by simp, by simp⟩,
      ⟨(0,0), by simp, by simp⟩, ⟨(0,0), by simp, by simp⟩, ⟨(0,0), by simp, by simp⟩,
      ⟨(0,0), by simp, by simp⟩, ⟨(0,0), by simp, by simp⟩, ⟨(0,0), by simp, by simp⟩⟩
    obtain ⟨x1, x2⟩ := x
    simp only [List.foldr_nil, Finset.mem_singleton, Prod.mk.injEq, o_in, o_iz]
    omega
  | cons t L ih =>
    rw [List.foldr_cons]
    exact o_step _ t.1 t.2.1 t.2.2 (hL t (by simp)).1 (hL t (by simp)).2
      (ih (fun t' ht' => hL t' (by simp [ht'])))
abbrev o_C (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) ×
  Fin (n+1) × Fin (n+1)
def o_dec (n : ℕ) (c : o_C n) : Finset (Fin (n+1) × Fin (n+1)) :=
  Finset.univ.filter (fun d => o_in ((c.1 : ℕ) : ℤ) ((c.2.1 : ℕ) : ℤ) ((c.2.2.1 : ℕ) : ℤ)
    ((c.2.2.2.1 : ℕ) : ℤ)
    (((c.2.2.2.2.2.1 : ℕ) : ℤ) + ((c.1 : ℕ) : ℤ) + ((c.2.2.1 : ℕ) : ℤ))
    (((c.2.2.2.2.1 : ℕ) : ℤ) + ((c.2.1 : ℕ) : ℤ) + ((c.2.2.1 : ℕ) : ℤ))
    (((c.2.2.2.2.2.2.2 : ℕ) : ℤ) + ((c.1 : ℕ) : ℤ) - ((c.2.2.2.1 : ℕ) : ℤ))
    (((c.2.2.2.2.2.2.1 : ℕ) : ℤ) + ((c.2.1 : ℕ) : ℤ) - ((c.2.2.2.1 : ℕ) : ℤ))
    ((d.1 : ℕ), (d.2 : ℕ)))
theorem o_code (n : ℕ) (S : Finset (ℕ × ℕ)) (m1 M1 m2 M2 ms Ms md Md : ℤ)
    (hS : o_sat S m1 M1 m2 M2 ms Ms md Md) (hn : ∀ x ∈ S, x.1 ≤ n ∧ x.2 ≤ n) :
    ∃ c : o_C n, ((c.1 : ℕ) : ℤ) = m1 ∧ ((c.2.1 : ℕ) : ℤ) = M1 ∧ ((c.2.2.1 : ℕ) : ℤ) = m2 ∧
      ((c.2.2.2.1 : ℕ) : ℤ) = M2 ∧ ((c.2.2.2.2.1 : ℕ) : ℤ) = Ms - M1 - m2 ∧
      ((c.2.2.2.2.2.1 : ℕ) : ℤ) = ms - m1 - m2 ∧ ((c.2.2.2.2.2.2.1 : ℕ) : ℤ) = Md - M1 + M2 ∧
      ((c.2.2.2.2.2.2.2 : ℕ) : ℤ) = md - m1 + M2 := by
  obtain ⟨hmem, ⟨u1, hu1, eu1⟩, ⟨u2, hu2, eu2⟩, ⟨u3, hu3, eu3⟩, ⟨u4, hu4, eu4⟩,
    ⟨u5, hu5, eu5⟩, ⟨u6, hu6, eu6⟩, ⟨u7, hu7, eu7⟩, ⟨u8, hu8, eu8⟩⟩ := hS
  have k1 := (hmem u1).1 hu1
  have k2 := (hmem u2).1 hu2
  have k4 := (hmem u4).1 hu4
  have k5 := (hmem u5).1 hu5
  have k6 := (hmem u6).1 hu6
  have k7 := (hmem u7).1 hu7
  have k8 := (hmem u8).1 hu8
  have n1 := hn u1 hu1
  have n2 := hn u2 hu2
  have n3 := hn u3 hu3
  have n4 := hn u4 hu4
  simp only [o_in, o_iz] at k1 k2 k4 k5 k6 k7 k8
  have r0 : 0 ≤ m1 ∧ m1 ≤ n := by omega
  have r1 : 0 ≤ M1 ∧ M1 ≤ n := by omega
  have r2 : 0 ≤ m2 ∧ m2 ≤ n := by omega
  have r3 : 0 ≤ M2 ∧ M2 ≤ n := by omega
  have r4 : 0 ≤ Ms - M1 - m2 ∧ Ms - M1 - m2 ≤ n := by omega
  have r5 : 0 ≤ ms - m1 - m2 ∧ ms - m1 - m2 ≤ n := by omega
  have r6 : 0 ≤ Md - M1 + M2 ∧ Md - M1 + M2 ≤ n := by omega
  have r7 : 0 ≤ md - m1 + M2 ∧ md - m1 + M2 ≤ n := by omega
  refine ⟨(⟨m1.toNat, by omega⟩, ⟨M1.toNat, by omega⟩, ⟨m2.toNat, by omega⟩, ⟨M2.toNat, by omega⟩,
    ⟨(Ms - M1 - m2).toNat, by omega⟩, ⟨(ms - m1 - m2).toNat, by omega⟩,
    ⟨(Md - M1 + M2).toNat, by omega⟩, ⟨(md - m1 + M2).toNat, by omega⟩), ?_⟩
  simp only
  omega
theorem h_upper : ∀ n : ℕ,
  let V := Bool × Fin n
  let Match := Bool → Equiv.Perm (Fin n)
  let Index := Fin (n+1) × Fin (n+1)
  let support := fun (M : Match) (pin : V → Option Bool) =>
    (Finset.univ : Finset Index).filter (fun d =>
      0 < ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card = d.2.val)).card)
  let classes := fun M : Match =>
    ((Finset.univ : Finset (V → Option Bool)).image (support M)).card
  (∀ M : Match, classes M ≤ (n+1)^8) := by
  intro n V Match Index support classes M
  have hinj : Function.Injective (fun d : Fin (n+1) × Fin (n+1) => ((d.1 : ℕ), (d.2 : ℕ))) := by
    intro d d' h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have key : ∀ pin : V → Option Bool, ∃ c : o_C n, support M pin = o_dec n c := by
    intro pin
    have hb : h_BoxSum ((support M pin).image (fun d : Fin (n+1) × Fin (n+1) => ((d.1 : ℕ), (d.2 : ℕ)))) :=
      h_bridge n M pin
    obtain ⟨L, hL, hSL⟩ := hb
    have hne : (support M pin).Nonempty := by
      refine ⟨(⟨(Finset.univ.filter (fun i : Fin n => (pin (false,i)).getD false ≠
          (pin (true,M false i)).getD false)).card, ?_⟩,
        ⟨(Finset.univ.filter (fun i : Fin n => (pin (false,i)).getD false ≠
          (pin (true,M true i)).getD false)).card, ?_⟩), ?_⟩
      · exact Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
      · exact Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
      · show _ ∈ Finset.filter _ _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Finset.card_pos.2 ⟨fun v => (pin v).getD false, ?_⟩⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun v => ?_, rfl, rfl⟩
        cases h : pin v <;> simp [h]
    rcases o_fold L hL with h0 | ⟨m1, M1, m2, M2, ms, Ms, md, Md, hS⟩
    · exfalso
      rw [← hSL] at h0
      obtain ⟨d, hd⟩ := hne
      have hm := Finset.mem_image_of_mem (fun d : Fin (n+1) × Fin (n+1) => ((d.1 : ℕ), (d.2 : ℕ))) hd
      rw [h0] at hm
      exact Finset.notMem_empty _ hm
    · rw [← hSL] at hS
      have hn : ∀ x ∈ (support M pin).image (fun d : Fin (n+1) × Fin (n+1) => ((d.1 : ℕ), (d.2 : ℕ))),
          x.1 ≤ n ∧ x.2 ≤ n := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨d, -, rfl⟩ := hx
        exact ⟨Nat.lt_succ_iff.1 d.1.2, Nat.lt_succ_iff.1 d.2.2⟩
      obtain ⟨c, h0, h1, h2, h3, h4, h5, h6, h7⟩ := o_code n _ _ _ _ _ _ _ _ _ hS hn
      refine ⟨c, ?_⟩
      ext d
      have e1 : d ∈ support M pin ↔ ((d.1 : ℕ), (d.2 : ℕ)) ∈
          (support M pin).image (fun d : Fin (n+1) × Fin (n+1) => ((d.1 : ℕ), (d.2 : ℕ))) :=
        hinj.mem_finset_image.symm
      rw [e1, hS.1, o_dec, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, o_in, o_iz]
      rw [h0, h1, h2, h3, h4, h5, h6, h7]
      constructor
      · intro h
        omega
      · intro h
        omega
  calc classes M = ((Finset.univ : Finset (V → Option Bool)).image (support M)).card := rfl
    _ ≤ ((Finset.univ : Finset (o_C n)).image (o_dec n)).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_image] at hs ⊢
        obtain ⟨pin, -, rfl⟩ := hs
        obtain ⟨c, hc⟩ := key pin
        exact ⟨c, Finset.mem_univ _, hc.symm⟩
    _ ≤ (Finset.univ : Finset (o_C n)).card := Finset.card_image_le
    _ = (n+1)^8 := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        ring
def l_sn (n j : ℕ) : ℕ := if j % 2 = 0 then (if j + 1 < n then j + 1 else j) else j - 1
theorem l_sn_lt {n j : ℕ} (h : j < n) : l_sn n j < n := by
  unfold l_sn; split_ifs <;> omega
theorem l_sn_sn {n j : ℕ} (h : j < n) : l_sn n (l_sn n j) = j := by
  unfold l_sn; split_ifs <;> omega
def l_sig (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨l_sn n i.1, l_sn_lt i.2⟩
  invFun i := ⟨l_sn n i.1, l_sn_lt i.2⟩
  left_inv i := Fin.ext (l_sn_sn i.2)
  right_inv i := Fin.ext (l_sn_sn i.2)
def l_M (n : ℕ) : Bool → Equiv.Perm (Fin n) := fun c => cond c (l_sig n) (Equiv.refl (Fin n))
def l_P (a b c e : Option Bool) (s p : Bool) : Option Bool := cond p (cond s e c) (cond s b a)
def l_pat : ℕ → Bool → Bool → Option Bool
  | 0 => l_P (some false) (some true) (some true) (some false)
  | 1 => l_P (some false) (some false) (some true) (some true)
  | 2 => l_P (some false) none (some false) (some false)
  | 3 => l_P (some false) none (some true) (some true)
  | 4 => l_P (some false) none none (some false)
  | 5 => l_P (some false) none none (some true)
  | 6 => l_P none none (some false) (some false)
  | 7 => l_P none none (some false) (some true)
  | _ => l_P (some false) (some false) (some false) (some false)
def l_ty (K : ℕ → ℕ) (p : ℕ) : ℕ := if p / 8 < K (p % 8) then p % 8 else 8
def l_pin (n : ℕ) (K : ℕ → ℕ) : Bool × Fin n → Option Bool :=
  fun v => l_pat (l_ty K (v.2.1 / 2)) v.1 (decide (v.2.1 % 2 = 1))
def l_sel (q : Bool × Bool × Bool × Bool) (s p : Bool) : Bool :=
  cond p (cond s q.2.2.2 q.2.2.1) (cond s q.2.1 q.1)
def l_f1 (q : Bool × Bool × Bool × Bool) : ℤ :=
  (if q.1 ≠ q.2.1 then 1 else 0) + (if q.2.2.1 ≠ q.2.2.2 then 1 else 0)
def l_f2 (q : Bool × Bool × Bool × Bool) : ℤ :=
  (if q.1 ≠ q.2.2.2 then 1 else 0) + (if q.2.2.1 ≠ q.2.1 then 1 else 0)
def l_xs (n : ℕ) (x : Bool × Fin n → Bool) (s : Bool) (j : ℕ) : Bool :=
  if h : j < n then x (s, ⟨j, h⟩) else false
def l_q (n : ℕ) (x : Bool × Fin n → Bool) (p : ℕ) : Bool × Bool × Bool × Bool :=
  (l_xs n x false (2*p), l_xs n x true (2*p), l_xs n x false (2*p+1), l_xs n x true (2*p+1))
def l_c1 (n : ℕ) (x : Bool × Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true, l_M n false i))).card
def l_c2 (n : ℕ) (x : Bool × Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true, l_M n true i))).card
def l_supp (n : ℕ) (M : Bool → Equiv.Perm (Fin n)) (pin : Bool × Fin n → Option Bool) :
    Finset (Fin (n+1) × Fin (n+1)) :=
  (Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun d =>
    0 < ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
      (∀ v, pin v = none ∨ pin v = some (x v)) ∧
      (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card = d.2.val)).card)
def l_wx (n : ℕ) (K : ℕ → ℕ) (w : ℕ → Bool × Bool × Bool × Bool) : Bool × Fin n → Bool :=
  fun v => l_sel (w (l_ty K (v.2.1 / 2))) v.1 (decide (v.2.1 % 2 = 1))
def l_v8 (v0 v1 v2 v3 v4 v5 v6 v7 : ℤ) : ℕ → ℤ
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | 3 => v3
  | 4 => v4
  | 5 => v5
  | 6 => v6
  | 7 => v7
  | _ => 0
def l_wl : ℕ → List (Bool × Bool × Bool × Bool)
  | 0 => [(false,true,true,false), (false,false,true,true), (false,true,false,false),
      (false,true,true,true), (false,true,true,false), (false,true,false,true),
      (false,true,false,false), (false,true,false,true)]
  | 1 => [(false,true,true,false), (false,false,true,true), (false,false,false,false),
      (false,false,true,true), (false,false,false,false), (false,false,true,true),
      (false,false,false,false), (false,false,false,true)]
  | 2 => [(false,true,true,false), (false,false,true,true), (false,true,false,false),
      (false,false,true,true), (false,false,true,false), (false,false,true,true),
      (true,true,false,false), (false,true,false,true)]
  | 3 => [(false,true,true,false), (false,false,true,true), (false,false,false,false),
      (false,true,true,true), (false,false,false,false), (false,false,false,true),
      (false,false,false,false), (true,false,false,true)]
  | 4 => [(false,true,true,false), (false,false,true,true), (false,true,false,false),
      (false,false,true,true), (false,true,true,false), (false,true,false,true),
      (false,true,false,false), (false,true,false,true)]
  | 5 => [(false,true,true,false), (false,false,true,true), (false,false,false,false),
      (false,false,true,true), (false,false,false,false), (false,false,false,true),
      (false,false,false,false), (false,false,false,true)]
  | 6 => [(false,true,true,false), (false,false,true,true), (false,false,false,false),
      (false,true,true,true), (false,true,true,false), (false,false,false,true),
      (false,false,false,false), (true,false,false,true)]
  | _ => [(false,true,true,false), (false,false,true,true), (false,false,false,false),
      (false,false,true,true), (false,false,false,false), (false,false,true,true),
      (true,true,false,false), (false,false,false,true)]
def l_w (j t : ℕ) : Bool × Bool × Bool × Bool := (l_wl j).getD t (false, false, false, false)
theorem l_ty_lt (K : ℕ → ℕ) (p : ℕ) : l_ty K p < 9 := by
  unfold l_ty; split_ifs <;> omega
theorem l_pair (f : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range (2*m), f i = ∑ p ∈ Finset.range m, (f (2*p) + f (2*p+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring
theorem l_group (f : ℕ → ℤ) (m : ℕ) :
    ∑ p ∈ Finset.range (8*m), f p = ∑ r ∈ Finset.range m, ∑ g ∈ Finset.range 8, f (8*r+g) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 8*(m+1) = 8*m+8 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun r => ∑ g ∈ Finset.range 8, f (8*r+g)) m]
theorem l_sumty (m : ℕ) (K : ℕ → ℕ) (hK : ∀ g, K g ≤ m) (H : ℕ → ℤ) (h8 : H 8 = 0) :
    ∑ p ∈ Finset.range (8*m), H (l_ty K p) = ∑ g ∈ Finset.range 8, (K g : ℤ) * H g := by
  rw [l_group, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  have hg8 : g < 8 := Finset.mem_range.mp hg
  have e : ∀ r, H (l_ty K (8*r+g)) = if r < K g then H g else 0 := by
    intro r
    have h1 : (8*r+g)/8 = r := by omega
    have h2 : (8*r+g)%8 = g := by omega
    unfold l_ty
    rw [h1, h2]
    split_ifs
    · rfl
    · exact h8
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const]
  have hf : (Finset.range m).filter (fun r => r < K g) = Finset.range (K g) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hK g
    omega
  rw [hf, Finset.card_range, nsmul_eq_mul]
theorem l_pin_eq (n : ℕ) (K : ℕ → ℕ) (s : Bool) (j : ℕ) (hj : j < n) (p : ℕ) (b : Bool)
    (hjp : j = 2*p + cond b 1 0) : l_pin n K (s, ⟨j, hj⟩) = l_pat (l_ty K p) s b := by
  have h1 : j / 2 = p := by cases b <;> simp at hjp <;> omega
  have h2 : decide (j % 2 = 1) = b := by cases b <;> simp at hjp ⊢ <;> omega
  unfold l_pin
  dsimp only
  rw [h1, h2]
theorem l_cons_sq (n : ℕ) (K : ℕ → ℕ) (x : Bool × Fin n → Bool)
    (hx : ∀ v, l_pin n K v = none ∨ l_pin n K v = some (x v)) (p : ℕ) (h : 2*p+1 < n) :
    ∀ s b, l_pat (l_ty K p) s b = none ∨ l_pat (l_ty K p) s b = some (l_sel (l_q n x p) s b) := by
  intro s b
  have hj : 2*p + cond b 1 0 < n := by cases b <;> simp <;> omega
  have e2 : l_sel (l_q n x p) s b = x (s, ⟨2*p + cond b 1 0, hj⟩) := by
    have h0 : 2*p < n := by omega
    cases s <;> cases b <;> simp [l_sel, l_q, l_xs, h0, h]
  rw [← l_pin_eq n K s (2*p + cond b 1 0) hj p b rfl, e2]
  exact hx _
theorem l_xs_hi (n : ℕ) (K : ℕ → ℕ) (hK : ∀ g, K g ≤ n/16) (x : Bool × Fin n → Bool)
    (hx : ∀ v, l_pin n K v = none ∨ l_pin n K v = some (x v)) (s : Bool) (j : ℕ)
    (hj : 16 * (n/16) ≤ j) : l_xs n x s j = false := by
  unfold l_xs
  split_ifs with h
  · have h8 : l_ty K (j/2) = 8 := by
      unfold l_ty
      have := hK ((j/2)%8)
      split_ifs <;> omega
    have hp8 : ∀ s b, l_pat 8 s b = some false := by
      intro s b
      cases s <;> cases b <;> rfl
    have h1 := hx (s, ⟨j, h⟩)
    unfold l_pin at h1
    dsimp only at h1
    rw [h8, hp8] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (by simp)
    · exact (Option.some.inj h1).symm
  · rfl
theorem l_dec (n : ℕ) (K : ℕ → ℕ) (hK : ∀ g, K g ≤ n/16) (x : Bool × Fin n → Bool)
    (hx : ∀ v, l_pin n K v = none ∨ l_pin n K v = some (x v)) (α β : ℤ) :
    α * (l_c1 n x : ℤ) + β * (l_c2 n x : ℤ) =
      ∑ p ∈ Finset.range (8*(n/16)), (α * (l_f1 (l_q n x p) : ℤ) + β * (l_f2 (l_q n x p) : ℤ)) := by
  have e1 : (l_c1 n x : ℤ) = ∑ j ∈ Finset.range n,
      (if l_xs n x false j ≠ l_xs n x true j then (1:ℤ) else 0) := by
    unfold l_c1
    rw [Finset.card_filter, Finset.sum_range]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp [l_xs, l_M]
  have e2 : (l_c2 n x : ℤ) = ∑ j ∈ Finset.range n,
      (if l_xs n x false j ≠ l_xs n x true (l_sn n j) then (1:ℤ) else 0) := by
    unfold l_c2
    rw [Finset.card_filter, Finset.sum_range]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp [l_xs, l_M, l_sig, l_sn_lt i.2]
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub : Finset.range (16*(n/16)) ⊆ Finset.range n := Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · rw [show 16*(n/16) = 2*(8*(n/16)) by ring, l_pair]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : 2*p+1 < n := by rw [Finset.mem_range] at hp; omega
    have hs0 : l_sn n (2*p) = 2*p+1 := by unfold l_sn; split_ifs <;> omega
    have hs1 : l_sn n (2*p+1) = 2*p := by unfold l_sn; split_ifs <;> omega
    rw [hs0, hs1]
    simp only [l_f1, l_f2, l_q]
    ring_nf
  · intro j hj hj'
    rw [Finset.mem_range] at hj hj'
    have h1 := l_xs_hi n K hK x hx false j (by omega)
    have h2 := l_xs_hi n K hK x hx true j (by omega)
    have h3 := l_xs_hi n K hK x hx true (l_sn n j) (by unfold l_sn; split_ifs <;> omega)
    rw [h1, h2, h3]
    simp
theorem l_bnd (n : ℕ) (K : ℕ → ℕ) (hK : ∀ g, K g ≤ n/16) (x : Bool × Fin n → Bool)
    (hx : ∀ v, l_pin n K v = none ∨ l_pin n K v = some (x v)) (α β : ℤ) (V : ℕ → ℤ)
    (hV8 : V 8 = 0)
    (hloc : ∀ t < 9, ∀ a b c e : Bool,
      (∀ s p, l_pat t s p = none ∨ l_pat t s p = some (l_sel (a,b,c,e) s p)) →
      α * (l_f1 (a,b,c,e) : ℤ) + β * (l_f2 (a,b,c,e) : ℤ) ≤ V t) :
    α * (l_c1 n x : ℤ) + β * (l_c2 n x : ℤ) ≤ ∑ g ∈ Finset.range 8, (K g : ℤ) * V g := by
  rw [l_dec n K hK x hx α β, ← l_sumty (n/16) K hK V hV8]
  apply Finset.sum_le_sum
  intro p hp
  have hp' : 2*p+1 < n := by rw [Finset.mem_range] at hp; omega
  exact hloc (l_ty K p) (l_ty_lt K p) _ _ _ _ (l_cons_sq n K x hx p hp')
theorem l_wx_q (n : ℕ) (K : ℕ → ℕ) (w : ℕ → Bool × Bool × Bool × Bool) (p : ℕ)
    (h : 2*p+1 < n) : l_q n (l_wx n K w) p = w (l_ty K p) := by
  have h0 : 2*p < n := by omega
  have a1 : 2*p/2 = p := by omega
  have a2 : (2*p+1)/2 = p := by omega
  have a3 : decide (2*p%2 = 1) = false := by rw [decide_eq_false_iff_not]; omega
  have a4 : decide ((2*p+1)%2 = 1) = true := by rw [decide_eq_true_eq]; omega
  simp only [l_q, l_xs, dite_eq_left h0, dite_eq_left h, l_wx, a1, a2, a3, a4, l_sel,
    Bool.cond_true, Bool.cond_false, Prod.mk.eta]
theorem l_c_lt (n : ℕ) (s : Finset (Fin n)) : s.card < n + 1 :=
  Nat.lt_succ_of_le ((Finset.card_le_univ s).trans_eq (Fintype.card_fin n))
theorem l_mem_of (n : ℕ) (pin : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool)
    (hx : ∀ v, pin v = none ∨ pin v = some (x v)) :
    ((⟨l_c1 n x, l_c_lt n _⟩, ⟨l_c2 n x, l_c_lt n _⟩) : Fin (n+1) × Fin (n+1)) ∈
      l_supp n (l_M n) pin := by
  unfold l_supp
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Finset.card_pos.mpr ⟨x, ?_⟩⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hx, rfl, rfl⟩
theorem l_of_mem (n : ℕ) (pin : Bool × Fin n → Option Bool) (d : Fin (n+1) × Fin (n+1))
    (hd : d ∈ l_supp n (l_M n) pin) : ∃ x : Bool × Fin n → Bool,
      (∀ v, pin v = none ∨ pin v = some (x v)) ∧ l_c1 n x = d.1.val ∧ l_c2 n x = d.2.val := by
  unfold l_supp at hd
  rw [Finset.mem_filter] at hd
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hd.2
  rw [Finset.mem_filter] at hx
  exact ⟨x, hx.2.1, hx.2.2.1, hx.2.2.2⟩
theorem l_dir (n : ℕ) (K K' : ℕ → ℕ) (hK : ∀ g, K g ≤ n/16) (hK' : ∀ g, K' g ≤ n/16)
    (h : l_supp n (l_M n) (l_pin n K) = l_supp n (l_M n) (l_pin n K'))
    (α β : ℤ) (w : ℕ → Bool × Bool × Bool × Bool) (V : ℕ → ℤ) (hV8 : V 8 = 0)
    (hw : ∀ t < 9, (∀ s p, l_pat t s p = none ∨ l_pat t s p = some (l_sel (w t) s p)) ∧
      α * (l_f1 (w t) : ℤ) + β * (l_f2 (w t) : ℤ) = V t)
    (hloc : ∀ t < 9, ∀ a b c e : Bool,
      (∀ s p, l_pat t s p = none ∨ l_pat t s p = some (l_sel (a,b,c,e) s p)) →
      α * (l_f1 (a,b,c,e) : ℤ) + β * (l_f2 (a,b,c,e) : ℤ) ≤ V t) :
    ∑ g ∈ Finset.range 8, (K g : ℤ) * V g ≤ ∑ g ∈ Finset.range 8, (K' g : ℤ) * V g := by
  have hx0 : ∀ v, l_pin n K v = none ∨ l_pin n K v = some (l_wx n K w v) := by
    intro v
    show l_pat (l_ty K (v.2.1 / 2)) v.1 (decide (v.2.1 % 2 = 1)) = none ∨
      l_pat (l_ty K (v.2.1 / 2)) v.1 (decide (v.2.1 % 2 = 1)) =
        some (l_sel (w (l_ty K (v.2.1 / 2))) v.1 (decide (v.2.1 % 2 = 1)))
    exact (hw _ (l_ty_lt K _)).1 _ _
  have hval : α * (l_c1 n (l_wx n K w) : ℤ) + β * (l_c2 n (l_wx n K w) : ℤ) =
      ∑ g ∈ Finset.range 8, (K g : ℤ) * V g := by
    rw [l_dec n K hK _ hx0, ← l_sumty (n/16) K hK V hV8]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : 2*p+1 < n := by rw [Finset.mem_range] at hp; omega
    rw [l_wx_q n K w p hp']
    exact (hw _ (l_ty_lt K p)).2
  have hmem := l_mem_of n (l_pin n K) (l_wx n K w) hx0
  rw [h] at hmem
  obtain ⟨x', hx', e1, e2⟩ := l_of_mem n _ _ hmem
  have hb := l_bnd n K' hK' x' hx' α β V hV8 hloc
  rw [e1, e2] at hb
  rw [← hval]
  exact hb
theorem l_dir2 (n : ℕ) (K K' : ℕ → ℕ) (hK : ∀ g, K g ≤ n/16) (hK' : ∀ g, K' g ≤ n/16)
    (h : l_supp n (l_M n) (l_pin n K) = l_supp n (l_M n) (l_pin n K'))
    (α β : ℤ) (w : ℕ → Bool × Bool × Bool × Bool) (v0 v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (hw : ∀ t < 9, (∀ s p, l_pat t s p = none ∨ l_pat t s p = some (l_sel (w t) s p)) ∧
      α * (l_f1 (w t) : ℤ) + β * (l_f2 (w t) : ℤ) = l_v8 v0 v1 v2 v3 v4 v5 v6 v7 t)
    (hloc : ∀ t < 9, ∀ a b c e : Bool,
      (∀ s p, l_pat t s p = none ∨ l_pat t s p = some (l_sel (a,b,c,e) s p)) →
      α * (l_f1 (a,b,c,e) : ℤ) + β * (l_f2 (a,b,c,e) : ℤ) ≤ l_v8 v0 v1 v2 v3 v4 v5 v6 v7 t) :
    (K 0 : ℤ) * v0 + K 1 * v1 + K 2 * v2 + K 3 * v3 + K 4 * v4 + K 5 * v5 + K 6 * v6 + K 7 * v7 =
      (K' 0 : ℤ) * v0 + K' 1 * v1 + K' 2 * v2 + K' 3 * v3 + K' 4 * v4 + K' 5 * v5 + K' 6 * v6 +
        K' 7 * v7 := by
  have a := l_dir n K K' hK hK' h α β w (l_v8 v0 v1 v2 v3 v4 v5 v6 v7) rfl hw hloc
  have b := l_dir n K' K hK' hK h.symm α β w (l_v8 v0 v1 v2 v3 v4 v5 v6 v7) rfl hw hloc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, l_v8] at a b
  linarith
theorem l_main (n : ℕ) : (n/16+1)^8 ≤
    ((Finset.univ : Finset (Bool × Fin n → Option Bool)).image (l_supp n (l_M n))).card := by
  let Kf : (Fin 8 → Fin (n/16+1)) → ℕ → ℕ := fun k g => if h : g < 8 then (k ⟨g, h⟩).val else 0
  have hKf : ∀ k g, Kf k g ≤ n/16 := by
    intro k g
    simp only [Kf]
    split_ifs
    · exact Nat.lt_succ_iff.mp (k _).isLt
    · exact Nat.zero_le _
  have hinj : Function.Injective (fun k => l_supp n (l_M n) (l_pin n (Kf k))) := by
    intro k k' h
    have h' : l_supp n (l_M n) (l_pin n (Kf k)) = l_supp n (l_M n) (l_pin n (Kf k')) := h
    have d0 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' 1 0 (l_w 0)
      2 0 1 1 2 2 1 2 (by decide +kernel) (by decide +kernel)
    have d1 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' (-1) 0 (l_w 1)
      (-2) 0 0 0 0 0 0 (-1) (by decide +kernel) (by decide +kernel)
    have d2 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' 0 1 (l_w 2)
      0 2 1 2 1 2 2 2 (by decide +kernel) (by decide +kernel)
    have d3 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' 0 (-1) (l_w 3)
      0 (-2) 0 (-1) 0 (-1) 0 0 (by decide +kernel) (by decide +kernel)
    have d4 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' 1 1 (l_w 4)
      2 2 2 2 2 4 2 4 (by decide +kernel) (by decide +kernel)
    have d5 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' (-1) (-1) (l_w 5)
      (-2) (-2) 0 (-2) 0 (-2) 0 (-2) (by decide +kernel) (by decide +kernel)
    have d6 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' 1 (-1) (l_w 6)
      2 (-2) 0 0 2 0 0 2 (by decide +kernel) (by decide +kernel)
    have d7 := l_dir2 n (Kf k) (Kf k') (hKf k) (hKf k') h' (-1) 1 (l_w 7)
      (-2) 2 0 2 0 2 2 0 (by decide +kernel) (by decide +kernel)
    have e : ∀ g < 8, Kf k g = Kf k' g := by
      intro g hg
      interval_cases g <;> omega
    funext g
    apply Fin.ext
    have := e g.val g.isLt
    simpa [Kf, g.isLt] using this
  calc (n/16+1)^8 = (Finset.univ : Finset (Fin 8 → Fin (n/16+1))).card := by simp
    _ = ((Finset.univ : Finset (Fin 8 → Fin (n/16+1))).image
          (fun k => l_supp n (l_M n) (l_pin n (Kf k)))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_image] at hy ⊢
      obtain ⟨k, _, rfl⟩ := hy
      exact ⟨_, Finset.mem_univ _, rfl⟩
theorem h_lower : ∀ n : ℕ,
  let V := Bool × Fin n
  let Match := Bool → Equiv.Perm (Fin n)
  let Index := Fin (n+1) × Fin (n+1)
  let support := fun (M : Match) (pin : V → Option Bool) =>
    (Finset.univ : Finset Index).filter (fun d =>
      0 < ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card = d.2.val)).card)
  let classes := fun M : Match =>
    ((Finset.univ : Finset (V → Option Bool)).image (support M)).card
  ∃ M : Match, (n/16+1)^8 ≤ classes M := by
  intro n V Match Index support classes
  exact ⟨l_M n, l_main n⟩
end PEqualNP.Outside.L_pcx_354
theorem PEqualNP.Outside.L_pcx_354 : ∀ n : ℕ,
  let V := Bool × Fin n
  let Match := Bool → Equiv.Perm (Fin n)
  let Index := Fin (n+1) × Fin (n+1)
  let support := fun (M : Match) (pin : V → Option Bool) =>
    (Finset.univ : Finset Index).filter (fun d =>
      0 < ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, pin v = none ∨ pin v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M false i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M true i))).card = d.2.val)).card)
  let classes := fun M : Match =>
    ((Finset.univ : Finset (V → Option Bool)).image (support M)).card
  (∀ M : Match, classes M ≤ (n+1)^8) ∧
    ∃ M : Match, (n/16+1)^8 ≤ classes M := by
  intro n V Match Index support classes
  exact ⟨PEqualNP.Outside.L_pcx_354.h_upper n, PEqualNP.Outside.L_pcx_354.h_lower n⟩

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover (graphFun)
open SimpleGraph

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2640_641
    (cofAtMostSeven : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (D : Circuit) (m : ℕ) (f g : Fin m ↪ Fin n),
      m ≤ 7 → Odd m →
      (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
      (∀ i j, G.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val) →
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) →
      (7 : ℕ∞) ≤ G.egirth →
      IsMinimalCircuit n D → circuitFun n D = graphFun G A →
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧ ∃ B : Circuit,
        FanInTwo B ∧ B.size + 7 ≤ D.size ∧ B.output < n + B.size ∧
        ∀ x : Fin n → Bool, circuitFun n B x =
          graphFun G A (Function.update (Function.update x (f i) Bool.false) (f j) Bool.false))
    (cofAboveSeven : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (D : Circuit) (m : ℕ) (f g : Fin m ↪ Fin n),
      7 < m → Odd m →
      (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
      (∀ i j, G.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val) →
      (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) →
      (7 : ℕ∞) ≤ G.egirth →
      IsMinimalCircuit n D → circuitFun n D = graphFun G A →
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧ ∃ B : Circuit,
        FanInTwo B ∧ B.size + 7 ≤ D.size ∧ B.output < n + B.size ∧
        ∀ x : Fin n → Bool, circuitFun n B x =
          graphFun G A (Function.update (Function.update x (f i) Bool.false) (f j) Bool.false)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by

  have small_mod (x k : ℕ) (h : x < 2 * k) : x % k = if x < k then x else x - k := by
    split_ifs with h1
    · exact Nat.mod_eq_of_lt h1
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

  have loopGirthBound {V : Type} {G : SimpleGraph V} (q : ℕ → V) (m : ℕ) (hl : q m = q 0 ∧ ∀ t < m, G.Adj (q t) (q (t + 1)))
      (hm : 3 ≤ m) (hinj : ∀ a b, a < m → b < m → q a = q b → a = b) : G.egirth ≤ m := by
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 3 := ⟨m - 3, by omega⟩
    have key : ∀ a b : ℕ, a < r + 3 → b < r + 3 → (r + 3 - a + b) % (r + 3) = 1 →
        G.Adj (q a) (q b) := by
      intro a b ha hb hab
      rw [small_mod _ _ (by omega)] at hab
      split_ifs at hab with h1
      · have : a = r + 2 := by omega
        subst this
        have hb0 : b = 0 := by omega
        subst hb0
        rw [← hl.1]
        exact hl.2 _ (by omega)
      · have hb' : b = a + 1 := by omega
        subst hb'
        exact hl.2 a ha
    let f : cycleGraph (r + 3) →g G := ⟨fun u => q u.val, by
      intro u v huv
      rw [cycleGraph_adj'] at huv
      rcases huv with h | h
      · rw [Fin.val_sub] at h
        exact (key v.val u.val v.isLt u.isLt h).symm
      · rw [Fin.val_sub] at h
        exact key u.val v.val u.isLt v.isLt h⟩
    have hf : Function.Injective f := fun u v h => Fin.ext (hinj _ _ u.isLt v.isLt h)
    have hc := (cycleGraph.isCycle_cycle (n := r)).map hf
    have := hc.egirth_le_length
    simpa using this

  have exists_odd_loop {V : Type} {G : SimpleGraph V} (h : ¬ G.Colorable 2) :
      ∃ k, Odd k ∧ ∃ q : ℕ → V, q k = q 0 ∧ ∀ t < k, G.Adj (q t) (q (t + 1)) := by
    have h' : ¬ G.IsBipartite := h
    rw [isBipartite_iff_forall_walk_even_length] at h'
    push Not at h'
    obtain ⟨v, w, hw⟩ := h'
    refine ⟨w.length, hw, fun i => w.getVert i, ?_, ?_⟩
    · simp
    · intro t ht
      exact w.adj_getVert_succ ht

  have oddCycleCore {V : Type} (G : SimpleGraph V)
      (hdeg : ∀ v, (∃ u, G.Adj v u) → (G.neighborSet v).ncard = 3)
      (hg : (7 : ℕ∞) ≤ G.egirth) (hodd : ∃ k, Odd k ∧ ∃ q : ℕ → V, q k = q 0 ∧ ∀ t < k, G.Adj (q t) (q (t + 1))) :
      ∃ k, 7 ≤ k ∧ Odd k ∧ ∃ c d : ℕ → V,
        (∀ a b, a < k → b < k → c a = c b → a = b) ∧
        (∀ a b, a < k → b < k → d a = d b → a = b) ∧
        (∀ a < k, G.Adj (c a) (d a) ∧ ∀ b < k, d a ≠ c b) ∧
        (∀ a b, a < k → b < k → (G.Adj (c a) (c b) ↔ (a + 1) % k = b ∨ (b + 1) % k = a)) := by
    classical
    have hmin : ∀ m < Nat.find hodd, m % 2 = 1 → ∀ q : ℕ → V, (q m = q 0 ∧ ∀ t < m, G.Adj (q t) (q (t + 1))) → False :=
      fun m hm ho q hq => Nat.find_min hodd hm ⟨Nat.odd_iff.mpr ho, q, hq⟩
    obtain ⟨hko, p, hp⟩ := Nat.find_spec hodd
    generalize Nat.find hodd = k at hmin hko p hp
    have hk2 : k % 2 = 1 := Nat.odd_iff.mp hko
    have hk3 : 3 ≤ k := by
      have h1 : k ≠ 1 := by
        intro h1
        subst h1
        have := hp.2 0 (by omega)
        rw [hp.1] at this
        exact this.ne rfl
      omega
    set c : ℕ → V := fun t => p (t % k) with hc
    have hcper : ∀ t, c (t + k) = c t := by
      intro t
      simp [c]
    have hcmod : ∀ t, c (t % k) = c t := by
      intro t
      simp [c]
    have hcadj : ∀ t, G.Adj (c t) (c (t + 1)) := by
      intro t
      have h1 : t % k < k := Nat.mod_lt _ (by omega)
      have h2 : (t + 1) % k = (t % k + 1) % k := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega)]
      simp only [c]
      rw [h2, small_mod (t % k + 1) k (by omega)]
      split_ifs with h3
      · exact hp.2 _ h1
      · have h4 : t % k + 1 = k := by omega
        have := hp.2 _ h1
        rw [h4, hp.1] at this
        rw [show t % k + 1 - k = 0 by omega]
        exact this
    have hkey : ∀ a b, a < b → b < k → p a = p b → False := by
      intro a b hlt hy hxy
      have l1 : (fun t => p (a + t)) (b - a) = (fun t => p (a + t)) 0 ∧ ∀ t < b - a, G.Adj ((fun t => p (a + t)) t) ((fun t => p (a + t)) (t + 1)) := by
        refine ⟨by simp [show a + (b - a) = b by omega, hxy], fun t ht => ?_⟩
        exact hp.2 _ (by omega)
      have l2 : (fun t => c (b + t)) (k - (b - a)) = (fun t => c (b + t)) 0 ∧ ∀ t < k - (b - a), G.Adj ((fun t => c (b + t)) t) ((fun t => c (b + t)) (t + 1)) := by
        refine ⟨?_, fun t _ => hcadj (b + t)⟩
        simp only [Nat.add_zero]
        rw [show b + (k - (b - a)) = a + k by omega, hcper]
        simp [c, Nat.mod_eq_of_lt (show a < k by omega), Nat.mod_eq_of_lt hy, hxy]
      rcases Nat.even_or_odd (b - a) with he | ho
      · rw [Nat.even_iff] at he
        exact hmin (k - (b - a)) (by omega) (by omega) (fun t => c (b + t)) l2
      · rw [Nat.odd_iff] at ho
        exact hmin (b - a) (by omega) ho (fun t => p (a + t)) l1
    have hcinj2 : ∀ x y, c x = c y → x % k = y % k := by
      intro x y hxy
      have hx := Nat.mod_lt x (show 0 < k by omega)
      have hy := Nat.mod_lt y (show 0 < k by omega)
      rcases lt_trichotomy (x % k) (y % k) with h | h | h
      · exact (hkey _ _ h hy hxy).elim
      · exact h
      · exact (hkey _ _ h hx hxy.symm).elim
    have hcinj : ∀ x y, x < k → y < k → c x = c y → x = y := by
      intro x y hx hy hxy
      have := hcinj2 x y hxy
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    have hloop_chord : ∀ s m, G.Adj (c (s + m)) (c s) →
        (fun t => if t ≤ m then c (s + t) else c s) (m + 1) = (fun t => if t ≤ m then c (s + t) else c s) 0 ∧ ∀ t < m + 1, G.Adj ((fun t => if t ≤ m then c (s + t) else c s) t) ((fun t => if t ≤ m then c (s + t) else c s) (t + 1)) := by
      intro s m hadj
      refine ⟨by simp, fun t ht => ?_⟩
      dsimp only
      by_cases h : t < m
      · rw [if_pos (by omega : t ≤ m), if_pos (by omega : t + 1 ≤ m)]
        exact hcadj (s + t)
      · have : t = m := by omega
        subst this
        rw [if_pos le_rfl, if_neg (by omega)]
        exact hadj
    have hloop_w : ∀ w s m, G.Adj w (c s) → G.Adj (c (s + m)) w →
        (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) (m + 2) = (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) 0 ∧ ∀ t < m + 2, G.Adj ((fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) t) ((fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) (t + 1)) := by
      intro w s m h1 h2
      refine ⟨by simp, fun t ht => ?_⟩
      dsimp only
      by_cases h0 : t = 0
      · subst h0
        rw [if_pos (by omega), if_neg (by omega)]
        simpa using h1
      by_cases hm : t = m + 1
      · subst hm
        rw [if_neg (by omega), if_pos (by omega)]
        simpa using h2
      rw [if_neg (by omega), if_neg (by omega)]
      have := hcadj (s + t - 1)
      rwa [show s + t - 1 + 1 = s + (t + 1) - 1 by omega] at this
    have hseven : ∀ (q : ℕ → V) m, (q m = q 0 ∧ ∀ t < m, G.Adj (q t) (q (t + 1))) → 3 ≤ m → (∀ a b, a < m → b < m → q a = q b → a = b) →
        7 ≤ m := by
      intro q m hl hm hi
      have := le_trans hg (loopGirthBound q m hl hm hi)
      exact_mod_cast this
    have hk7 : 7 ≤ k := by
      refine hseven c k ⟨?_, fun t _ => hcadj t⟩ hk3 hcinj
      simpa using hcper 0
    have hchord : ∀ x y, x < y → y < k → G.Adj (c x) (c y) → y = x + 1 ∨ (x = 0 ∧ y = k - 1) := by
      intro x y hxy hy hadj
      by_contra hne
      have h1 : y ≠ x + 1 := fun h => hne (Or.inl h)
      have h2 : x ≠ 0 ∨ y ≠ k - 1 := by
        by_cases hx : x = 0
        · right
          intro h
          exact hne (Or.inr ⟨hx, h⟩)
        · left
          exact hx
      have l1 := hloop_chord x (y - x) (by rw [show x + (y - x) = y by omega]; exact hadj.symm)
      have l2 := hloop_chord y (k - (y - x))
        (by rw [show y + (k - (y - x)) = x + k by omega, hcper]; exact hadj)
      rcases Nat.even_or_odd (y - x) with he | ho
      · rw [Nat.even_iff] at he
        exact hmin (y - x + 1) (by omega) (by omega) (fun t => if t ≤ y - x then c (x + t) else c x) l1
      · rw [Nat.odd_iff] at ho
        exact hmin (k - (y - x) + 1) (by omega) (by omega) (fun t => if t ≤ k - (y - x) then c (y + t) else c y) l2
    have hadjiff : ∀ a b, a < k → b < k →
        (G.Adj (c a) (c b) ↔ (a + 1) % k = b ∨ (b + 1) % k = a) := by
      intro a b ha hb
      constructor
      · intro h
        rw [small_mod (a + 1) k (by omega), small_mod (b + 1) k (by omega)]
        rcases lt_trichotomy a b with hab | hab | hab
        · rcases hchord a b hab hb h with h' | h'
          · split_ifs <;> omega
          · split_ifs <;> omega
        · subst hab
          exact (h.ne rfl).elim
        · rcases hchord b a hab ha h.symm with h' | h'
          · split_ifs <;> omega
          · split_ifs <;> omega
      · rintro (h | h)
        · rw [← h, hcmod]
          exact hcadj a
        · rw [← h, hcmod]
          exact (hcadj b).symm
    have hnb : ∀ i < k, ∃ w, G.Adj (c i) w ∧ ∀ j < k, w ≠ c j := by
      intro i hi
      have h3 := hdeg (c i) ⟨_, hcadj i⟩
      have hne : c (i + 1) ≠ c (i + k - 1) := by
        intro h
        have := hcinj2 _ _ h
        rw [small_mod (i + 1) k (by omega), small_mod (i + k - 1) k (by omega)] at this
        split_ifs at this <;> omega
      obtain ⟨w, hw, hw1, hw2⟩ : ∃ w ∈ G.neighborSet (c i), w ≠ c (i + 1) ∧ w ≠ c (i + k - 1) := by
        by_contra hcon
        push Not at hcon
        have hsub : G.neighborSet (c i) ⊆ {c (i + 1), c (i + k - 1)} := by
          intro w hw
          by_cases h : w = c (i + 1)
          · simp [h]
          · simp [hcon w hw h]
        have := Set.ncard_le_ncard hsub
        rw [Set.ncard_pair hne] at this
        omega
      refine ⟨w, hw, fun j hj hwj => ?_⟩
      subst hwj
      have hadj : G.Adj (c i) (c j) := hw
      rw [hadjiff i j hi hj] at hadj
      rcases hadj with h | h
      · apply hw1
        rw [← h, hcmod]
      · apply hw2
        rw [← hcmod (i + k - 1)]
        congr 1
        rw [small_mod (j + 1) k (by omega)] at h
        rw [small_mod (i + k - 1) k (by omega)]
        split_ifs at h ⊢ <;> omega
    have : Nonempty V := ⟨p 0⟩
    choose! d hd using hnb
    have hwinj : ∀ w s m, (∀ j < k, w ≠ c j) → s < k → m + 1 ≤ k → ∀ a b, a < m + 2 → b < m + 2 →
        (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) a =
        (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) b → a = b := by
      intro w s m hw hs hm a b ha hb hab
      have hw' : ∀ j, w ≠ c j := by
        intro j h
        rw [← hcmod] at h
        exact hw _ (Nat.mod_lt _ (by omega)) h
      dsimp only at hab
      by_cases ha0 : a = 0
      · by_cases hb0 : b = 0
        · omega
        · rw [if_pos (Or.inl ha0), if_neg (by omega)] at hab
          exact absurd hab (hw' _)
      · by_cases hb0 : b = 0
        · rw [if_neg (by omega), if_pos (Or.inl hb0)] at hab
          exact absurd hab.symm (hw' _)
        · rw [if_neg (by omega), if_neg (by omega)] at hab
          have := hcinj2 _ _ hab
          rw [small_mod (s + a - 1) k (by omega), small_mod (s + b - 1) k (by omega)] at this
          split_ifs at this <;> omega
    have hdinj : ∀ x y, x < k → y < k → d x = d y → x = y := by
      intro x y hx hy hxy
      by_contra hne
      wlog hlt : x < y generalizing x y
      · exact this y x hy hx hxy.symm (Ne.symm hne) (by omega)
      have hwx : G.Adj (d x) (c x) := (hd x hx).1.symm
      have hwy : G.Adj (d x) (c y) := by rw [hxy]; exact (hd y hy).1.symm
      have hwn : ∀ j < k, d x ≠ c j := (hd x hx).2
      have l1 := hloop_w (d x) x (y - x) hwx
        (by rw [show x + (y - x) = y by omega]; exact hwy.symm)
      have l2 := hloop_w (d x) y (k - (y - x)) hwy
        (by rw [show y + (k - (y - x)) = x + k by omega, hcper]; exact hwx.symm)
      have g1 := hseven _ _ l1 (by omega) (hwinj (d x) x (y - x) hwn hx (by omega))
      have g2 := hseven _ _ l2 (by omega) (hwinj (d x) y (k - (y - x)) hwn hy (by omega))
      rcases Nat.even_or_odd (y - x) with he | ho
      · rw [Nat.even_iff] at he
        exact hmin (k - (y - x) + 2) (by omega) (by omega) (fun t => if t = 0 ∨ k - (y - x) + 1 < t then d x else c (y + t - 1)) l2
      · rw [Nat.odd_iff] at ho
        exact hmin (y - x + 2) (by omega) (by omega) (fun t => if t = 0 ∨ y - x + 1 < t then d x else c (x + t - 1)) l1
    exact ⟨k, hk7, hko, c, d, hcinj, hdinj, fun a ha => hd a ha, hadjiff⟩

  have findOddCycleWithSpokes : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), ¬x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → ∃ (x8 : ℕ), (7 : ℕ) ≤ x8 ∧ Odd x8 ∧ ∃ (x9 : Fin x8 ↪ Fin x1) (x10 : Fin x8 ↪ Fin x1), (∀ (x11 : Fin x8), x2.Adj (x9 x11) (x10 x11) ∧ x10 x11 ∉ Set.range ⇑x9) ∧ ∀ (x11 x12 : Fin x8), x2.Adj (x9 x11) (x9 x12) ↔ (↑x11 + (1 : ℕ)) % x8 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x8 = ↑x11 := by
    intro n G A hcol hdeg hg hA
    obtain ⟨k, hk7, hko, c, d, hci, hdi, hcd, hiff⟩ := oddCycleCore G
      (fun v hv => hdeg v (by obtain ⟨u, hu⟩ := hv; exact hA v u hu)) hg
      (exists_odd_loop hcol)
    refine ⟨k, hk7, hko, ⟨fun i => c i.val, fun a b h => Fin.ext (hci _ _ a.isLt b.isLt h)⟩,
      ⟨fun i => d i.val, fun a b h => Fin.ext (hdi _ _ a.isLt b.isLt h)⟩,
      fun i => ⟨(hcd i i.isLt).1, ?_⟩, fun a b => hiff _ _ a.isLt b.isLt⟩
    rintro ⟨j, hj⟩
    exact (hcd i i.isLt).2 j j.isLt hj.symm

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

  have getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
      (w ++ [x]).getD i false =
        if i < w.length then w.getD i false else if i = w.length then x else false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
    split_ifs with h1 h2
    · rfl
    · subst h2; simp
    · have : 1 ≤ i - w.length := by omega
      rw [List.getElem?_eq_none (by simpa using this)]; rfl

  have fold_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih, List.length_append]; simp only [List.length_cons, List.length_nil]; omega

  have fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, getD_snoc, if_pos h]

  have gates_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).gates = C.gates.take m ++
        (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
    unfold eraseGate
    rw [if_pos hm]

  have out_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    unfold eraseGate
    rw [if_pos hm]

  have len_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
      (eraseGate n C m p).gates.length + 1 = C.gates.length := by
    rw [gates_erase n C m p hm]
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
    omega

  let pinF {n : ℕ} (u v : Fin n) (y : Fin n → Bool) : Fin n → Bool :=
    Function.update (Function.update y u Bool.false) v Bool.false

  have pinU {n : ℕ} (u v : Fin n) (z : Fin n → Bool) : pinF u v z u = Bool.false := by
    unfold pinF
    by_cases huv : u = v
    · subst huv
      rw [Function.update_self]
    · rw [Function.update_of_ne huv, Function.update_self]

  have pinV {n : ℕ} (u v : Fin n) (z : Fin n → Bool) : pinF u v z v = Bool.false := by
    unfold pinF
    rw [Function.update_self]

  have pinOther {n : ℕ} (u v : Fin n) (z : Fin n → Bool) {q : Fin n}
      (hu : q ≠ u) (hv : q ≠ v) : pinF u v z q = z q := by
    unfold pinF
    rw [Function.update_of_ne hv, Function.update_of_ne hu]

  have ofg {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
      (List.ofFn f).getD i Bool.false = f ⟨i, h⟩ := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h),
      List.getElem_ofFn]

  have any2 : ∀ (x y : Bool), [x, y].any id = (x || y) := by
    decide

  have all2 : ∀ (x y : Bool), [x, y].all id = (x && y) := by
    decide

  have eval_or2 (i j : ℕ) (f : ℕ → Bool) :
      (⟨GateOp.or, [i, j]⟩ : Gate).op.eval
        ((⟨GateOp.or, [i, j]⟩ : Gate).inputs.map f) = (f i || f j) := by
    show [f i, f j].any id = (f i || f j)
    rw [any2]

  have eval_and2 (i j : ℕ) (f : ℕ → Bool) :
      (⟨GateOp.and, [i, j]⟩ : Gate).op.eval
        ((⟨GateOp.and, [i, j]⟩ : Gate).inputs.map f) = (f i && f j) := by
    show [f i, f j].all id = (f i && f j)
    rw [all2]

  have gd_lt : ∀ (W l : List Bool) (p : ℕ), p < W.length →
      (W ++ l).getD p Bool.false = W.getD p Bool.false := by
    intro W l p hp
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append, if_pos hp]

  have gd_idx (W l : List Bool) (k : ℕ) (hk : k < l.length) :
      (W ++ l).getD (W.length + k) Bool.false = l.getD k Bool.false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append, if_neg (by omega : ¬(W.length + k < W.length)),
      Nat.add_sub_cancel_left]

  have g7 : ∀ (v0 v1 v2 v3 v4 v5 v6 : Bool),
      ([v0, v1, v2, v3, v4, v5, v6] : List Bool).getD 6 Bool.false = v6 := by
    decide

  let addGates (n : ℕ) (B : Circuit) (u v a b c d : Fin n) : List Gate :=
    [⟨GateOp.or, [(v : ℕ), (a : ℕ)]⟩,
     ⟨GateOp.or, [n + B.size, (b : ℕ)]⟩,
     ⟨GateOp.and, [(u : ℕ), n + B.size + 1]⟩,
     ⟨GateOp.or, [(c : ℕ), (d : ℕ)]⟩,
     ⟨GateOp.and, [(v : ℕ), n + B.size + 3]⟩,
     ⟨GateOp.or, [n + B.size + 2, n + B.size + 4]⟩,
     ⟨GateOp.or, [B.output, n + B.size + 5]⟩]

  let extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n) : Circuit :=
    ⟨B.gates ++ addGates n B u v a b c d, n + B.size + 6⟩

  have len_addGates (n : ℕ) (B : Circuit) (u v a b c d : Fin n) :
      (addGates n B u v a b c d).length = 7 := by
    unfold addGates
    simp

  have size_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n) :
      (extC n B u v a b c d).size = B.size + 7 := by
    unfold extC PEqualNP.CircuitLowerBounds.Circuit.size
    rw [List.length_append, len_addGates]

  have fanInTwo_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
      (hB : FanInTwo B) : FanInTwo (extC n B u v a b c d) := by
    intro g hg
    unfold extC addGates at hg
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hB g hg
    · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
    · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
    · exact ⟨Or.inl rfl, Nat.le_refl _⟩
    · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
    · exact ⟨Or.inl rfl, Nat.le_refl _⟩
    · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩
    · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl _⟩

  have foldVals (n : ℕ) (B : Circuit) (u v a b c d : Fin n) (W : List Bool)
      (hW : W.length = n) (hbnd : B.output < n + B.size) :
      (addGates n B u v a b c d).foldl step (B.gates.foldl step W) =
        B.gates.foldl step W ++
          [W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false,
            (W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
              W.getD (b : ℕ) Bool.false,
            W.getD (u : ℕ) Bool.false &&
              ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
                W.getD (b : ℕ) Bool.false),
            W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false,
            W.getD (v : ℕ) Bool.false &&
              (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false),
            (W.getD (u : ℕ) Bool.false &&
              ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
                W.getD (b : ℕ) Bool.false)) ||
              (W.getD (v : ℕ) Bool.false &&
                (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false)),
            (B.gates.foldl step W).getD (B.output : ℕ) Bool.false ||
              ((W.getD (u : ℕ) Bool.false &&
                ((W.getD (v : ℕ) Bool.false || W.getD (a : ℕ) Bool.false) ||
                  W.getD (b : ℕ) Bool.false)) ||
                (W.getD (v : ℕ) Bool.false &&
                  (W.getD (c : ℕ) Bool.false || W.getD (d : ℕ) Bool.false)))] := by
    set P := B.gates.foldl step W with hP
    have rdP : ∀ (l : List Bool) (j : Fin n),
        (P ++ l).getD (j : ℕ) Bool.false = W.getD (j : ℕ) Bool.false := by
      intro l j
      have hj : (j : ℕ) < n := Fin.isLt j
      have hl : (n : ℕ) ≤ P.length := by
        show (n : ℕ) ≤ (B.gates.foldl step W).length
        rw [fold_len, hW]
        omega
      rw [gd_lt P l _ (Nat.lt_of_lt_of_le hj hl)]
      exact fold_stab B.gates W _ (by rw [hW]; exact hj)
    have rd0 : ∀ j : Fin n,
        P.getD (j : ℕ) Bool.false = W.getD (j : ℕ) Bool.false :=
      fun j => fold_stab B.gates W j (by rw [hW]; exact Fin.isLt j)
    have rdg : ∀ (l : List Bool) (k : ℕ), k < l.length →
        (P ++ l).getD (P.length + k) Bool.false = l.getD k Bool.false :=
      fun l k hk => gd_idx P l k hk
    have rdg0 : ∀ (a : Bool) (rest : List Bool),
        (P ++ (a :: rest)).getD P.length Bool.false = (a :: rest).getD 0 Bool.false :=
      fun a rest => gd_idx P (a :: rest) 0 (by simp)
    have rdH : ∀ (l : List Bool) (p : ℕ), p < P.length →
        (P ++ l).getD p Bool.false = P.getD p Bool.false :=
      fun l p hp => gd_lt P l p hp
    unfold addGates
    simp only [List.foldl_cons, List.foldl_nil]
    have hlenP : (n + B.size : ℕ) = P.length := by
      show n + B.gates.length = (B.gates.foldl step W).length
      rw [fold_len, hW]
    have e0 : step P ⟨GateOp.or, [(v : ℕ), (a : ℕ)]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false] := by
      dsimp only [step]
      rw [eval_or2, rd0 v, rd0 a]
    have e1 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false])
        ⟨GateOp.or, [n + B.size, (b : ℕ)]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false] := by
      dsimp only [step]
      rw [eval_or2, hlenP, rdg0, rdP _ b]
      simp
    have e2 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false])
        ⟨GateOp.and, [(u : ℕ), n + B.size + 1]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)] := by
          dsimp only [step]
          rw [eval_and2, rdP _ u, hlenP, rdg _ 1 (by simp)]
          simp
    have e3 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)])
        ⟨GateOp.or, [(c : ℕ), (d : ℕ)]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false] := by
      dsimp only [step]
      rw [eval_or2, rdP _ c, rdP _ d]
      simp
    have e4 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false])
        ⟨GateOp.and, [(v : ℕ), n + B.size + 3]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false,
          W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)] := by
      dsimp only [step]
      rw [eval_and2, rdP _ v, hlenP, rdg _ 3 (by simp)]
      simp
    have e5 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false,
        W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)])
        ⟨GateOp.or, [n + B.size + 2, n + B.size + 4]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false,
          W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
          (W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
            (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false))] := by
      dsimp only [step]
      rw [eval_or2, hlenP, rdg _ 2 (by simp), rdg _ 4 (by simp)]
      simp
    have e6 : step (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
        (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
        W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
        W.getD (c : ℕ) false || W.getD (d : ℕ) false,
        W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
        (W.getD (u : ℕ) false &&
          ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
          (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false))])
        ⟨GateOp.or, [B.output, n + B.size + 5]⟩ =
        P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
          (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
          W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
          W.getD (c : ℕ) false || W.getD (d : ℕ) false,
          W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
          (W.getD (u : ℕ) false &&
            ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
            (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
          P.getD (B.output : ℕ) false ||
            ((W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
              (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))] := by
      dsimp only [step]
      rw [eval_or2, hlenP,
        rdH _ _ (by rw [← hlenP]; exact hbnd), rdg _ 5 (by simp)]
      simp
    rw [e0, e1, e2, e3, e4, e5, e6]

  have eval_extC (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
      (hbnd : B.output < n + B.size) (x : Fin n → Bool) :
      (extC n B u v a b c d).eval (List.ofFn x) =
        ((B.eval (List.ofFn x) || (x u && ((x v || x a) || x b))) ||
          (x v && (x c || x d))) := by
    unfold extC Circuit.eval
    rw [wires_eq, List.foldl_append,
      foldVals n B u v a b c d (List.ofFn x) (by simp) hbnd]
    set P := B.gates.foldl step (List.ofFn x)
    have hlen : P.length = n + B.size := by
      show (B.gates.foldl step (List.ofFn x)).length = n + B.gates.length
      rw [fold_len]
      simp
    rw [← hlen]
    rw [gd_idx P _ 6 (by simp)]
    rw [g7]
    have oget : P.getD (B.output : ℕ) Bool.false = B.eval (List.ofFn x) := by
      unfold Circuit.eval
      rw [wires_eq]
    simp only [ofg x (u : ℕ) (Fin.isLt u),
      ofg x (v : ℕ) (Fin.isLt v),
      ofg x (a : ℕ) (Fin.isLt a),
      ofg x (b : ℕ) (Fin.isLt b),
      ofg x (c : ℕ) (Fin.isLt c),
      ofg x (d : ℕ) (Fin.isLt d)]
    rw [oget]
    conv_lhs => rw [← Bool.or_assoc]
    rfl

  have erase_chain (n : ℕ) (B : Circuit) (u v a b c d : Fin n)
      (hout : B.output < n + B.size) :
      ∃ (f : ℕ → Circuit), f 0 = extC n B u v a b c d ∧
        ∀ t < 7, ∃ (m p : ℕ), m < (f t).size ∧
          (p < n + m ∨ n + (f t).size ≤ p) ∧
          f (t + 1) = eraseGate n (f t) m p ∧
          ((∀ z : Fin n → Bool,
              ((f t).wires (List.ofFn (pinF u v z))).getD (n + m) Bool.false =
                ((f t).wires (List.ofFn (pinF u v z))).getD p Bool.false) ∨
            ((f t).output ≠ n + m ∧
              ∀ g ∈ List.drop (m + 1) (f t).gates, n + m ∉ g.inputs)) := by
    set C := extC n B u v a b c d with hC
    set f : ℕ → Circuit := fun t =>
      Nat.rec C (fun i Ci => eraseGate n Ci (B.size + (6 - i))
        (if i = 0 then B.output else n + Ci.size)) t with hf
    have hf0 : f 0 = C := by rw [hf]; rfl
    have hstep : ∀ t, f (t + 1) =
        eraseGate n (f t) (B.size + (6 - t))
          (if t = 0 then B.output else n + (f t).size) := fun _ => rfl
    have hsz : ∀ t ≤ 7, (f t).size = B.size + 7 - t := by
      intro t ht
      induction t with
      | zero => rw [hf0]; exact size_extC n B u v a b c d
      | succ t ih =>
          have h1 : (f t).size = B.size + 7 - t := ih (by omega)
          have hlt : B.size + (6 - t) < (f t).gates.length := by
            show B.size + (6 - t) < (f t).size
            omega
          have heq := len_erase n (f t) (B.size + (6 - t))
            (if t = 0 then B.output else n + (f t).size) hlt
          have h1' : (f t).gates.length = B.size + 7 - t := h1
          rw [hstep]
          show (eraseGate n (f t) (B.size + (6 - t))
            (if t = 0 then B.output else n + (f t).size)).gates.length = _
          omega
    have houtF : ∀ t, 1 ≤ t → t ≤ 7 → (f t).output = B.output := by
      intro t ht1 ht7
      induction t with
      | zero => exact absurd ht1 (by omega)
      | succ t ih =>
          rcases Nat.eq_zero_or_pos t with rfl | ht0
          ·
            have hcl : C.gates.length = B.size + 7 := size_extC n B u v a b c d
            have hm0 : B.size + (6 - 0) < C.gates.length := by omega
            rw [hstep, if_pos rfl, hf0]
            rw [out_erase n C (B.size + (6 - 0)) B.output hm0]
            show eraseRedirect n (B.size + (6 - 0)) B.output (n + B.size + 6) = B.output
            unfold eraseRedirect
            rw [if_pos (by omega : (n + B.size + 6) = n + (B.size + (6 - 0)))]
          ·
            have hszf := hsz t (by omega)
            have hlt : B.size + (6 - t) < (f t).gates.length := by
              show B.size + (6 - t) < (f t).size
              omega
            rw [hstep, if_neg (Nat.ne_of_gt ht0)]
            rw [out_erase n (f t) (B.size + (6 - t)) _ hlt, ih (by omega) (by omega)]
            unfold eraseRedirect
            have hb : (B.output : ℕ) < n + (B.size + (6 - t)) := by omega
            rw [if_neg (fun h : B.output = n + (B.size + (6 - t)) =>
              lt_irrefl _ (hb.trans_le (Nat.le_of_eq h.symm)))]
            rw [if_neg (fun h : n + (B.size + (6 - t)) < B.output => lt_asymm hb h)]
    refine ⟨f, hf0, ?_⟩
    intro t ht
    rcases t with _|s
    ·
      refine ⟨B.size + 6, B.output, ?_, Or.inl (by omega), ?_, Or.inl ?_⟩
      · rw [hf0, size_extC]; omega
      · rw [hstep, if_pos rfl]
      intro z
      set W := List.ofFn (pinF u v z)
      set P := B.gates.foldl step W
      have hlen : P.length = n + B.size := by
        show (B.gates.foldl step W).length = n + B.gates.length
        rw [fold_len]
        simp [W]
      have w0 : (f 0).wires W =
          P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
            (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
            W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
            W.getD (c : ℕ) false || W.getD (d : ℕ) false,
            W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
            (W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
              (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
            P.getD (B.output : ℕ) false ||
              ((W.getD (u : ℕ) false &&
                ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
                (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))] := by
        rw [hf0, hC]
        unfold extC
        rw [wires_eq, List.foldl_append,
          foldVals n B u v a b c d W
            (by show (List.ofFn (pinF u v z)).length = n; simp) hout]
      have pu : W.getD (u : ℕ) Bool.false = false := by
        rw [ofg _ _ (Fin.isLt u), pinU]
      have pv : W.getD (v : ℕ) Bool.false = false := by
        rw [ofg _ _ (Fin.isLt v), pinV]
      have hlhs : (P ++ [W.getD (v : ℕ) false || W.getD (a : ℕ) false,
            (W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false,
            W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false),
            W.getD (c : ℕ) false || W.getD (d : ℕ) false,
            W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false),
            (W.getD (u : ℕ) false &&
              ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
              (W.getD (v : ℕ) false && (W.getD (c : ℕ) false || W.getD (d : ℕ) false)),
            P.getD (B.output : ℕ) false ||
              ((W.getD (u : ℕ) false &&
                ((W.getD (v : ℕ) false || W.getD (a : ℕ) false) || W.getD (b : ℕ) false)) ||
                (W.getD (v : ℕ) false &&
                  (W.getD (c : ℕ) false || W.getD (d : ℕ) false)))]).getD (n + (B.size + 6)) Bool.false =
          P.getD (B.output : ℕ) Bool.false := by
        rw [← Nat.add_assoc, ← hlen, gd_idx P _ 6 (by simp)]
        rw [g7]
        rw [pu, pv]
        simp
      rw [w0]
      exact hlhs.trans
        (gd_lt P _ (B.output : ℕ) (by rw [hlen]; exact hout)).symm
    ·
      refine ⟨B.size + (6 - (s + 1)), n + (f (s + 1)).size, ?_,
        Or.inr (le_refl _), ?_, Or.inr ⟨?_, ?_⟩⟩
      · have hszf := hsz (s + 1) (by omega)
        show B.size + (6 - (s + 1)) < (f (s + 1)).size
        omega
      · rw [hstep (s + 1), if_neg (Nat.succ_ne_zero s)]
      · rw [houtF (s + 1) (by omega) (by omega)]
        omega
      · intro g hg
        have hlen : (f (s + 1)).gates.length = B.size + 7 - (s + 1) :=
          hsz (s + 1) (by omega)
        have hdrop : List.drop (B.size + (6 - (s + 1)) + 1) (f (s + 1)).gates = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hdrop] at hg
        cases hg

  classical
  intro n G A D notColor degree girth edgeOut hEdges minimal spec
  have G7 : (7 : ℕ∞) ≤ G.egirth :=
    (SimpleGraph.le_egirth (G := G)).2 (fun v w hw => by exact_mod_cast girth v w hw)
  obtain ⟨m, hm, odd, f, g, spokes, edges⟩ :=
    findOddCycleWithSpokes n G A notColor degree G7 edgeOut
  have nonIso {z w : Fin n} (h : G.Adj z w) : z ∉ A := fun hz => edgeOut z w h hz
  have deg (v : Fin n) : (G.neighborSet v).ncard = if v ∈ A then 0 else 3 := by
    by_cases hv : v ∈ A
    · have empty : G.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hu => nonIso hu hv)
      simp [hv, empty]
    · simpa [hv] using degree v hv
  have computes : circuitFun n D = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  obtain ⟨i, j, uv, B, fan, bound, hout, specB⟩ :
      ∃ i j : Fin m, G.Adj (f i) (f j) ∧ ∃ B : Circuit,
        FanInTwo B ∧ B.size + 7 ≤ D.size ∧ B.output < n + B.size ∧
        ∀ x : Fin n → Bool, circuitFun n B x = graphFun G A (pinF (f i) (f j) x) := by
    by_cases shortCycle : m ≤ 7
    · exact cofAtMostSeven n G A D m f g shortCycle odd spokes edges deg G7 minimal computes
    · exact cofAboveSeven n G A D m f g (Nat.lt_of_not_ge shortCycle)
        odd spokes edges deg G7 minimal computes
  let u := f i
  let v := f j
  have uv' : G.Adj u v := uv
  have nbrs (z w : Fin n) (h : G.Adj z w) :
      ∃ a b : Fin n, ∀ k, G.Adj z k ↔ k = w ∨ k = a ∨ k = b := by
    have three : (G.neighborSet z).ncard = 3 := by
      simpa only [nonIso h, ite_false] using deg z
    have two : (G.neighborSet z \ {w}).ncard = 2 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show w ∈ G.neighborSet z from h), three]
    obtain ⟨a, b, _, rest⟩ := Set.ncard_eq_two.mp two
    refine ⟨a, b, ?_⟩
    intro k
    by_cases hk : k = w
    · subst k
      simp [h]
    · have same : k ∈ G.neighborSet z \ {w} ↔ G.Adj z k := by simp [hk]
      rw [← same, rest]
      simp [hk]
  obtain ⟨a, b, nbrU⟩ := nbrs u v uv'
  obtain ⟨c, d, nbrV⟩ := nbrs v u uv'.symm
  have split (x : Fin n → Bool) :
      ((B.eval (List.ofFn x) || (x u && ((x v || x a) || x b))) ||
        (x v && (x c || x d))) = graphFun G A x := by
    have yeq : B.eval (List.ofFn x) = graphFun G A (pinF u v x) := by
      change circuitFun n B x = _
      exact specB x
    have ytrue {q : Fin n} (hq : pinF u v x q = true) : x q = true := by
      have hu : q ≠ u := by
        intro h2
        rw [h2] at hq
        rw [pinU u v x] at hq
        exact absurd hq Bool.false_ne_true
      have hv : q ≠ v := by
        intro h2
        rw [h2] at hq
        rw [pinV u v x] at hq
        exact absurd hq Bool.false_ne_true
      exact (pinOther u v x hu hv).symm.trans hq
    have freeA {q : Fin n} (hq : q ∈ A) : pinF u v x q = x q := by
      refine pinOther u v x ?_ ?_
      · intro h2
        rw [h2] at hq
        exact absurd hq (nonIso uv)
      · intro h2
        rw [h2] at hq
        exact absurd hq (nonIso uv.symm)
    have incidentU {q : Fin n} (h : G.Adj u q) (hq : x q = true) :
        (x v = true ∨ x a = true) ∨ x b = true := by
      rcases (nbrU q).mp h with rfl | rfl | rfl
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
    have incidentV {q : Fin n} (hqU : q ≠ u) (h : G.Adj v q) (hq : x q = true) :
        x c = true ∨ x d = true := by
      rcases (nbrV q).mp h with ht | rfl | rfl
      · exact False.elim (hqU ht)
      · exact Or.inl hq
      · exact Or.inr hq
    rw [yeq]
    apply Bool.eq_iff_iff.mpr
    change (((decide (∃ q ∈ A, pinF u v x q = true) ||
      decide (∃ q r, G.Adj q r ∧ pinF u v x q = true ∧ pinF u v x r = true)) ||
      (x u && ((x v || x a) || x b))) || (x v && (x c || x d))) = true ↔
      (decide (∃ q ∈ A, x q = true) ||
        decide (∃ q r, G.Adj q r ∧ x q = true ∧ x r = true)) = true
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (((hA | edgeY) | starU) | starV)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl ⟨q, hq, ytrue val⟩
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeY
        exact Or.inr ⟨q, r, adj, ytrue hq, ytrue hr⟩
      · obtain ⟨hu, (hv | ha) | hb⟩ := starU
        · exact Or.inr ⟨u, v, uv, hu, hv⟩
        · exact Or.inr ⟨u, a, (nbrU a).mpr (Or.inr (Or.inl rfl)), hu, ha⟩
        · exact Or.inr ⟨u, b, (nbrU b).mpr (Or.inr (Or.inr rfl)), hu, hb⟩
      · obtain ⟨hv, hc | hd⟩ := starV
        · exact Or.inr ⟨v, c, (nbrV c).mpr (Or.inr (Or.inl rfl)), hv, hc⟩
        · exact Or.inr ⟨v, d, (nbrV d).mpr (Or.inr (Or.inr rfl)), hv, hd⟩
    · rintro (hA | edgeX)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl (Or.inl (Or.inl ⟨q, hq, (freeA hq).trans val⟩))
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeX
        by_cases huq : q = u
        · subst q
          exact Or.inl (Or.inr ⟨hq, incidentU adj hr⟩)
        by_cases hur : r = u
        · subst r
          exact Or.inl (Or.inr ⟨hr, incidentU adj.symm hq⟩)
        by_cases hvq : q = v
        · subst q
          exact Or.inr ⟨hq, incidentV hur adj hr⟩
        by_cases hvr : r = v
        · subst r
          exact Or.inr ⟨hr, incidentV huq adj.symm hq⟩
        exact Or.inl (Or.inl (Or.inr ⟨q, r, adj,
          (pinOther u v x huq hvq).trans hq, (pinOther u v x hur hvr).trans hr⟩))
  have hfun : circuitFun n (extC n B u v a b c d) = graphFun G A := by
    funext x
    unfold circuitFun
    rw [eval_extC n B u v a b c d hout]
    exact split x
  obtain ⟨F, hF0, hchain⟩ := erase_chain n B u v a b c d hout
  refine ⟨u, v, uv, F, ?_, ?_, ?_, hchain⟩
  · rw [hF0]
    exact fanInTwo_extC n B u v a b c d fan
  · rw [hF0, size_extC]
    exact bound
  · rw [hF0]
    exact hfun.trans computes.symm

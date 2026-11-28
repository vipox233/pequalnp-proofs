import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1005_aux

def Aff {V : Type} [AddCommGroup V] (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x - y + z ∈ S

def AffF {V : Type} [AddCommGroup V] (φ : V → ZMod 2) : Prop :=
  ∀ x y z, φ (x - y + z) = φ x - φ y + φ z

theorem z3 : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a = b := by decide

theorem aff_filter {V : Type} [AddCommGroup V] [DecidableEq V] {S : Finset V} (hS : Aff S)
    (φ : V → ZMod 2) (hφ : AffF φ) (b : ZMod 2) :
    Aff (S.filter (fun x => φ x = b)) := by
  intro x hx y hy z hz
  simp only [Finset.mem_filter] at hx hy hz ⊢
  refine ⟨hS x hx.1 y hy.1 z hz.1, ?_⟩
  rw [hφ, hx.2, hy.2, hz.2]; ring

def Surj {V C : Type} (co : C → V → ZMod 2) (S : Finset V) (C' : Finset C) : Prop :=
  ∀ t : C → ZMod 2, ∃ x ∈ S, ∀ c ∈ C', co c x = t c

theorem surj_mono {V C : Type} (co : C → V → ZMod 2) {S : Finset V} {C1 C2 : Finset C}
    (h : C1 ⊆ C2) (hS : Surj co S C2) : Surj co S C1 := by
  intro t
  obtain ⟨x, hx, h2⟩ := hS t
  exact ⟨x, hx, fun c hc => h2 c (h hc)⟩

theorem z4 : ∀ a b c d : ZMod 2, a ≠ b → c ≠ d → a - b + c = d := by decide

theorem split {V C : Type} [AddCommGroup V] [DecidableEq V] [DecidableEq C]
    (co : C → V → ZMod 2) (hco : ∀ c, AffF (co c)) {S : Finset V} (hS : Aff S) {C' : Finset C}
    (hC : Surj co S C') (φ : V → ZMod 2) (hφ : AffF φ) :
    (∃ b, ∀ x ∈ S, φ x = b) ∨ (∀ b, Surj co (S.filter (fun x => φ x = b)) C') ∨
    (∃ c0 ∈ C', ∀ b, Surj co (S.filter (fun x => φ x = b)) (C'.erase c0)) := by
  classical
  by_cases hb : ∀ b, Surj co (S.filter (fun x => φ x = b)) C'
  · exact Or.inr (Or.inl hb)
  push_neg at hb
  obtain ⟨b, hb⟩ := hb
  have ht0 : ∃ t : C → ZMod 2, ∀ x, x ∈ S → φ x = b → ∃ c ∈ C', co c x ≠ t c := by
    by_contra hcon
    push_neg at hcon
    apply hb
    intro t
    obtain ⟨x, hx1, hx2, hx3⟩ := hcon t
    exact ⟨x, Finset.mem_filter.2 ⟨hx1, hx2⟩, hx3⟩
  obtain ⟨t, ht⟩ := ht0
  obtain ⟨w, hw, hwt⟩ := hC t
  have hwb : φ w ≠ b := fun h => by
    obtain ⟨c, hc, hne⟩ := ht w hw h; exact hne (hwt c hc)
  have hfib : ∀ x ∈ S, ∀ x' ∈ S, (∀ c ∈ C', co c x = co c x') → φ x = φ x' := by
    intro x hx x' hx' hxx
    have hz : x - x' + w ∈ S := hS x hx x' hx' w hw
    have hzb : φ (x - x' + w) ≠ b := fun h => by
      obtain ⟨c, hc, hne⟩ := ht _ hz h
      apply hne; rw [hco, hxx c hc, ← hwt c hc]; ring
    have := z3 _ _ _ hzb hwb
    rw [hφ] at this
    linear_combination this
  by_cases hc : ∃ c0 ∈ C', ∀ x ∈ S, ∀ x' ∈ S, (∀ c ∈ C', c ≠ c0 → co c x = co c x') →
      co c0 x ≠ co c0 x' → φ x ≠ φ x'
  · right; right
    obtain ⟨c0, hc0, hc⟩ := hc
    refine ⟨c0, hc0, fun b' t' => ?_⟩
    obtain ⟨x, hx, hxt⟩ := hC t'
    by_cases hxb : φ x = b'
    · exact ⟨x, Finset.mem_filter.2 ⟨hx, hxb⟩, fun c h => hxt c (Finset.mem_of_mem_erase h)⟩
    · obtain ⟨x', hx', hx't⟩ := hC (fun c => if c = c0 then co c0 x + 1 else t' c)
      refine ⟨x', Finset.mem_filter.2 ⟨hx', ?_⟩, fun c h => ?_⟩
      · have h1 := hc x' hx' x hx (fun c h1 h2 => by rw [hx't c h1, if_neg h2, hxt c h1])
          (by rw [hx't c0 hc0, if_pos rfl]; simp)
        exact z3 _ _ _ h1 (Ne.symm hxb)
      · rw [hx't c (Finset.mem_of_mem_erase h), if_neg (Finset.ne_of_mem_erase h)]
  · left
    push_neg at hc
    have hflip : ∀ c0 ∈ C', ∀ y ∈ S, ∀ y' ∈ S, (∀ c ∈ C', c ≠ c0 → co c y = co c y') →
        φ y = φ y' := by
      intro c0 hc0 y hy y' hy' hyy
      by_cases he : co c0 y = co c0 y'
      · exact hfib y hy y' hy' (fun c h => by
          by_cases h' : c = c0
          · rw [h']; exact he
          · exact hyy c h h')
      · obtain ⟨x, hx, x', hx', hxx, hne, hφe⟩ := hc c0 hc0
        have hz : y - y' + x' ∈ S := hS y hy y' hy' x' hx'
        have := hfib _ hz x hx (fun c h => by
          rw [hco]
          by_cases h' : c = c0
          · rw [h']; exact z4 _ _ _ _ he (Ne.symm hne)
          · rw [hyy c h h', hxx c h h']; ring)
        rw [hφ, hφe] at this
        linear_combination this
    have hchain : ∀ D : Finset C, D ⊆ C' → ∀ x ∈ S, ∀ x' ∈ S,
        (∀ c ∈ C', c ∉ D → co c x = co c x') → φ x = φ x' := by
      intro D
      induction D using Finset.induction_on with
      | empty => intro _ x hx x' hx' h; exact hfib x hx x' hx' (fun c hc => h c hc (by simp))
      | insert c D0 hcD ih =>
        intro hsub x hx x' hx' hxx
        obtain ⟨x'', hx'', hx''t⟩ := hC (fun c' => if c' = c then co c x' else co c' x)
        have hcC : c ∈ C' := hsub (Finset.mem_insert_self _ _)
        rw [hflip c hcC x hx x'' hx'' (fun c' h1 h2 => by rw [hx''t c' h1, if_neg h2])]
        refine ih ((Finset.subset_insert _ _).trans hsub) x'' hx'' x' hx' (fun c' h1 h2 => ?_)
        rw [hx''t c' h1]
        by_cases h' : c' = c
        · rw [if_pos h', h']
        · rw [if_neg h']; exact hxx c' h1 (by simp [h', h2])
    by_cases hne : S.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      exact ⟨φ x0, fun x hx => hchain C' subset_rfl x hx x0 hx0 (fun c h1 h2 => absurd h1 h2)⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, by simp [hne]⟩

def co {m : ℕ} (c : Fin m × Bool) (x : (Fin m → ZMod 2) × (Fin m → ZMod 2)) : ZMod 2 :=
  if c.2 then x.2 c.1 else x.1 c.1

theorem co_aff {m : ℕ} (c : Fin m × Bool) : AffF (co (m := m) c) := by
  intro x y z
  unfold co
  split_ifs <;> simp

theorem zA : ∀ c y f : ZMod 2, c * y + f = 1 → c * y ≠ f := by decide
theorem zB : ∀ y f : ZMod 2, ¬ (1 * y + f = 1) → f = y := by decide
theorem zC : ∀ y f : ZMod 2, ¬ (0 * y + f = 1) → f = 0 := by decide

theorem allwrong {m : ℕ} (f : Fin m → (Fin m → ZMod 2) × (Fin m → ZMod 2) → ZMod 2)
    (hf : ∀ j, AffF (f j)) : ∀ J : Finset (Fin m),
    ∀ S : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)), Aff S →
      Surj co S (J ×ˢ (Finset.univ : Finset Bool)) →
      ∃ x ∈ S, ∀ j ∈ J, x.1 j * x.2 j ≠ f j x := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro S _ hS
    obtain ⟨x, hx, _⟩ := hS 0
    exact ⟨x, hx, by simp⟩
  | insert j J0 hj ih =>
    intro S hA hS
    have key : ∃ c : ZMod 2, Surj co ((S.filter (fun x => x.1 j = c)).filter
        (fun x => c * x.2 j + f j x = 1)) (J0 ×ˢ (Finset.univ : Finset Bool)) := by
      by_contra hcon
      push_neg at hcon
      have hc1 := hcon 1
      have hc0 := hcon 0
      simp only [Surj, not_forall, not_exists, not_and, Finset.mem_filter] at hc1 hc0
      obtain ⟨t1, ht1⟩ := hc1
      obtain ⟨t0, ht0⟩ := hc0
      have hmem : ∀ c ∈ J0 ×ˢ (Finset.univ : Finset Bool),
          c ∈ (insert j J0) ×ˢ (Finset.univ : Finset Bool) := by
        intro c hc; simp only [Finset.mem_product] at hc ⊢; exact ⟨Finset.mem_insert_of_mem hc.1, hc.2⟩
      have hjm : ∀ bb : Bool, (j, bb) ∈ (insert j J0) ×ˢ (Finset.univ : Finset Bool) := by
        intro bb; simp
      have hjn : ∀ c ∈ J0 ×ˢ (Finset.univ : Finset Bool), c.1 ≠ j := by
        intro c hc h; simp only [Finset.mem_product] at hc; exact hj (h ▸ hc.1)
      let tg := fun (t : Fin m × Bool → ZMod 2) (u v : ZMod 2) (c : Fin m × Bool) =>
        if c.1 = j then (if c.2 then v else u) else t c
      have get : ∀ (t : Fin m × Bool → ZMod 2) (u v : ZMod 2), ∃ x ∈ S, x.1 j = u ∧ x.2 j = v ∧ ∀ c ∈ J0 ×ˢ (Finset.univ : Finset Bool),
          co c x = t c := by
        intro t u v
        obtain ⟨x, hx, hxt⟩ := hS (tg t u v)
        refine ⟨x, hx, ?_, ?_, fun c hc => ?_⟩
        · have := hxt (j, false) (hjm false); simpa [co, tg] using this
        · have := hxt (j, true) (hjm true); simpa [co, tg] using this
        · have := hxt c (hmem c hc); simpa [tg, hjn c hc] using this
      obtain ⟨x1, hx1, h11, h12, h13⟩ := get t1 1 0
      obtain ⟨x2, hx2, h21, h22, h23⟩ := get t1 1 1
      obtain ⟨y2, hy2, h31, h32, h33⟩ := get t0 0 1
      have f1 : f j x1 = 0 := by
        have := zB _ _ (fun h' => by
          obtain ⟨c, hc, hne⟩ := ht1 x1 ⟨⟨hx1, h11⟩, h'⟩; exact hne (h13 c hc))
        rw [this, h12]
      have f2 : f j x2 = 1 := by
        have := zB _ _ (fun h' => by
          obtain ⟨c, hc, hne⟩ := ht1 x2 ⟨⟨hx2, h21⟩, h'⟩; exact hne (h23 c hc))
        rw [this, h22]
      have f3 : f j y2 = 0 := by
        exact zC _ _ (fun h' => by
          obtain ⟨c, hc, hne⟩ := ht0 y2 ⟨⟨hy2, h31⟩, h'⟩; exact hne (h33 c hc))
      have hz : x1 - x2 + y2 ∈ S := hA x1 hx1 x2 hx2 y2 hy2
      have hz1 : (x1 - x2 + y2).1 j = 0 := by simp [h11, h21, h31]
      have := zC _ _ (fun h' => by
          obtain ⟨c, hc, hne⟩ := ht0 (x1 - x2 + y2) ⟨⟨hz, hz1⟩, h'⟩; apply hne
          rw [co_aff, h13 c hc, h23 c hc, h33 c hc]; ring)
      rw [hf, f1, f2, f3] at this
      exact absurd this (by decide)
    obtain ⟨c, hc⟩ := key
    have hA' : Aff ((S.filter (fun x => x.1 j = c)).filter (fun x => c * x.2 j + f j x = 1)) := by
      refine aff_filter (aff_filter hA (fun x => x.1 j) (fun x y z => by simp) c) _ ?_ 1
      intro x y z; show c * (x - y + z).2 j + f j (x - y + z) = _; rw [hf]; simp; ring
    obtain ⟨x, hx, hxJ⟩ := ih _ hA' hc
    simp only [Finset.mem_filter] at hx
    refine ⟨x, hx.1.1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [hx.1.2]; exact zA _ _ _ hx.2
    · exact hxJ i hi

def stp {V : Type} (T : Finset (List Bool)) (φ : List Bool → V → ZMod 2) (x : V) :
    List Bool → List Bool :=
  fun p => if p ∈ T then p ++ [decide (φ p x ≠ 0)] else p

theorem desc_disj (q r : List Bool) (h0 : q ++ [false] <+: r) (h1 : q ++ [true] <+: r) : False := by
  rw [List.prefix_iff_eq_take] at h0 h1
  have : q ++ [false] = q ++ [true] := by
    rw [h0, h1]; simp
  simp at this

theorem hcnt (T : Finset (List Bool)) (q : List Bool) (hq : q ∈ T) :
    (T.filter (fun r => (q ++ [false]) <+: r)).card +
      (T.filter (fun r => (q ++ [true]) <+: r)).card + 1 ≤
      (T.filter (fun r => q <+: r)).card := by
  have hsub : insert q ((T.filter (fun r => (q ++ [false]) <+: r)) ∪
      (T.filter (fun r => (q ++ [true]) <+: r))) ⊆ T.filter (fun r => q <+: r) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hr ⊢
    rcases hr with rfl | ⟨hr, h⟩ | ⟨hr, h⟩
    · exact ⟨hq, List.prefix_refl _⟩
    · exact ⟨hr, (List.prefix_append _ _).trans h⟩
    · exact ⟨hr, (List.prefix_append _ _).trans h⟩
  have hnot : q ∉ (T.filter (fun r => (q ++ [false]) <+: r)) ∪
      (T.filter (fun r => (q ++ [true]) <+: r)) := by
    simp only [Finset.mem_union, Finset.mem_filter]
    rintro (⟨_, h⟩ | ⟨_, h⟩) <;> simpa using h.length_le
  have hdisj : Disjoint (T.filter (fun r => (q ++ [false]) <+: r))
      (T.filter (fun r => (q ++ [true]) <+: r)) := by
    rw [Finset.disjoint_left]
    intro r h0 h1
    exact desc_disj q r (Finset.mem_filter.1 h0).2 (Finset.mem_filter.1 h1).2
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj] at this
  exact this

theorem adv {V C : Type} [AddCommGroup V] [DecidableEq V] [DecidableEq C]
    (co : C → V → ZMod 2) (hco : ∀ c, AffF (co c)) (T : Finset (List Bool))
    (φ : List Bool → V → ZMod 2) (hφ : ∀ p, AffF (φ p)) (M : ℕ) :
    ∀ (n : ℕ) (q : List Bool) (S : Finset V) (C' : Finset C), Aff S → Surj co S C' →
      ((T.filter (fun r => q <+: r)).card + 1) * 2 ^ M < 2 ^ C'.card →
      ∃ (p : List Bool) (S' : Finset V) (C'' : Finset C), S' ⊆ S ∧ C'' ⊆ C' ∧ Aff S' ∧
        Surj co S' C'' ∧ (∀ x ∈ S', (stp T φ x)^[n] q = p) ∧ 2 ^ M < 2 ^ C''.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro q S C' hA hS hN
    refine ⟨q, S, C', subset_rfl, subset_rfl, hA, hS, fun x _ => rfl, ?_⟩
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hN
  | succ n ih =>
    intro q S C' hA hS hN
    by_cases hq : q ∈ T
    · have hc := hcnt T q hq
      set N := (T.filter (fun r => q <+: r)).card
      let Nb := fun b : ZMod 2 => (T.filter (fun r => (q ++ [decide (b ≠ 0)]) <+: r)).card
      have hNb : Nb 0 + Nb 1 + 1 ≤ N := by
        have h0 : decide ((0 : ZMod 2) ≠ 0) = false := by decide
        have h1 : decide ((1 : ZMod 2) ≠ 0) = true := by decide
        simp only [Nb, h0, h1]; exact hc
      have hrun : ∀ b : ZMod 2, ∀ x ∈ S.filter (fun x => φ q x = b),
          (stp T φ x)^[n+1] q = (stp T φ x)^[n] (q ++ [decide (b ≠ 0)]) := by
        intro b x hx
        rw [Finset.mem_filter] at hx
        rw [Function.iterate_succ_apply]
        congr 1
        simp only [stp, hq, if_true]
        rw [hx.2]
      have hmin : ∃ b : ZMod 2, 2 * (Nb b + 1) ≤ N + 1 := by
        by_cases h : Nb 0 ≤ Nb 1
        · exact ⟨0, by omega⟩
        · exact ⟨1, by omega⟩
      rcases split co hco hA hS (φ q) (hφ q) with ⟨b, hb⟩ | hall | ⟨c0, hc0, hsur⟩
      · have hSeq : S.filter (fun x => φ q x = b) = S := Finset.filter_true_of_mem hb
        obtain ⟨p, S', C'', h1, h2, h3, h4, h5, h6⟩ :=
          ih (q ++ [decide (b ≠ 0)]) S C' hA hS (by
            have : Nb b + 1 ≤ N := by
              rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;> omega
            calc (Nb b + 1) * 2 ^ M ≤ N * 2 ^ M := Nat.mul_le_mul_right _ this
              _ ≤ (N + 1) * 2 ^ M := Nat.mul_le_mul_right _ (by omega)
              _ < _ := hN)
        refine ⟨p, S', C'', h1, h2, h3, h4, fun x hx => ?_, h6⟩
        rw [hrun b x (by rw [hSeq]; exact h1 hx)]; exact h5 x hx
      · obtain ⟨b, hb⟩ := hmin
        obtain ⟨p, S', C'', h1, h2, h3, h4, h5, h6⟩ :=
          ih (q ++ [decide (b ≠ 0)]) _ C' (aff_filter hA _ (hφ q) b) (hall b) (by
            have : 2 * ((Nb b + 1) * 2 ^ M) ≤ (N + 1) * 2 ^ M := by
              rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hb
            show (Nb b + 1) * 2 ^ M < _
            omega)
        exact ⟨p, S', C'', h1.trans (Finset.filter_subset _ _), h2, h3, h4,
          fun x hx => by rw [hrun b x (h1 hx)]; exact h5 x hx, h6⟩
      · obtain ⟨b, hb⟩ := hmin
        have hcard : (C'.erase c0).card + 1 = C'.card := Finset.card_erase_add_one hc0
        obtain ⟨p, S', C'', h1, h2, h3, h4, h5, h6⟩ :=
          ih (q ++ [decide (b ≠ 0)]) _ (C'.erase c0) (aff_filter hA _ (hφ q) b) (hsur b) (by
            have : 2 * ((Nb b + 1) * 2 ^ M) ≤ (N + 1) * 2 ^ M := by
              rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hb
            rw [← hcard, pow_succ] at hN
            show (Nb b + 1) * 2 ^ M < _
            omega)
        exact ⟨p, S', C'', h1.trans (Finset.filter_subset _ _), h2.trans (Finset.erase_subset _ _),
          h3, h4, fun x hx => by rw [hrun b x (h1 hx)]; exact h5 x hx, h6⟩
    · obtain ⟨p, S', C'', h1, h2, h3, h4, h5, h6⟩ := ih q S C' hA hS hN
      refine ⟨p, S', C'', h1, h2, h3, h4, fun x hx => ?_, h6⟩
      rw [Function.iterate_succ_apply]
      have : stp T φ x q = q := by simp [stp, hq]
      rw [this]; exact h5 x hx

theorem count_pairs {m : ℕ} (K : Finset (Fin m)) (C'' : Finset (Fin m × Bool))
    (h : C'' ⊆ K ×ˢ (Finset.univ : Finset Bool)) :
    C''.card ≤ K.card + (K.filter (fun j => (j, false) ∈ C'' ∧ (j, true) ∈ C'')).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := C'')
    (fun c => c.2 = true ∧ (c.1, false) ∈ C'')
  have hA : (C''.filter (fun c => ¬ (c.2 = true ∧ (c.1, false) ∈ C''))).card ≤ K.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc
      exact (Finset.mem_product.1 (h hc.1)).1
    · intro c hc c' hc' hcc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
      obtain ⟨c1, c2⟩ := c
      obtain ⟨c1', c2'⟩ := c'
      simp only at hcc
      subst hcc
      cases c2 <;> cases c2' <;> simp_all
  have hB : (C''.filter (fun c => c.2 = true ∧ (c.1, false) ∈ C'')).card ≤
      (K.filter (fun j => (j, false) ∈ C'' ∧ (j, true) ∈ C'')).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      obtain ⟨c1, c2⟩ := c
      simp only at hc ⊢
      obtain ⟨h1, h2, h3⟩ := hc
      subst h2
      exact ⟨(Finset.mem_product.1 (h h1)).1, h3, h1⟩
    · intro c hc c' hc' hcc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
      obtain ⟨c1, c2⟩ := c
      obtain ⟨c1', c2'⟩ := c'
      simp only at hcc hc hc'
      rw [hcc, hc.2.1, hc'.2.1]
  omega

section struct
variable {m g b : ℕ} (group : Fin m → Fin g) (block : Fin g → Fin b)
  (hg : Function.Surjective group) (hb : Function.Surjective block)

def sumAt (x : Fin m → ZMod 2) (v : Fin g) : ZMod 2 :=
  ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => group i = v), x i

def Valid (x : Fin m → ZMod 2) : Prop :=
  ∀ u v, block u = block v → sumAt group x u = sumAt group x v

noncomputable def piv : Fin g → Fin m := Function.surjInv hg
noncomputable def rep : Fin b → Fin g := Function.surjInv hb

theorem piv_spec (u : Fin g) : group (piv group hg u) = u := Function.surjInv_eq hg u
theorem rep_spec (β : Fin b) : block (rep block hb β) = β := Function.surjInv_eq hb β
theorem piv_inj : Function.Injective (piv group hg) := Function.injective_surjInv hg
theorem rep_inj : Function.Injective (rep block hb) := Function.injective_surjInv hb

noncomputable def KK : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter
  (fun i => piv group hg (group i) ≠ i ∨ i = piv group hg (rep block hb (block (group i))))

theorem g_le (group : Fin m → Fin g) (hg : Function.Surjective group) : g ≤ m := by
  have := Fintype.card_le_of_surjective group hg; simpa using this
theorem b_le (block : Fin g → Fin b) (hb : Function.Surjective block) : b ≤ g := by
  have := Fintype.card_le_of_surjective block hb; simpa using this

theorem card_KK : (KK group block hg hb).card = m - (g - b) := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun i => piv group hg (group i) ≠ i ∨ i = piv group hg (rep block hb (block (group i))))
  have h2 : (Finset.univ.filter (fun i => ¬ (piv group hg (group i) ≠ i ∨
      i = piv group hg (rep block hb (block (group i)))))) =
      ((Finset.univ : Finset (Fin g)).filter (fun u => rep block hb (block u) ≠ u)).image
        (piv group hg) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_or, not_not]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨group i, fun h => h2 ?_, h1⟩
      rw [h]; exact h1.symm
    · rintro ⟨u, hu, rfl⟩
      rw [piv_spec group hg]
      exact ⟨rfl, fun h => hu (piv_inj group hg h).symm⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin g)))
    (fun u => rep block hb (block u) = u)
  have h4 : (Finset.univ : Finset (Fin g)).filter (fun u => rep block hb (block u) = u) =
      (Finset.univ : Finset (Fin b)).image (rep block hb) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨block u, h⟩
    · rintro ⟨β, rfl⟩; rw [rep_spec block hb]
  rw [h2, Finset.card_image_of_injective _ (piv_inj group hg)] at h1
  rw [h4, Finset.card_image_of_injective _ (rep_inj block hb)] at h3
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h3
  unfold KK
  have := g_le group hg
  have := b_le block hb
  simp only [ne_eq] at h1 h3 ⊢
  omega

noncomputable def ext (α : Fin m → ZMod 2) : Fin m → ZMod 2 := fun i =>
  if i ∈ KK group block hg hb then α i else
    sumAt group α (rep block hb (block (group i))) +
      ∑ j ∈ ((Finset.univ : Finset (Fin m)).filter (fun j => group j = group i)).erase i, α j

theorem ext_K (α : Fin m → ZMod 2) (i : Fin m) (hi : i ∈ KK group block hg hb) :
    ext group block hg hb α i = α i := by
  unfold ext; rw [if_pos hi]

theorem ext_sum (α : Fin m → ZMod 2) (u : Fin g) :
    sumAt group (ext group block hg hb α) u = sumAt group α (rep block hb (block u)) := by
  classical
  have hpu : piv group hg u ∈ (Finset.univ : Finset (Fin m)).filter (fun j => group j = u) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact piv_spec group hg u
  by_cases hr : rep block hb (block u) = u
  · rw [hr]
    unfold sumAt
    refine Finset.sum_congr rfl (fun i hi => ?_)
    apply ext_K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : piv group hg (group i) = i
    · right; rw [hi, hr, ← hi, h]
    · left; exact h
  · unfold sumAt
    rw [← Finset.add_sum_erase _ _ hpu]
    have hnK : piv group hg u ∉ KK group block hg hb := by
      simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and, piv_spec group hg, not_or, not_not]
      exact fun h => hr (piv_inj group hg h).symm
    have hrest : ∀ i ∈ ((Finset.univ : Finset (Fin m)).filter (fun j => group j = u)).erase
        (piv group hg u), ext group block hg hb α i = α i := by
      intro i hi
      apply ext_K
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and]
      left; rw [hi.2]; exact fun h => hi.1 h.symm
    rw [Finset.sum_congr rfl hrest]
    unfold ext
    rw [if_neg hnK, piv_spec group hg]
    unfold sumAt
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ext_valid (α : Fin m → ZMod 2) : Valid group block (ext group block hg hb α) := by
  intro u v huv
  rw [ext_sum, ext_sum, huv]

end struct

theorem sumAt_aff {m g : ℕ} (group : Fin m → Fin g) (x y z : Fin m → ZMod 2) (u : Fin g) :
    sumAt group (x - y + z) u = sumAt group x u - sumAt group y u + sumAt group z u := by
  unfold sumAt
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rfl

theorem valid_aff {m g b : ℕ} (group : Fin m → Fin g) (block : Fin g → Fin b)
    (x y z : Fin m → ZMod 2) (hx : Valid group block x) (hy : Valid group block y)
    (hz : Valid group block z) : Valid group block (x - y + z) := by
  intro u v huv
  rw [sumAt_aff, sumAt_aff, hx u v huv, hy u v huv, hz u v huv]

theorem lower {m g b : ℕ} (group : Fin m → Fin g) (block : Fin g → Fin b)
    (hg : Function.Surjective group) (hb : Function.Surjective block) (e L : ℕ)
    (T : Finset (List Bool))
    (ask : List Bool → ((Fin m → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2)
    (P : List Bool → Fin m → (((Fin m → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2))
    (d : List Bool → Fin m → ZMod 2) (hT : T.card < L)
    (h : ∀ x : (Fin m → ZMod 2) × (Fin m → ZMod 2), Valid group block x.1 →
      Valid group block x.2 →
      ((Finset.univ : Finset (Fin m)).filter (fun i => x.1 i * x.2 i ≠
        P ((stp T (fun p x => ask p x + bias p) x)^[T.card] []) i x +
        d ((stp T (fun p x => ask p x + bias p) x)^[T.card] []) i)).card ≤ e) :
    2 ^ (m - (g - b) - e) ≤ L := by
  classical
  by_contra hL
  push_neg at hL
  set k := m - (g - b) with hk
  have hek : e ≤ k := by
    by_contra h'
    have : k - e = 0 := by omega
    rw [this] at hL; omega
  let S0 := (Finset.univ : Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2))).filter
    (fun x => Valid group block x.1 ∧ Valid group block x.2)
  have hA0 : Aff S0 := by
    intro x hx y hy z hz
    simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz ⊢
    exact ⟨valid_aff group block _ _ _ hx.1 hy.1 hz.1, valid_aff group block _ _ _ hx.2 hy.2 hz.2⟩
  have hS0 : Surj co S0 (KK group block hg hb ×ˢ (Finset.univ : Finset Bool)) := by
    intro t
    refine ⟨(ext group block hg hb (fun i => t (i, false)),
      ext group block hg hb (fun i => t (i, true))), ?_, fun c hc => ?_⟩
    · simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ext_valid _ _ _ _ _, ext_valid _ _ _ _ _⟩
    · obtain ⟨i, bb⟩ := c
      have hi := (Finset.mem_product.1 hc).1
      cases bb <;> simp [co, ext_K group block hg hb _ i hi]
  have hφ : ∀ p, AffF (fun x => ask p x + bias p) := by
    intro p x y z; simp only [map_add, map_sub]; ring
  have hstart : ((T.filter (fun r => ([] : List Bool) <+: r)).card + 1) * 2 ^ (k + e) <
      2 ^ (KK group block hg hb ×ˢ (Finset.univ : Finset Bool)).card := by
    have hf : T.filter (fun r => ([] : List Bool) <+: r) = T :=
      Finset.filter_true_of_mem (fun r _ => List.nil_prefix)
    rw [hf, Finset.card_product, card_KK, Finset.card_univ, Fintype.card_bool]
    have h1 : T.card + 1 < 2 ^ (k - e) := by omega
    have h2 : 2 ^ (k * 2) = 2 ^ (k - e) * 2 ^ (k + e) := by
      rw [← pow_add]; congr 1; omega
    rw [← hk, h2]
    exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
  obtain ⟨p, S', C'', h1, h2, h3, h4, h5, h6⟩ :=
    adv co co_aff T _ hφ (k + e) T.card [] S0 _ hA0 hS0 hstart
  have h6' : k + e < C''.card := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h6
  have hcnt := count_pairs _ C'' h2
  rw [card_KK, ← hk] at hcnt
  set J := (KK group block hg hb).filter (fun j => (j, false) ∈ C'' ∧ (j, true) ∈ C'')
  have hJ : Surj co S' (J ×ˢ (Finset.univ : Finset Bool)) := by
    refine surj_mono co ?_ h4
    intro c hc
    obtain ⟨j, bb⟩ := c
    have := (Finset.mem_filter.1 (Finset.mem_product.1 hc).1).2
    cases bb
    · exact this.1
    · exact this.2
  have hf : ∀ j, AffF (fun x => P p j x + d p j) := by
    intro j x y z; simp only [map_add, map_sub]; ring
  obtain ⟨x, hx, hxJ⟩ := allwrong (fun j x => P p j x + d p j) hf J S' h3 hJ
  have hx0 := h1 hx
  simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hx0
  have := h x hx0.1 hx0.2
  rw [h5 x hx] at this
  have hsub : J ⊆ (Finset.univ : Finset (Fin m)).filter
      (fun i => x.1 i * x.2 i ≠ P p i x + d p i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxJ j hj
  have := Finset.card_le_card hsub
  omega

section upper
variable {m g b : ℕ} (group : Fin m → Fin g) (block : Fin g → Fin b)
  (hg : Function.Surjective group) (hb : Function.Surjective block)

noncomputable def NPs : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => piv group hg (group i) ≠ i)

theorem card_NPs : (NPs group hg).card = m - g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun i => piv group hg (group i) ≠ i)
  have h2 : (Finset.univ.filter (fun i => ¬ (piv group hg (group i) ≠ i))) =
      (Finset.univ : Finset (Fin g)).image (piv group hg) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_not]
    constructor
    · intro h; exact ⟨group i, h⟩
    · rintro ⟨u, rfl⟩; rw [piv_spec group hg]
  rw [h2, Finset.card_image_of_injective _ (piv_inj group hg)] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  unfold NPs
  omega

noncomputable def np (j : Fin (m - g)) : Fin m :=
  (NPs group hg).orderEmbOfFin (card_NPs group hg) j

theorem np_mem (j : Fin (m - g)) : np group hg j ∈ NPs group hg :=
  Finset.orderEmbOfFin_mem _ _ j

theorem np_inj : Function.Injective (np group hg) :=
  ((NPs group hg).orderEmbOfFin (card_NPs group hg)).injective

theorem np_surj (i : Fin m) (hi : i ∈ NPs group hg) : ∃ j, np group hg j = i := by
  have := Finset.range_orderEmbOfFin (NPs group hg) (card_NPs group hg)
  have hi' : i ∈ Set.range ((NPs group hg).orderEmbOfFin (card_NPs group hg)) := by
    rw [this]; exact hi
  obtain ⟨j, hj⟩ := hi'
  exact ⟨j, hj⟩

noncomputable def idx (i : Fin m) : ℕ :=
  if h : ∃ j, np group hg j = i then (Classical.choose h).val else 0

theorem idx_spec (j : Fin (m - g)) : idx group hg (np group hg j) = j.val := by
  have h : ∃ j', np group hg j' = np group hg j := ⟨j, rfl⟩
  unfold idx
  rw [dif_pos h]
  exact congrArg Fin.val (np_inj group hg (Classical.choose_spec h))

def unk (p : ℕ) (i : Fin m) : Prop := ∃ j : Fin (m - g), np group hg j = i ∧ p ≤ b + j.val

noncomputable def sig (β : Fin b) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => group i = rep block hb β),
    LinearMap.proj i

theorem sig_apply (β : Fin b) (x : Fin m → ZMod 2) :
    sig group block hb β x = sumAt group x (rep block hb β) := by
  unfold sig sumAt
  simp [LinearMap.sum_apply]

noncomputable def askL (j : Fin (m - (g - b))) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if h : j.val < b then sig group block hb ⟨j.val, h⟩ else
    LinearMap.proj (np group hg ⟨j.val - b, by
      have := g_le group hg; have := b_le block hb; have := j.isLt; omega⟩)

def rk (v : Fin g) : ℕ :=
  ((Finset.univ : Finset (Fin g)).filter (fun w => block w = block v ∧ w < v)).card

theorem rk_lt (h4 : ∀ j, ((Finset.univ : Finset (Fin g)).filter (fun v => block v = j)).card ≤ 4)
    (v : Fin g) : rk block v < 4 := by
  have hsub : (Finset.univ : Finset (Fin g)).filter (fun w => block w = block v ∧ w < v) ⊆
      ((Finset.univ : Finset (Fin g)).filter (fun w => block w = block v)).erase v := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hw ⊢
    exact ⟨ne_of_lt hw.2, hw.1⟩
  have h1 := Finset.card_le_card hsub
  have h2 : v ∈ (Finset.univ : Finset (Fin g)).filter (fun w => block w = block v) := by simp
  rw [Finset.card_erase_of_mem h2] at h1
  have := h4 (block v)
  unfold rk; omega

theorem rk_mono (v1 v2 : Fin g) (hb12 : block v1 = block v2) (hlt : v1 < v2) :
    rk block v1 < rk block v2 := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨v1, ?_, ?_⟩
    · simp [hb12, hlt]
    · simp
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw.1.trans hb12, hw.2.trans hlt⟩

theorem rk_inj (v1 v2 : Fin g) (hb12 : block v1 = block v2) (h : rk block v1 = rk block v2) :
    v1 = v2 := by
  rcases lt_trichotomy v1 v2 with hlt | heq | hgt
  · have := rk_mono block v1 v2 hb12 hlt; omega
  · exact heq
  · have := rk_mono block v2 v1 hb12.symm hgt; omega

theorem zr : ∀ r1 r2 : ℕ, r1 < 4 → r2 < 4 → ((r1 % 2 : ℕ) : ZMod 2) = ((r2 % 2 : ℕ) : ZMod 2) →
    ((r1 / 2 : ℕ) : ZMod 2) = ((r2 / 2 : ℕ) : ZMod 2) → r1 = r2 := by
  intro r1 r2 h1 h2
  interval_cases r1 <;> interval_cases r2 <;> decide

theorem sum_decomp (x : Fin m → ZMod 2) (v : Fin g) :
    sumAt group x v = x (piv group hg v) +
      ∑ i ∈ (NPs group hg).filter (fun i => group i = v), x i := by
  classical
  unfold sumAt
  have hmem : piv group hg v ∈ (Finset.univ : Finset (Fin m)).filter (fun i => group i = v) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact piv_spec group hg v
  rw [← Finset.add_sum_erase _ _ hmem]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, NPs]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩; rw [h2]; exact fun h => h1 h.symm
  · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩; rw [← h2]; exact fun h => h1 h.symm

end upper

section upper2
variable {m g b : ℕ} (group : Fin m → Fin g) (block : Fin g → Fin b)
  (hg : Function.Surjective group) (hb : Function.Surjective block)

noncomputable def col (p : ℕ) (i : Fin m) : ZMod 2 × ZMod 2 :=
  if i ∈ NPs group hg then (1, 1)
  else if (block (group i)).val < p then
    ((((NPs group hg).filter (fun i' => group i' = group i ∧
      ∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val)).card : ZMod 2) + 1, 0)
  else (((rk block (group i) % 2 : ℕ) : ZMod 2) +
      (((NPs group hg).filter (fun i' => group i' = group i)).card : ZMod 2),
    ((rk block (group i) / 2 : ℕ) : ZMod 2) +
      (((NPs group hg).filter (fun i' => group i' = group i)).card : ZMod 2))

noncomputable def xr (p : ℕ) (hp : p ≤ m - (g - b)) (a : Fin p → ZMod 2) : Fin m → ZMod 2 := by
  classical
  exact if h : ∃ x, Valid group block x ∧
      ∀ j : Fin p, askL group block hg hb (Fin.castLE hp j) x = a j then Classical.choose h else 0

noncomputable def Pp (p : ℕ) (hp : p ≤ m - (g - b)) (a : Fin p → ZMod 2) (i : Fin m) :
    ((Fin m → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
  (xr group block hg hb p hp a i) • ((LinearMap.proj i).comp (LinearMap.snd _ _ _)) +
  ((col group block hg p i).2 + 1) • ((LinearMap.proj i).comp (LinearMap.fst _ _ _)) +
  ((col group block hg p i).1 + 1) • ((LinearMap.proj i).comp (LinearMap.snd _ _ _))

noncomputable def dd (p : ℕ) (hp : p ≤ m - (g - b)) (a : Fin p → ZMod 2) (i : Fin m) : ZMod 2 :=
  ((col group block hg p i).2 + 1) * xr group block hg hb p hp a i +
    ((col group block hg p i).1 + 1) * ((col group block hg p i).2 + 1)

theorem zP : ∀ x x' y c1 c2 : ZMod 2,
    x * y ≠ x' * y + (c2 + 1) * x + (c1 + 1) * y + ((c2 + 1) * x' + (c1 + 1) * (c2 + 1)) ↔
    (x - x' = c1 ∧ y = c2) := by decide

theorem sumAt_sub (x y : Fin m → ZMod 2) (v : Fin g) :
    sumAt group (x - y) v = sumAt group x v - sumAt group y v := by
  unfold sumAt; rw [← Finset.sum_sub_distrib]; rfl

theorem zF : ∀ s t : ZMod 2, t = s + 1 → t + s = 0 → False := by decide
theorem zG : ∀ a n : ZMod 2, a + n + n = a := by decide

theorem idx_eq (i1 i2 : Fin m) (h1 : i1 ∈ NPs group hg) (h2 : i2 ∈ NPs group hg)
    (h : idx group hg i1 = idx group hg i2) : i1 = i2 := by
  obtain ⟨j1, rfl⟩ := np_surj group hg i1 h1
  obtain ⟨j2, rfl⟩ := np_surj group hg i2 h2
  rw [idx_spec, idx_spec] at h
  rw [Fin.ext h]

theorem upper_main
    (h4 : ∀ j, ((Finset.univ : Finset (Fin g)).filter (fun v => block v = j)).card ≤ 4) (p : ℕ) (hp : p ≤ m - (g - b)) (x : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (hx1 : Valid group block x.1) (hx2 : Valid group block x.2) :
    ((Finset.univ : Finset (Fin m)).filter (fun i => x.1 i * x.2 i ≠
      Pp group block hg hb p hp (fun j => askL group block hg hb (Fin.castLE hp j) x.1) i x +
      dd group block hg hb p hp (fun j => askL group block hg hb (Fin.castLE hp j) x.1) i)).card
      ≤ m - (g - b) - p := by
  classical
  have hgm := g_le group hg
  have hbg := b_le block hb
  set a := fun j => askL group block hg hb (Fin.castLE hp j) x.1 with ha
  have hex : ∃ x0, Valid group block x0 ∧
      ∀ j : Fin p, askL group block hg hb (Fin.castLE hp j) x0 = a j := ⟨x.1, hx1, fun j => rfl⟩
  have hxr : xr group block hg hb p hp a = Classical.choose hex := by
    unfold xr; rw [dif_pos hex]
  set x' := xr group block hg hb p hp a with hx'
  have hv' : Valid group block x' := by rw [hxr]; exact (Classical.choose_spec hex).1
  have ha' : ∀ j : Fin p, askL group block hg hb (Fin.castLE hp j) x' =
      askL group block hg hb (Fin.castLE hp j) x.1 := by
    intro j; rw [hxr]; exact (Classical.choose_spec hex).2 j
  set u := x.1 - x' with hu
  set y := x.2 with hy
  set E := (Finset.univ : Finset (Fin m)).filter
    (fun i => u i = (col group block hg p i).1 ∧ y i = (col group block hg p i).2) with hEdef
  have hfil : (Finset.univ : Finset (Fin m)).filter (fun i => x.1 i * x.2 i ≠
      Pp group block hg hb p hp a i x + dd group block hg hb p hp a i) = E := by
    apply Finset.filter_congr
    intro i _
    simp only [Pp, dd, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul]
    rw [hu]
    simp only [Pi.sub_apply]
    rw [← zP (x.1 i) (x' i) (x.2 i) (col group block hg p i).1 (col group block hg p i).2]
  rw [hfil]

  have F1 : ∀ j : Fin (m - g), b + j.val < p → u (np group hg j) = 0 := by
    intro j hj
    have := ha' ⟨b + j.val, hj⟩
    have hnb : ¬ (Fin.castLE hp ⟨b + j.val, hj⟩).val < b := by simp
    unfold askL at this
    rw [dif_neg hnb] at this
    have hjj : (⟨(Fin.castLE hp ⟨b + j.val, hj⟩).val - b, by
        have := j.isLt; simp⟩ : Fin (m - g)) = j := by
      ext; simp
    simp only [LinearMap.proj_apply] at this
    rw [hu, Pi.sub_apply]
    have e2 : np group hg ⟨(Fin.castLE hp ⟨b + j.val, hj⟩).val - b, by
        have := j.isLt; simp⟩ = np group hg j := by rw [hjj]
    rw [e2] at this
    rw [this]; ring

  have F2 : ∀ v : Fin g, (block v).val < p → sumAt group u v = 0 := by
    intro v hv
    have := ha' ⟨(block v).val, hv⟩
    have hlt : (Fin.castLE hp ⟨(block v).val, hv⟩).val < b := by simp
    unfold askL at this
    rw [dif_pos hlt] at this
    have hβ : (⟨(Fin.castLE hp ⟨(block v).val, hv⟩).val, hlt⟩ : Fin b) = block v := by
      ext; simp
    rw [hβ, sig_apply, sig_apply] at this
    have e1 := hx1 v (rep block hb (block v)) (rep_spec block hb (block v)).symm
    have e2 := hv' v (rep block hb (block v)) (rep_spec block hb (block v)).symm
    rw [hu, sumAt_sub, e1, e2, this]; ring
  have F3 : Valid group block u := by
    intro v1 v2 h12
    rw [hu, sumAt_sub, sumAt_sub, hx1 v1 v2 h12, hv' v1 v2 h12]
  have unk_iff : ∀ i ∈ NPs group hg, ((∃ j : Fin (m - g), np group hg j = i ∧ p ≤ b + j.val) ↔
      p ≤ b + idx group hg i) := by
    intro i hi
    obtain ⟨j, rfl⟩ := np_surj group hg i hi
    rw [idx_spec]
    constructor
    · rintro ⟨j', hj', hle⟩; rw [← np_inj group hg hj']; exact hle
    · intro h; exact ⟨j, rfl, h⟩
  have idx_lt : ∀ i ∈ NPs group hg, idx group hg i < m - g := by
    intro i hi
    obtain ⟨j, rfl⟩ := np_surj group hg i hi
    rw [idx_spec]; exact j.isLt
  have colNP : ∀ i ∈ NPs group hg, col group block hg p i = (1, 1) := by
    intro i hi; unfold col; rw [if_pos hi]
  have pivof : ∀ i, i ∉ NPs group hg → piv group hg (group i) = i := by
    intro i hi
    simp only [NPs, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  have memE : ∀ i, i ∈ E ↔ (u i = (col group block hg p i).1 ∧ y i = (col group block hg p i).2) := by
    intro i; simp [hEdef]

  let f : Fin m → ℕ := fun i =>
    if i ∈ NPs group hg then b + idx group hg i else
      if h : ∃ i', i' ∈ NPs group hg ∧ group i' = group i ∧
          (∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val) ∧ i' ∉ E then
        b + idx group hg (Classical.choose h) else (block (group i)).val

  have lemA : ∀ i ∈ E, i ∉ NPs group hg → (¬ ∃ i', i' ∈ NPs group hg ∧ group i' = group i ∧
      (∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val) ∧ i' ∉ E) →
      p ≤ (block (group i)).val := by
    intro i hiE hiN hno
    by_contra hlt
    push_neg at hlt
    have hcol : col group block hg p i = ((((NPs group hg).filter (fun i' => group i' = group i ∧
        ∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val)).card : ZMod 2) + 1, 0) := by
      unfold col; rw [if_neg hiN, if_pos hlt]
    have hui := ((memE i).1 hiE).1
    rw [hcol] at hui
    have hs := F2 (group i) hlt
    rw [sum_decomp group hg, pivof i hiN] at hs
    have hsum : ∑ i' ∈ (NPs group hg).filter (fun i' => group i' = group i), u i' =
        ∑ i' ∈ (NPs group hg).filter (fun i' => group i' = group i),
          (if (∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val) then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro i' hi'
      simp only [Finset.mem_filter] at hi'
      split_ifs with hk
      · have : i' ∈ E := by
          by_contra hne; exact hno ⟨i', hi'.1, hi'.2, hk, hne⟩
        have := ((memE i').1 this).1
        rw [colNP i' hi'.1] at this; exact this
      · obtain ⟨j, rfl⟩ := np_surj group hg i' hi'.1
        apply F1 j
        by_contra hh; push_neg at hh; exact hk ⟨j, rfl, hh⟩
    rw [hsum, Finset.sum_boole, Finset.filter_filter] at hs
    exact zF _ _ hui hs

  have lemB : ∀ i ∈ E, i ∉ NPs group hg → (¬ ∃ i', i' ∈ NPs group hg ∧ group i' = group i ∧
      (∃ j : Fin (m - g), np group hg j = i' ∧ p ≤ b + j.val) ∧ i' ∉ E) →
      sumAt group u (group i) = ((rk block (group i) % 2 : ℕ) : ZMod 2) ∧
      sumAt group y (group i) = ((rk block (group i) / 2 : ℕ) : ZMod 2) := by
    intro i hiE hiN hno
    have hA := lemA i hiE hiN hno
    have hlt : (block (group i)).val < b := (block (group i)).isLt
    have hcol : col group block hg p i = (((rk block (group i) % 2 : ℕ) : ZMod 2) +
        (((NPs group hg).filter (fun i' => group i' = group i)).card : ZMod 2),
        ((rk block (group i) / 2 : ℕ) : ZMod 2) +
        (((NPs group hg).filter (fun i' => group i' = group i)).card : ZMod 2)) := by
      unfold col; rw [if_neg hiN, if_neg (by omega)]
    have hall : ∀ i' ∈ (NPs group hg).filter (fun i' => group i' = group i), i' ∈ E := by
      intro i' hi'
      simp only [Finset.mem_filter] at hi'
      by_contra hne
      refine hno ⟨i', hi'.1, hi'.2, ?_, hne⟩
      obtain ⟨j, rfl⟩ := np_surj group hg i' hi'.1
      exact ⟨j, rfl, by omega⟩
    have h1 : ∀ i' ∈ (NPs group hg).filter (fun i' => group i' = group i), u i' = 1 := by
      intro i' hi'
      have := ((memE i').1 (hall i' hi')).1
      rw [colNP i' (Finset.mem_filter.1 hi').1] at this; exact this
    have h2 : ∀ i' ∈ (NPs group hg).filter (fun i' => group i' = group i), y i' = 1 := by
      intro i' hi'
      have := ((memE i').1 (hall i' hi')).2
      rw [colNP i' (Finset.mem_filter.1 hi').1] at this; exact this
    have hE := (memE i).1 hiE
    rw [hcol] at hE
    rw [sum_decomp group hg, sum_decomp group hg, pivof i hiN, Finset.sum_congr rfl h1,
      Finset.sum_congr rfl h2, hE.1, hE.2]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact ⟨zG _ _, zG _ _⟩
  have hmaps : ∀ i ∈ E, f i ∈ Finset.Ico p (m - (g - b)) := by
    intro i hiE
    rw [Finset.mem_Ico]
    by_cases hiN : i ∈ NPs group hg
    · simp only [f, if_pos hiN]
      have hl := idx_lt i hiN
      refine ⟨?_, by omega⟩
      rw [← unk_iff i hiN]
      obtain ⟨j, rfl⟩ := np_surj group hg i hiN
      refine ⟨j, rfl, ?_⟩
      by_contra hh; push_neg at hh
      have h0 := F1 j hh
      have h1 := ((memE _).1 hiE).1
      rw [colNP _ hiN, h0] at h1
      exact absurd h1 (by decide)
    · simp only [f, if_neg hiN]
      split_ifs with hh
      · have hs := Classical.choose_spec hh
        have hl := idx_lt _ hs.1
        refine ⟨?_, by omega⟩
        exact (unk_iff _ hs.1).1 hs.2.2.1
      · exact ⟨lemA i hiE hiN hh, by have := (block (group i)).isLt; omega⟩
  have hinj : Set.InjOn f E := by
    intro i1 hi1 i2 hi2 h12
    have hi1E : i1 ∈ E := hi1
    have hi2E : i2 ∈ E := hi2
    by_cases hN1 : i1 ∈ NPs group hg <;> by_cases hN2 : i2 ∈ NPs group hg
    · simp only [f, if_pos hN1, if_pos hN2] at h12
      exact idx_eq group hg i1 i2 hN1 hN2 (by omega)
    · simp only [f, if_pos hN1, if_neg hN2] at h12
      split_ifs at h12 with hh
      · have hs := Classical.choose_spec hh
        have := idx_eq group hg _ _ hN1 hs.1 (by omega)
        exact absurd (this ▸ hi1E) hs.2.2.2
      · have := (block (group i2)).isLt; omega
    · simp only [f, if_neg hN1, if_pos hN2] at h12
      split_ifs at h12 with hh
      · have hs := Classical.choose_spec hh
        have := idx_eq group hg _ _ hN2 hs.1 (by omega)
        exact absurd (this ▸ hi2E) hs.2.2.2
      · have := (block (group i1)).isLt; omega
    · simp only [f, if_neg hN1, if_neg hN2] at h12
      split_ifs at h12 with hh1 hh2 hh2
      · have hs1 := Classical.choose_spec hh1
        have hs2 := Classical.choose_spec hh2
        have := idx_eq group hg _ _ hs1.1 hs2.1 (by omega)
        rw [← pivof i1 hN1, ← pivof i2 hN2, ← hs1.2.1, ← hs2.2.1, this]
      · have hs1 := Classical.choose_spec hh1
        have := (block (group i2)).isLt; omega
      · have hs2 := Classical.choose_spec hh2
        have := (block (group i1)).isLt; omega
      · have hbl : block (group i1) = block (group i2) := Fin.ext h12
        obtain ⟨b1, c1⟩ := lemB i1 hi1E hN1 hh1
        obtain ⟨b2, c2⟩ := lemB i2 hi2E hN2 hh2
        have e1 := F3 _ _ hbl
        have e2 := hx2 _ _ hbl
        rw [b1, b2] at e1
        rw [c1, c2] at e2
        have hr := zr _ _ (rk_lt block h4 _) (rk_lt block h4 _) e1 e2
        have hv := rk_inj block _ _ hbl hr
        rw [← pivof i1 hN1, ← pivof i2 hN2, hv]
  have := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Nat.card_Ico] at this
  exact this

end upper2

theorem foldl_iter {α β : Type} (gg : α → α) : ∀ (l : List β) (q : α),
    l.foldl (fun p _ => gg p) q = gg^[l.length] q := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons x l ih => intro q; simp only [List.foldl_cons, List.length_cons]; rw [ih]; rfl

theorem run_eq {V : Type} (T : Finset (List Bool)) (φ : List Bool → V → ZMod 2) (x : V) :
    (List.range T.card).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (φ p x ≠ 0)] else p) [] =
    (stp T φ x)^[T.card] [] := by
  have := foldl_iter (stp T φ x) (List.range T.card) []
  rw [List.length_range] at this
  exact this

def Tset (s : ℕ) : Finset (List Bool) :=
  (Finset.range s).biUnion (fun k => (Finset.univ : Finset (Fin k → Bool)).image List.ofFn)

theorem memT (s : ℕ) (p : List Bool) : p ∈ Tset s ↔ p.length < s := by
  simp only [Tset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨k, hk, f, rfl⟩; simpa using hk
  · intro h; exact ⟨p.length, h, p.get, List.ofFn_get p⟩

theorem geom : ∀ N : ℕ, (∑ k ∈ Finset.range N, 2 ^ k) + 1 = 2 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem cardT_lt (s : ℕ) : (Tset s).card < 2 ^ s := by
  have h1 : (Tset s).card ≤ ∑ k ∈ Finset.range s, 2 ^ k := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun k _ => ?_))
    refine Finset.card_image_le.trans ?_
    simp
  have h2 := geom s
  omega

theorem cardT_ge (s : ℕ) : s ≤ (Tset s).card := by
  have hsub : (Finset.range s).image (fun k => List.replicate k false) ⊆ Tset s := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [memT]; simpa using hk
  have hinj : Function.Injective (fun k => List.replicate k false) := by
    intro a b h; simpa using congrArg List.length h
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  exact this

def st {V : Type} (ψ : ℕ → V → ZMod 2) (x : V) (k : ℕ) : List Bool :=
  (List.range k).map (fun j => decide (ψ j x ≠ 0))

theorem iter_st {V : Type} (s : ℕ) (ψ : ℕ → V → ZMod 2) (x : V) : ∀ k ≤ s,
    (stp (Tset s) (fun p => ψ p.length) x)^[k] [] = st ψ x k := by
  intro k
  induction k with
  | zero => intro _; simp [st]
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hl : (st ψ x k).length = k := by simp [st]
    have hm : st ψ x k ∈ Tset s := by rw [memT, hl]; omega
    simp only [stp, hm, if_true, hl]
    simp [st, List.range_succ]

theorem run_st {V : Type} (s : ℕ) (ψ : ℕ → V → ZMod 2) (x : V) :
    (stp (Tset s) (fun p => ψ p.length) x)^[(Tset s).card] [] = st ψ x s := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (cardT_ge s)
  rw [hr, add_comm, Function.iterate_add_apply, iter_st s ψ x _ le_rfl]
  apply Function.iterate_fixed
  have hl : (st ψ x s).length = s := by simp [st]
  have hm : st ψ x s ∉ Tset s := by rw [memT, hl]; omega
  simp [stp, hm]

def rd (p : List Bool) (k : ℕ) : ZMod 2 := if p.getD k false = true then 1 else 0

theorem zdec : ∀ z : ZMod 2, (if decide (z ≠ 0) = true then (1 : ZMod 2) else 0) = z := by decide

theorem rd_st {V : Type} (ψ : ℕ → V → ZMod 2) (x : V) (M k : ℕ) (hk : k < M) :
    rd (st ψ x M) k = ψ k x := by
  unfold rd st
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  exact zdec _

end PEqualNP.Outside.L_lib_1005_aux

theorem PEqualNP.Outside.L_lib_1005 : (∀ (m g b : Nat),
  let F := ZMod 2
  let I := Fin m
  let G := Fin g
  let W := I → F
  let X := W × W
  let D := X →ₗ[F] F
  let H := List Bool
  ∀ (group : I → G) (block : G → Fin b), Function.Surjective group → Function.Surjective block →
    (∀ j, ((Finset.univ : Finset G).filter (fun v => block v = j)).card ≤ 4) →
    let sumAt := fun (x : W) (v : G) => ∑ i ∈ (Finset.univ : Finset I).filter (fun i => group i = v), x i
    let valid := fun (x : W) => ∀ u v, block u = block v → sumAt x u = sumAt x v
    let k := m-(g-b)
    let err := fun (x : X) (P : I → D) (d : W) =>
      ((Finset.univ : Finset I).filter (fun i => x.1 i * x.2 i ≠ P i x + d i)).card
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    (∀ e L : Nat,
      (∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → I → D) (d : H → W),
        T.card < L ∧ ∀ x : X, valid x.1 → valid x.2 →
          err x (P (run T ask bias x)) (d (run T ask bias x)) ≤ e) ↔ 2^(k-e) ≤ L) ∧
    ∃ ask : Fin k → W →ₗ[F] F, ∀ (p : Nat) (hp : p ≤ k),
      ∃ (P : (Fin p → F) → I → D) (d : (Fin p → F) → W),
        ∀ x : X, valid x.1 → valid x.2 →
          let answers := fun j : Fin p => ask (Fin.castLE hp j) x.1
          err x (P answers) (d answers) ≤ k-p) := by
  intro m g b F I G W X D H group block hg hb h4 sumAt valid k err run
  refine ⟨?_, ⟨PEqualNP.Outside.L_lib_1005_aux.askL group block hg hb, fun p hp =>
    ⟨PEqualNP.Outside.L_lib_1005_aux.Pp group block hg hb p hp,
     PEqualNP.Outside.L_lib_1005_aux.dd group block hg hb p hp, fun x hx1 hx2 =>
      PEqualNP.Outside.L_lib_1005_aux.upper_main group block hg hb h4 p hp x hx1 hx2⟩⟩⟩
  intro e L
  constructor
  · rintro ⟨T, ask, bias, P, d, hT, hx⟩
    refine PEqualNP.Outside.L_lib_1005_aux.lower group block hg hb e L T ask bias P d hT ?_
    intro x hx1 hx2
    have := hx x hx1 hx2
    rw [show run T ask bias x = (PEqualNP.Outside.L_lib_1005_aux.stp T
        (fun p y => ask p y + bias p) x)^[T.card] [] from
        PEqualNP.Outside.L_lib_1005_aux.run_eq T (fun p y => ask p y + bias p) x] at this
    exact this
  · intro hL
    have hgm := PEqualNP.Outside.L_lib_1005_aux.g_le group hg
    have hbg := PEqualNP.Outside.L_lib_1005_aux.b_le block hb
    set p0 := k - e with hp0d
    have hp0 : p0 ≤ m - (g - b) := by omega
    let ψ : ℕ → X → ZMod 2 := fun j x =>
      if hj : j < m - (g - b) then PEqualNP.Outside.L_lib_1005_aux.askL group block hg hb ⟨j, hj⟩ x.1
      else 0
    let askT : H → D := fun h =>
      if hj : h.length < m - (g - b) then
        (PEqualNP.Outside.L_lib_1005_aux.askL group block hg hb ⟨h.length, hj⟩).comp
          (LinearMap.fst _ _ _)
      else 0
    refine ⟨PEqualNP.Outside.L_lib_1005_aux.Tset p0, askT, fun _ => 0,
      fun h => PEqualNP.Outside.L_lib_1005_aux.Pp group block hg hb p0 hp0
        (fun j => PEqualNP.Outside.L_lib_1005_aux.rd h j.val),
      fun h => PEqualNP.Outside.L_lib_1005_aux.dd group block hg hb p0 hp0
        (fun j => PEqualNP.Outside.L_lib_1005_aux.rd h j.val), ?_, ?_⟩
    · exact lt_of_lt_of_le (PEqualNP.Outside.L_lib_1005_aux.cardT_lt p0) hL
    · intro x hx1 hx2
      have hrun : run (PEqualNP.Outside.L_lib_1005_aux.Tset p0) askT (fun _ => 0) x =
          PEqualNP.Outside.L_lib_1005_aux.st ψ x p0 := by
        refine (PEqualNP.Outside.L_lib_1005_aux.run_eq _
          (fun p y => askT p y + (fun _ => (0 : ZMod 2)) p) x).trans ?_
        have hfun : PEqualNP.Outside.L_lib_1005_aux.stp (PEqualNP.Outside.L_lib_1005_aux.Tset p0)
            (fun p y => askT p y + (fun _ => (0 : ZMod 2)) p) x =
            PEqualNP.Outside.L_lib_1005_aux.stp (PEqualNP.Outside.L_lib_1005_aux.Tset p0)
            (fun p => ψ p.length) x := by
          funext q
          have hq : askT q x + 0 = ψ q.length x := by
            simp only [askT, ψ, add_zero]
            split_ifs <;> rfl
          simp only [PEqualNP.Outside.L_lib_1005_aux.stp, hq]
        rw [hfun]
        exact PEqualNP.Outside.L_lib_1005_aux.run_st p0 ψ x
      rw [hrun]
      have hans : (fun j : Fin p0 => PEqualNP.Outside.L_lib_1005_aux.rd
          (PEqualNP.Outside.L_lib_1005_aux.st ψ x p0) j.val) =
          (fun j : Fin p0 => PEqualNP.Outside.L_lib_1005_aux.askL group block hg hb
            (Fin.castLE hp0 j) x.1) := by
        funext j
        rw [PEqualNP.Outside.L_lib_1005_aux.rd_st ψ x p0 j.val j.isLt]
        simp only [ψ]
        rw [dif_pos (by omega)]
        rfl
      simp only [err]
      rw [hans]
      have := PEqualNP.Outside.L_lib_1005_aux.upper_main group block hg hb h4 p0 hp0 x hx1 hx2
      exact le_trans this (by omega)

import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_1171_aux

open Finset

/-! Basic Boolean tests of the statement, as named functions. -/

noncomputable def passB {n t d : Nat} (scope : Fin t → Finset (Fin n)) (s : Fin t → Fin n → Fin (d + 2))
    (x : Fin n → Fin (d + 2)) : Bool :=
  (Finset.univ : Finset (Fin t)).toList.all (fun j => (scope j).toList.any (fun v => x v != s j v))

theorem passB_true {n t d : Nat} (scope : Fin t → Finset (Fin n)) (s : Fin t → Fin n → Fin (d + 2))
    (x : Fin n → Fin (d + 2)) :
    passB scope s x = true ↔ ∀ j, ∃ v ∈ scope j, x v ≠ s j v := by
  simp [passB]

theorem passB_false {n t d : Nat} (scope : Fin t → Finset (Fin n)) (s : Fin t → Fin n → Fin (d + 2))
    (x : Fin n → Fin (d + 2)) :
    passB scope s x = false ↔ ∃ j, ∀ v ∈ scope j, x v = s j v := by
  have key := passB_true scope s x
  constructor
  · intro h
    have h2 : ¬ ∀ j, ∃ v ∈ scope j, x v ≠ s j v := by
      rw [← key, h]; simp
    push Not at h2
    exact h2
  · rintro ⟨j, hj⟩
    cases hb : passB scope s x
    · rfl
    · obtain ⟨v, hv, hne⟩ := (key.mp hb) j
      exact absurd (hj v hv) hne

noncomputable def covB {n t d : Nat} (scope : Fin t → Finset (Fin n)) (M : Finset (Fin t → Fin n → Fin (d + 2))) :
    Nat :=
  ((Finset.univ : Finset (Fin n → Fin (d + 2))).filter
    (fun x => M.toList.any (fun s => passB scope s x))).card

noncomputable def unc {n t d : Nat} (scope : Fin t → Finset (Fin n)) (M : Finset (Fin t → Fin n → Fin (d + 2))) :
    Finset (Fin n → Fin (d + 2)) :=
  (Finset.univ : Finset (Fin n → Fin (d + 2))).filter (fun x => ∀ s ∈ M, passB scope s x = false)

theorem card_unc {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (M : Finset (Fin t → Fin n → Fin (d + 2))) :
    (Finset.univ : Finset (Fin n → Fin (d + 2))).card - covB scope M = (unc scope M).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Fin (d + 2))))
    (fun x => M.toList.any (fun s => passB scope s x) = true)
  have h2 : (Finset.univ.filter
      (fun x => ¬ (M.toList.any (fun s => passB scope s x) = true))) = unc scope M := by
    unfold unc
    apply Finset.filter_congr
    intro x _
    simp
  unfold covB
  rw [← h2]
  omega

noncomputable def replyB {n t d : Nat} (scope : Fin t → Finset (Fin n)) (A : Finset (Fin n → Fin (d + 2)))
    (s : Fin t → Fin n → Fin (d + 2)) : Bool :=
  A.toList.any (passB scope s)

theorem replyB_false {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (A : Finset (Fin n → Fin (d + 2))) (s : Fin t → Fin n → Fin (d + 2)) (x : Fin n → Fin (d + 2))
    (hx : x ∈ A) (h : replyB scope A s = false) : passB scope s x = false := by
  cases hp : passB scope s x
  · rfl
  · exfalso
    have : replyB scope A s = true := by
      simp only [replyB, List.any_eq_true, Finset.mem_toList]
      exact ⟨x, hx, hp⟩
    rw [this] at h
    exact Bool.noConfusion h

def possibleP {n t : Nat} (d : Nat) (scope : Fin t → Finset (Fin n)) (a b q k : Nat) : Prop :=
  ∃ N : Nat, 0 < N ∧
    ∃ ask : Fin N → Fin k → List Bool → (Fin t → Fin n → Fin (d + 2)),
    ∃ answer : Fin N → List Bool → Bool,
      ∀ A : Finset (Fin n → Fin (d + 2)),
        let yes := ((Finset.univ : Finset (Fin N)).filter (fun seed =>
          answer seed ((List.finRange k).foldl (fun h j =>
            h ++ [replyB scope A (ask seed j h)]) ([] : List Bool)))).card
        if A.Nonempty then q * (N - yes) ≤ b * N else q * yes ≤ a * N

/-! Histories. -/

theorem foldl_false {α : Type} (g : α → List Bool → Bool) (l : List α)
    (h : ∀ i (hi : i < l.length), g (l[i]) (List.replicate i false) = false) :
    l.foldl (fun h j => h ++ [g j h]) [] = List.replicate l.length false := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have h1 : ∀ i (hi : i < l.length), g (l[i]) (List.replicate i false) = false := by
      intro i hi
      have := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at this
    have h2 : g a (List.replicate l.length false) = false := by
      have := h l.length (by simp)
      simpa using this
    rw [List.foldl_append, ih h1]
    simp [h2, List.replicate_succ']

theorem foldl_map {α : Type} (f : α → Bool) (l : List α) (acc : List Bool) :
    l.foldl (fun h j => h ++ [f j]) acc = acc ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [List.foldl_cons, ih, List.append_assoc]

/-! The lower bound direction. -/

theorem forward {n t d : Nat} (scope : Fin t → Finset (Fin n)) (a b q k : Nat) (hq : 0 < q)
    (haq : a ≤ q) (hp : possibleP d scope a b q k) :
    ∃ M : Finset (Fin t → Fin n → Fin (d + 2)), M.card ≤ k ∧
      (q - a) * ((Finset.univ : Finset (Fin n → Fin (d + 2))).card - covB scope M) ≤
        b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card := by
  obtain ⟨N, hN, ask, answer, hA⟩ := hp
  have hist_empty : ∀ seed, (List.finRange k).foldl (fun h j =>
      h ++ [replyB scope ∅ (ask seed j h)]) ([] : List Bool) = List.replicate k false := by
    intro seed
    have := foldl_false (fun j h => replyB scope ∅ (ask seed j h)) (List.finRange k)
      (by intro i hi; simp [replyB])
    rw [List.length_finRange] at this
    exact this
  have hist_single : ∀ seed (x : Fin n → Fin (d + 2)),
      (∀ j : Fin k, passB scope (ask seed j (List.replicate j.val false)) x = false) →
      (List.finRange k).foldl (fun h j => h ++ [replyB scope {x} (ask seed j h)])
        ([] : List Bool) = List.replicate k false := by
    intro seed x hx
    have := foldl_false (fun j h => replyB scope {x} (ask seed j h)) (List.finRange k) (by
      intro i hi
      have hi' : i < k := by simpa using hi
      have := hx ⟨i, hi'⟩
      simpa [replyB] using this)
    rw [List.length_finRange] at this
    exact this
  have hE := hA ∅
  dsimp only at hE
  rw [if_neg Finset.not_nonempty_empty] at hE
  simp only [hist_empty] at hE
  -- hE : q * #{seed | answer seed Z = true} ≤ a * N
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N), R = (Finset.univ : Finset (Fin N)).filter
      (fun seed => ¬ (answer seed (List.replicate k false) = true)) := ⟨_, rfl⟩
  have hRY : ((Finset.univ : Finset (Fin N)).filter
      (fun seed => answer seed (List.replicate k false) = true)).card + R.card = N := by
    rw [hR]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun seed => answer seed (List.replicate k false) = true)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  by_cases hRe : R = ∅
  · refine ⟨∅, by simp, ?_⟩
    rw [hRe, Finset.card_empty, Nat.add_zero] at hRY
    rw [hRY] at hE
    have hqa : q ≤ a := Nat.le_of_mul_le_mul_right hE hN
    have : q - a = 0 := by omega
    rw [this, Nat.zero_mul]
    exact Nat.zero_le _
  · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRe
    obtain ⟨path, hpath⟩ : ∃ path : Fin N → Finset (Fin t → Fin n → Fin (d + 2)),
        path = fun seed => (Finset.univ : Finset (Fin k)).image
          (fun j => ask seed j (List.replicate j.val false)) := ⟨_, rfl⟩
    obtain ⟨s0, hs0, hmin⟩ := Finset.exists_min_image R
      (fun seed => (unc scope (path seed)).card) hRne
    refine ⟨path s0, ?_, ?_⟩
    · rw [hpath]
      exact (Finset.card_image_le).trans (by simp)
    · rw [card_unc]
      have hx : ∀ x : Fin n → Fin (d + 2),
          q * (R.filter (fun seed => x ∈ unc scope (path seed))).card ≤ b * N := by
        intro x
        have hX := hA {x}
        dsimp only at hX
        rw [if_pos (Finset.singleton_nonempty x)] at hX
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin N)))
          (fun seed => answer seed ((List.finRange k).foldl (fun h j =>
            h ++ [replyB scope {x} (ask seed j h)]) ([] : List Bool)) = true)
        rw [Finset.card_univ, Fintype.card_fin] at hsplit
        have hsub : R.filter (fun seed => x ∈ unc scope (path seed)) ⊆
            (Finset.univ : Finset (Fin N)).filter (fun seed => ¬ (answer seed
              ((List.finRange k).foldl (fun h j =>
                h ++ [replyB scope {x} (ask seed j h)]) ([] : List Bool)) = true)) := by
          intro seed hs
          rw [hR] at hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          rw [hist_single seed x ?_]
          · exact hs.1
          · intro j
            have h3 := hs.2
            simp only [unc, Finset.mem_filter, Finset.mem_univ, true_and] at h3
            apply h3
            rw [hpath]
            exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
        have hle := Finset.card_le_card hsub
        calc q * (R.filter (fun seed => x ∈ unc scope (path seed))).card
            ≤ q * (N - ((Finset.univ : Finset (Fin N)).filter (fun seed => answer seed
              ((List.finRange k).foldl (fun h j =>
                h ++ [replyB scope {x} (ask seed j h)]) ([] : List Bool)) = true)).card) := by
              apply Nat.mul_le_mul_left
              omega
          _ ≤ b * N := hX
      have hsum : ∑ x : Fin n → Fin (d + 2), (R.filter (fun seed => x ∈ unc scope (path seed))).card =
          ∑ seed ∈ R, (unc scope (path seed)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro seed _
        simp
      have h1 : R.card * (unc scope (path s0)).card ≤ ∑ seed ∈ R, (unc scope (path seed)).card := by
        have := Finset.card_nsmul_le_sum R (fun seed => (unc scope (path seed)).card)
          (unc scope (path s0)).card (fun seed hs => hmin seed hs)
        simpa using this
      have h2 : q * ∑ x : Fin n → Fin (d + 2),
          (R.filter (fun seed => x ∈ unc scope (path seed))).card ≤
          (Finset.univ : Finset (Fin n → Fin (d + 2))).card * (b * N) := by
        rw [Finset.mul_sum]
        calc ∑ x : Fin n → Fin (d + 2), q * (R.filter (fun seed => x ∈ unc scope (path seed))).card
            ≤ ∑ _x : Fin n → Fin (d + 2), b * N := Finset.sum_le_sum (fun x _ => hx x)
          _ = (Finset.univ : Finset (Fin n → Fin (d + 2))).card * (b * N) := by
            rw [Finset.sum_const, smul_eq_mul]
      have h3 : (q - a) * N ≤ q * R.card := by
        rw [Nat.sub_mul]
        have : q * N = q * ((Finset.univ : Finset (Fin N)).filter
            (fun seed => answer seed (List.replicate k false) = true)).card + q * R.card := by
          rw [← Nat.mul_add, hRY]
        omega
      have h4 : (q - a) * (unc scope (path s0)).card * N ≤
          b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card * N := by
        calc (q - a) * (unc scope (path s0)).card * N
            = ((q - a) * N) * (unc scope (path s0)).card := by ring
          _ ≤ (q * R.card) * (unc scope (path s0)).card := Nat.mul_le_mul_right _ h3
          _ = q * (R.card * (unc scope (path s0)).card) := by ring
          _ ≤ q * ∑ seed ∈ R, (unc scope (path seed)).card := Nat.mul_le_mul_left _ h1
          _ = q * ∑ x : Fin n → Fin (d + 2),
              (R.filter (fun seed => x ∈ unc scope (path seed))).card := by rw [hsum]
          _ ≤ (Finset.univ : Finset (Fin n → Fin (d + 2))).card * (b * N) := h2
          _ = b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card * N := by ring
      exact Nat.le_of_mul_le_mul_right h4 hN

/-! The construction direction. -/

def shiftS {n t d : Nat} (s : Fin t → Fin n → Fin (d + 2)) (w : Fin n → Fin (d + 2)) :
    Fin t → Fin n → Fin (d + 2) :=
  fun i v => s i v + w v

theorem shift_pass {n t d : Nat} (scope : Fin t → Finset (Fin n)) (s : Fin t → Fin n → Fin (d + 2))
    (w x : Fin n → Fin (d + 2)) :
    passB scope (shiftS s w) x = passB scope s (x - w) := by
  rw [Bool.eq_iff_iff, passB_true, passB_true]
  apply forall_congr'
  intro j
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  simp only [shiftS, Pi.sub_apply, ne_eq]
  rw [sub_eq_iff_eq_add]

theorem exists_cover {α : Type} (d0 : α) (M : Finset α) (k : Nat) (hM : M.card ≤ k) :
    ∃ g : Fin k → α, ∀ s ∈ M, ∃ i, g i = s := by
  refine ⟨fun i => M.toList.getD i.val d0, ?_⟩
  intro s hs
  have hs' : s ∈ M.toList := Finset.mem_toList.mpr hs
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hs'
  have hlen : M.toList.length = M.card := Finset.length_toList M
  refine ⟨⟨i, by omega⟩, ?_⟩
  show M.toList.getD i d0 = s
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hget

theorem yes_eq {N k : Nat} {β γ : Type} [Fintype γ] (e : γ ≃ Fin N) (r : β → Bool)
    (ask : Fin N → Fin k → List Bool → β) (answer : Fin N → List Bool → Bool)
    (sig : Fin k → γ → β) (c : γ → Bool)
    (hask : ∀ seed j h, ask seed j h = sig j (e.symm seed))
    (hans : ∀ seed hl, answer seed hl = (hl.any id || c (e.symm seed))) :
    ((Finset.univ : Finset (Fin N)).filter (fun seed => answer seed
      ((List.finRange k).foldl (fun h j => h ++ [r (ask seed j h)]) ([] : List Bool)))).card =
    ((Finset.univ : Finset γ).filter (fun z => (∃ j, r (sig j z) = true) ∨ c z = true)).card := by
  apply Finset.card_equiv e.symm
  intro seed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hans, hask]
  rw [foldl_map]
  simp

theorem count_empty {n t d k : Nat} (scope : Fin t → Finset (Fin n))
    (g : Fin k → Fin t → Fin n → Fin (d + 2)) (a q : Nat) (haq : a ≤ q) :
    ((Finset.univ : Finset ((Fin n → Fin (d + 2)) × Fin q)).filter (fun z =>
      (∃ j, replyB scope ∅ (shiftS (g j) z.1) = true) ∨ decide (z.2.val < a) = true)).card =
      (Finset.univ : Finset (Fin n → Fin (d + 2))).card * a := by
  have : ((Finset.univ : Finset ((Fin n → Fin (d + 2)) × Fin q)).filter (fun z =>
      (∃ j, replyB scope ∅ (shiftS (g j) z.1) = true) ∨ decide (z.2.val < a) = true)) =
      (Finset.univ : Finset (Fin n → Fin (d + 2))) ×ˢ
        ((Finset.univ : Finset (Fin q)).filter (fun c => c.val < a)) := by
    ext z
    simp [replyB]
  rw [this, Finset.card_product, Fin.card_filter_val_lt, min_eq_right haq]

theorem count_reject {n t d k : Nat} (scope : Fin t → Finset (Fin n))
    (g : Fin k → Fin t → Fin n → Fin (d + 2)) (a q : Nat) (haq : a ≤ q)
    (M : Finset (Fin t → Fin n → Fin (d + 2))) (hg : ∀ s ∈ M, ∃ i, g i = s)
    (A : Finset (Fin n → Fin (d + 2))) (x0 : Fin n → Fin (d + 2)) (hx0 : x0 ∈ A) :
    ((Finset.univ : Finset ((Fin n → Fin (d + 2)) × Fin q)).filter (fun z =>
      ¬ ((∃ j, replyB scope A (shiftS (g j) z.1) = true) ∨ decide (z.2.val < a) = true))).card ≤
      (unc scope M).card * (q - a) := by
  have hlt : ((Finset.univ : Finset (Fin q)).filter (fun c => c.val < a)).card = a := by
    rw [Fin.card_filter_val_lt, min_eq_right haq]
  have hge : ((Finset.univ : Finset (Fin q)).filter (fun c => ¬ c.val < a)).card = q - a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin q)))
      (fun c => c.val < a)
    rw [hlt, Finset.card_univ, Fintype.card_fin] at this
    omega
  calc _ ≤ (((Finset.univ : Finset (Fin n → Fin (d + 2))).filter
          (fun w => ∀ j, passB scope (g j) (x0 - w) = false)) ×ˢ
          ((Finset.univ : Finset (Fin q)).filter (fun c => ¬ c.val < a))).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists,
          Bool.not_eq_true, decide_eq_false_iff_not] at hz
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun j => ?_, hz.2⟩
        rw [← shift_pass]
        exact replyB_false scope A _ x0 hx0 (hz.1 j)
    _ = ((Finset.univ : Finset (Fin n → Fin (d + 2))).filter
          (fun w => ∀ j, passB scope (g j) (x0 - w) = false)).card * (q - a) := by
        rw [Finset.card_product, hge]
    _ ≤ (unc scope M).card * (q - a) := by
        apply Nat.mul_le_mul_right
        calc ((Finset.univ : Finset (Fin n → Fin (d + 2))).filter
              (fun w => ∀ j, passB scope (g j) (x0 - w) = false)).card
            = ((Finset.univ : Finset (Fin n → Fin (d + 2))).filter
              (fun y => ∀ j, passB scope (g j) y = false)).card := by
              apply Finset.card_equiv (Equiv.subLeft x0)
              intro w
              simp
          _ ≤ (unc scope M).card := by
              apply Finset.card_le_card
              intro y hy
              simp only [unc, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
              intro s hs
              obtain ⟨i, rfl⟩ := hg s hs
              exact hy i

theorem backward {n t d : Nat} (scope : Fin t → Finset (Fin n)) (a b q k : Nat) (hq : 0 < q)
    (haq : a ≤ q) (M : Finset (Fin t → Fin n → Fin (d + 2))) (hM : M.card ≤ k)
    (h : (q - a) * ((Finset.univ : Finset (Fin n → Fin (d + 2))).card - covB scope M) ≤
        b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card) :
    possibleP d scope a b q k := by
  rw [card_unc] at h
  obtain ⟨g, hg⟩ := exists_cover (fun _ _ => (0 : Fin (d + 2))) M k hM
  let e := Fintype.equivFin ((Fin n → Fin (d + 2)) × Fin q)
  obtain ⟨ask, hask⟩ : ∃ ask : Fin (Fintype.card ((Fin n → Fin (d + 2)) × Fin q)) → Fin k →
      List Bool → (Fin t → Fin n → Fin (d + 2)),
      ∀ seed j h, ask seed j h = (fun j z => shiftS (g j) z.1) j (e.symm seed) :=
    ⟨fun seed j _ => shiftS (g j) (e.symm seed).1, fun _ _ _ => rfl⟩
  obtain ⟨answer, hans⟩ : ∃ answer : Fin (Fintype.card ((Fin n → Fin (d + 2)) × Fin q)) →
      List Bool → Bool,
      ∀ seed hl, answer seed hl = (hl.any id ||
        (fun z : (Fin n → Fin (d + 2)) × Fin q => decide (z.2.val < a)) (e.symm seed)) :=
    ⟨fun seed hl => hl.any id || decide ((e.symm seed).2.val < a), fun _ _ => rfl⟩
  have hNpos : 0 < Fintype.card ((Fin n → Fin (d + 2)) × Fin q) :=
    Fintype.card_pos_iff.mpr ⟨(fun _ => 0, ⟨0, hq⟩)⟩
  have hNcard : Fintype.card ((Fin n → Fin (d + 2)) × Fin q) =
      (Finset.univ : Finset (Fin n → Fin (d + 2))).card * q := by
    rw [Fintype.card_prod, Fintype.card_fin, Finset.card_univ]
  refine ⟨_, hNpos, ask, answer, ?_⟩
  intro A
  dsimp only
  rw [yes_eq e (replyB scope A) ask answer (fun j z => shiftS (g j) z.1)
    (fun z => decide (z.2.val < a)) hask hans]
  split_ifs with hA
  · obtain ⟨x0, hx0⟩ := hA
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ((Fin n → Fin (d + 2)) × Fin q)))
      (fun z => (∃ j, replyB scope A (shiftS (g j) z.1) = true) ∨ decide (z.2.val < a) = true)
    rw [Finset.card_univ] at hsplit
    have hrej := count_reject scope g a q haq M hg A x0 hx0
    have hlhs : Fintype.card ((Fin n → Fin (d + 2)) × Fin q) -
        ((Finset.univ : Finset ((Fin n → Fin (d + 2)) × Fin q)).filter (fun z =>
          (∃ j, replyB scope A (shiftS (g j) z.1) = true) ∨ decide (z.2.val < a) = true)).card ≤
        (unc scope M).card * (q - a) := by
      omega
    refine le_trans (Nat.mul_le_mul_left q hlhs) ?_
    rw [hNcard]
    calc q * ((unc scope M).card * (q - a)) = (q - a) * (unc scope M).card * q := by ring
      _ ≤ b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card * q := Nat.mul_le_mul_right _ h
      _ = b * ((Finset.univ : Finset (Fin n → Fin (d + 2))).card * q) := by ring
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst hAe
    rw [count_empty scope g a q haq, hNcard]
    apply le_of_eq
    ring

/-! Polarization: distinct constant signings minimize the uncovered set. -/

noncomputable def Ufam {n t d k : Nat} (scope : Fin t → Finset (Fin n)) (h : Fin k → Fin t → Fin n → Fin (d + 2)) :
    Finset (Fin n → Fin (d + 2)) :=
  (Finset.univ : Finset (Fin n → Fin (d + 2))).filter (fun x => ∀ i, passB scope (h i) x = false)

def compress {n t d k : Nat} (color : Fin k → Fin (d + 2)) (v : Fin n)
    (h : Fin k → Fin t → Fin n → Fin (d + 2)) : Fin k → Fin t → Fin n → Fin (d + 2) :=
  fun i j u => if u = v then color i else h i j u

theorem memU {n t d k : Nat} (scope : Fin t → Finset (Fin n))
    (h : Fin k → Fin t → Fin n → Fin (d + 2)) (x : Fin n → Fin (d + 2)) :
    x ∈ Ufam scope h ↔ ∀ i, ∃ j, ∀ u ∈ scope j, x u = h i j u := by
  simp only [Ufam, Finset.mem_filter, Finset.mem_univ, true_and, passB_false]

theorem fiber_le {n t d k : Nat} (scope : Fin t → Finset (Fin n)) (color : Fin k → Fin (d + 2))
    (hc : Function.Injective color) (v : Fin n) (h : Fin k → Fin t → Fin n → Fin (d + 2))
    (z : Fin n → Fin (d + 2)) :
    ((Finset.univ : Finset (Fin (d + 2))).filter
      (fun b => Function.update z v b ∈ Ufam scope (compress color v h))).card ≤
    ((Finset.univ : Finset (Fin (d + 2))).filter
      (fun b => Function.update z v b ∈ Ufam scope h)).card := by
  by_cases hfull : ∀ i, ∃ j, v ∉ scope j ∧ ∀ u ∈ scope j, z u = h i j u
  · have : (Finset.univ : Finset (Fin (d + 2))).filter
        (fun b => Function.update z v b ∈ Ufam scope h) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro b _
      rw [memU]
      intro i
      obtain ⟨j, hvj, hj⟩ := hfull i
      refine ⟨j, fun u hu => ?_⟩
      have huv : u ≠ v := fun e => hvj (e ▸ hu)
      rw [Function.update_of_ne huv]
      exact hj u hu
    rw [this]
    exact Finset.card_le_univ _
  · push Not at hfull
    obtain ⟨i0, hi0⟩ := hfull
    have key : ∀ b j, (∀ u ∈ scope j, Function.update z v b u = compress color v h i0 j u) →
        v ∈ scope j ∧ b = color i0 := by
      intro b j hj
      by_cases hv : v ∈ scope j
      · refine ⟨hv, ?_⟩
        have := hj v hv
        simpa [compress] using this
      · exfalso
        obtain ⟨u, hu, hne⟩ := hi0 j hv
        have huv : u ≠ v := fun e => hv (e ▸ hu)
        have := hj u hu
        rw [Function.update_of_ne huv] at this
        simp only [compress, if_neg huv] at this
        exact hne this
    rcases Finset.eq_empty_or_nonempty ((Finset.univ : Finset (Fin (d + 2))).filter
        (fun b => Function.update z v b ∈ Ufam scope (compress color v h))) with he | hne
    · rw [he]
      simp
    · obtain ⟨b, hb⟩ := hne
      have hb' : Function.update z v b ∈ Ufam scope (compress color v h) :=
        (Finset.mem_filter.mp hb).2
      have hle1 : ((Finset.univ : Finset (Fin (d + 2))).filter
          (fun b => Function.update z v b ∈ Ufam scope (compress color v h))).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro b1 hb1 b2 hb2
        obtain ⟨j1, hj1⟩ := (memU _ _ _).mp (Finset.mem_filter.mp hb1).2 i0
        obtain ⟨j2, hj2⟩ := (memU _ _ _).mp (Finset.mem_filter.mp hb2).2 i0
        rw [(key b1 j1 hj1).2, (key b2 j2 hj2).2]
      refine le_trans hle1 ?_
      apply Finset.card_pos.mpr
      obtain ⟨j0, hj0⟩ := (memU _ _ _).mp hb' i0
      obtain ⟨_, hbc⟩ := key b j0 hj0
      refine ⟨h i0 j0 v, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [memU]
      intro i
      by_cases hii : i = i0
      · rw [hii]
        refine ⟨j0, fun u hu => ?_⟩
        by_cases huv : u = v
        · rw [huv, Function.update_self]
        · rw [Function.update_of_ne huv]
          have := hj0 u hu
          rw [Function.update_of_ne huv] at this
          simpa [compress, huv] using this
      · obtain ⟨j, hj⟩ := (memU _ _ _).mp hb' i
        have hvj : v ∉ scope j := by
          intro hv
          have := hj v hv
          simp only [compress, Function.update_self, if_true] at this
          exact hii (hc (this.symm.trans hbc))
        refine ⟨j, fun u hu => ?_⟩
        have huv : u ≠ v := fun e => hvj (e ▸ hu)
        rw [Function.update_of_ne huv]
        have := hj u hu
        rw [Function.update_of_ne huv] at this
        simpa [compress, huv] using this

theorem compress_le {n t d k : Nat} (scope : Fin t → Finset (Fin n)) (color : Fin k → Fin (d + 2))
    (hc : Function.Injective color) (v : Fin n) (h : Fin k → Fin t → Fin n → Fin (d + 2)) :
    (Ufam scope (compress color v h)).card ≤ (Ufam scope h).card := by
  have fib : ∀ (U : Finset (Fin n → Fin (d + 2))) (z : Fin n → Fin (d + 2)), z v = 0 →
      (U.filter (fun x => Function.update x v 0 = z)).card =
      ((Finset.univ : Finset (Fin (d + 2))).filter (fun b => Function.update z v b ∈ U)).card := by
    intro U z hz
    apply Finset.card_nbij' (fun x => x v) (fun b => Function.update z v b)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx ⊢
      rw [← hx.2, Function.update_idem, Function.update_eq_self]
      exact hx.1
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hb ⊢
      refine ⟨hb, ?_⟩
      rw [Function.update_idem, Function.update_eq_self_iff]
      exact hz.symm
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      simp only
      rw [← hx.2, Function.update_idem, Function.update_eq_self]
    · intro b _
      simp only [Function.update_self]
  have hmaps : ∀ U : Finset (Fin n → Fin (d + 2)), ((U : Set (Fin n → Fin (d + 2))).MapsTo
      (fun x => Function.update x v 0)
      ((Finset.univ : Finset (Fin n → Fin (d + 2))).filter (fun z => z v = 0))) := by
    intro U x _
    simp
  rw [Finset.card_eq_sum_card_fiberwise (hmaps (Ufam scope (compress color v h))),
    Finset.card_eq_sum_card_fiberwise (hmaps (Ufam scope h))]
  apply Finset.sum_le_sum
  intro z hz
  have hz' : z v = 0 := (Finset.mem_filter.mp hz).2
  rw [fib _ z hz', fib _ z hz']
  exact fiber_le scope color hc v h z

def iter {n t d k : Nat} (color : Fin k → Fin (d + 2)) (V : Finset (Fin n))
    (h : Fin k → Fin t → Fin n → Fin (d + 2)) : Fin k → Fin t → Fin n → Fin (d + 2) :=
  fun i j u => if u ∈ V then color i else h i j u

theorem iter_le {n t d k : Nat} (scope : Fin t → Finset (Fin n)) (color : Fin k → Fin (d + 2))
    (hc : Function.Injective color) (h : Fin k → Fin t → Fin n → Fin (d + 2))
    (V : Finset (Fin n)) : (Ufam scope (iter color V h)).card ≤ (Ufam scope h).card := by
  induction V using Finset.induction_on with
  | empty =>
    have : iter color ∅ h = h := by
      funext i j u
      simp [iter]
    exact le_of_eq (by rw [this])
  | @insert v V hv ih =>
    have : iter color (insert v V) h = compress color v (iter color V h) := by
      funext i j u
      simp only [iter, compress, Finset.mem_insert]
      by_cases huv : u = v
      · simp [huv]
      · simp [huv]
    rw [this]
    exact le_trans (compress_le scope color hc v _) ih

theorem polar {n t d k : Nat} (scope : Fin t → Finset (Fin n)) (color : Fin k → Fin (d + 2))
    (hc : Function.Injective color) (M : Finset (Fin t → Fin n → Fin (d + 2))) (hM : M.card ≤ k) :
    (unc scope (Finset.univ.image
      (fun i : Fin k => (fun _ _ => color i : Fin t → Fin n → Fin (d + 2))))).card ≤
      (unc scope M).card := by
  obtain ⟨g, hg⟩ := exists_cover (fun _ _ => (0 : Fin (d + 2))) M k hM
  have h1 : unc scope (Finset.univ.image
      (fun i : Fin k => (fun _ _ => color i : Fin t → Fin n → Fin (d + 2)))) =
      Ufam scope (iter color Finset.univ g) := by
    have hit : iter color Finset.univ g = fun i _ _ => color i := by
      funext i j u
      simp [iter]
    rw [hit]
    ext x
    simp [unc, Ufam]
  have h2 : Ufam scope g ⊆ unc scope M := by
    intro x hx
    simp only [Ufam, unc, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro s hs
    obtain ⟨i, rfl⟩ := hg s hs
    exact hx i
  rw [h1]
  exact le_trans (iter_le scope color hc g Finset.univ) (Finset.card_le_card h2)

theorem part2 {n t d : Nat} (scope : Fin t → Finset (Fin n)) (a b q : Nat) (hq : 0 < q)
    (haq : a ≤ q) (k : Nat) (color : Fin k → Fin (d + 2)) (hc : Function.Injective color) :
    possibleP d scope a b q k ↔
      (q - a) * ((Finset.univ : Finset (Fin n → Fin (d + 2))).card - covB scope (Finset.univ.image
        (fun i : Fin k => (fun _ _ => color i : Fin t → Fin n → Fin (d + 2))))) ≤
        b * (Finset.univ : Finset (Fin n → Fin (d + 2))).card := by
  constructor
  · intro hp
    obtain ⟨M, hM, hineq⟩ := forward scope a b q k hq haq hp
    rw [card_unc] at hineq ⊢
    exact le_trans (Nat.mul_le_mul_left _ (polar scope color hc M hM)) hineq
  · intro hineq
    exact backward scope a b q k hq haq _ ((Finset.card_image_le).trans (by simp)) hineq

end PEqualNP.Outside.L_lib_1171_aux

theorem PEqualNP.Outside.L_lib_1171 : ∀ (n t d : Nat) (scope : Fin t → Finset (Fin n)),
  let Word := Fin n → Fin (d + 2)
  let Signing := Fin t → Word
  let labels := (Finset.univ : Finset (Fin t))
  let cube := (Finset.univ : Finset Word)
  let pass := fun (s : Signing) (x : Word) => labels.toList.all (fun j =>
    (scope j).toList.any (fun v => x v != s j v))
  let coverage := fun (M : Finset Signing) =>
    (cube.filter (fun x => M.toList.any (fun s => pass s x))).card
  let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (pass s)
  ∀ (a b q : Nat), 0 < q → a ≤ q → b ≤ q →
    let possible := fun (k : Nat) => ∃ N : Nat, 0 < N ∧
      ∃ ask : Fin N → Fin k → List Bool → Signing, ∃ answer : Fin N → List Bool → Bool,
        ∀ A : Finset Word,
          let yes := ((Finset.univ : Finset (Fin N)).filter (fun seed =>
            answer seed ((List.finRange k).foldl (fun h j =>
              h ++ [reply A (ask seed j h)]) ([] : List Bool)))).card
          if A.Nonempty then q * (N - yes) ≤ b * N else q * yes ≤ a * N
    (∀ k : Nat, possible k ↔ ∃ M : Finset Signing, M.card ≤ k ∧
      (q - a) * (cube.card - coverage M) ≤ b * cube.card) ∧
    (∀ (k : Nat) (color : Fin k → Fin (d + 2)), Function.Injective color →
      let constant : Fin k → Signing := fun i _ _ => color i
      possible k ↔ (q - a) * (cube.card - coverage (Finset.univ.image constant)) ≤ b * cube.card) := by
  intro n t d scope Word Signing labels cube pass coverage reply a b q hq haq _hbq possible
  exact ⟨fun k => ⟨fun hp => PEqualNP.Outside.L_lib_1171_aux.forward scope a b q k hq haq hp,
      fun ⟨M, hM, h⟩ => PEqualNP.Outside.L_lib_1171_aux.backward scope a b q k hq haq M hM h⟩,
    fun k color hc => PEqualNP.Outside.L_lib_1171_aux.part2 scope a b q hq haq k color hc⟩

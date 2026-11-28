import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1372

open PEqualNP.CircuitLowerBounds

theorem stepA {α : Type*} [DecidableEq α] (f : Finset α → ℕ)
    (hloc : ∀ (S : Finset α) (i j : α), i ≠ j → i ∉ S → j ∉ S →
      f (insert i (insert j S)) + f S ≤ f (insert i S) + f (insert j S))
    (Y : Finset α) (p : α) (hp : p ∉ Y) (Q : Finset α) (hpQ : p ∉ Q) :
    f (insert p (Y ∪ Q)) + f Y ≤ f (insert p Y) + f (Y ∪ Q) := by
  revert hpQ
  refine Finset.induction_on Q (by intro _; simp) ?_
  intro q Q hq ih hpQ
  have hpQ' : p ∉ Q := fun h => hpQ (Finset.mem_insert_of_mem h)
  have hpq : p ≠ q := fun h => hpQ (h ▸ Finset.mem_insert_self q Q)
  have ih' := ih hpQ'
  rw [Finset.union_insert]
  by_cases hqY : q ∈ Y ∪ Q
  · rw [Finset.insert_eq_of_mem hqY]
    exact ih'
  · have hpYQ : p ∉ Y ∪ Q := by simp [hp, hpQ']
    have hl := hloc (Y ∪ Q) p q hpq hpYQ hqY
    omega

theorem stepB {α : Type*} [DecidableEq α] (f : Finset α → ℕ)
    (hloc : ∀ (S : Finset α) (i j : α), i ≠ j → i ∉ S → j ∉ S →
      f (insert i (insert j S)) + f S ≤ f (insert i S) + f (insert j S))
    (Y P Q : Finset α) (hd : Disjoint P Q) :
    f (Y ∪ P ∪ Q) + f Y ≤ f (Y ∪ P) + f (Y ∪ Q) := by
  revert hd
  refine Finset.induction_on P (by intro _; simp only [Finset.union_empty]; omega) ?_
  intro p P hp ih hd
  have hd' : Disjoint P Q := Finset.disjoint_of_subset_left (Finset.subset_insert p P) hd
  have hpQ : p ∉ Q := Finset.disjoint_left.mp hd (Finset.mem_insert_self p P)
  have ih' := ih hd'
  rw [Finset.union_insert, Finset.insert_union]
  by_cases hpY : p ∈ Y ∪ P
  · have hm : p ∈ Y ∪ P ∪ Q := Finset.mem_union_left _ hpY
    rw [Finset.insert_eq_of_mem hm, Finset.insert_eq_of_mem hpY]
    exact ih'
  · have hA := stepA f hloc (Y ∪ P) p hpY Q hpQ
    omega

theorem sub_of_local {α : Type*} [DecidableEq α] (f : Finset α → ℕ)
    (hloc : ∀ (S : Finset α) (i j : α), i ≠ j → i ∉ S → j ∉ S →
      f (insert i (insert j S)) + f S ≤ f (insert i S) + f (insert j S))
    (U V : Finset α) : f (U ∩ V) + f (U ∪ V) ≤ f U + f V := by
  have h := stepB f hloc (U ∩ V) (U \ V) (V \ U) disjoint_sdiff_sdiff
  have e1 : U ∩ V ∪ U \ V = U := by ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e2 : U ∩ V ∪ V \ U = V := by ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e3 : U ∩ V ∪ U \ V ∪ V \ U = U ∪ V := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [e3, e1, e2] at h
  omega

theorem local_of_not_sub {α : Type*} [DecidableEq α] (f : Finset α → ℕ)
    (h : ¬ ∀ U V : Finset α, f (U ∩ V) + f (U ∪ V) ≤ f U + f V) :
    ∃ (S : Finset α) (i j : α), i ≠ j ∧ i ∉ S ∧ j ∉ S ∧
      f (insert i S) + f (insert j S) < f S + f (insert i (insert j S)) := by
  by_contra hc
  apply h
  apply sub_of_local f
  intro S i j hij hi hj
  have := not_lt.mp (fun hlt => hc ⟨S, i, j, hij, hi, hj, hlt⟩)
  omega

theorem wires_prefix (C : Circuit) (x : List Bool) (h : ℕ) (hh : h < x.length) :
    (C.wires x).getD h false = x.getD h false := by
  unfold Circuit.wires
  suffices key : ∀ (gs : List Gate) (w : List Bool), h < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD h false =
        w.getD h false from key _ _ hh
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hw
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

theorem arithEq (g : Bool → Bool → ℕ) (δ K T : ℕ) (x y : Bool)
    (hT : T = K + (if x && y then δ else 0)) :
    (g false false + g true true) * T +
      δ * ((if x = false then g false false else 0) + (if y = false then g false false else 0) +
        (if x = true ∧ y = false then g true false else 0) +
        (if y = true ∧ x = false then g false true else 0)) =
    (g false false + g true true) * K + δ * g false false + δ * g x y := by
  subst hT
  cases x <;> cases y <;> simp <;> ring

theorem arithLe (g : Bool → Bool → ℕ) (δ K T : ℕ) (x y : Bool) (hT : K + δ ≤ T) :
    (g false false + g true true) * K + δ * g false false + δ * g x y ≤
    (g false false + g true true) * T +
      δ * ((if x = false then g false false else 0) + (if y = false then g false false else 0) +
        (if x = true ∧ y = false then g true false else 0) +
        (if y = true ∧ x = false then g false true else 0)) := by
  have hm : (g false false + g true true) * (K + δ) ≤ (g false false + g true true) * T :=
    Nat.mul_le_mul_left _ hT
  cases x <;> cases y <;> simp <;> nlinarith [hm]

theorem core : (∀ (a : Nat) (f : Finset (Fin a) → Nat),
  (¬ ∀ U V, f (U ∩ V) + f (U ∪ V) ≤ f U + f V) ↔
  ∃ (i j : Fin a) (S : Finset (Fin a)) (δ K : Nat) (u : Fin a → Bool → Nat),
    i ≠ j ∧ i ∉ S ∧ j ∉ S ∧ 0 < δ ∧
    let lift := fun (x y : Bool) => Finset.univ.filter (fun v : Fin a =>
      if v = i then x else if v = j then y else decide (v ∈ S))
    let price := fun (g : Bool → Bool → Nat) (W : Finset (Fin a)) =>
      let x := decide (i ∈ W)
      let y := decide (j ∈ W)
      (g false false + g true true) * (f W + Finset.univ.sum (fun v => u v (decide (v ∈ W)))) +
      δ*((if x = false then g false false else 0) + (if y = false then g false false else 0) +
        (if x = true ∧ y = false then g true false else 0) +
        (if y = true ∧ x = false then g false true else 0))
    let bias := fun (g : Bool → Bool → Nat) => (g false false + g true true)*K + δ*g false false
    (∀ g W, bias g + δ*g (decide (i ∈ W)) (decide (j ∈ W)) ≤ price g W) ∧
    (∀ g x y, price g (lift x y) = bias g + δ*g x y) ∧
    ∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p z : Nat),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
      C.output < n+2+C.size → p < n+2+C.size → z < n+2+C.size →
      ∃ tap : Fin a → Nat, tap i = p ∧ tap j = z ∧ (∀ v, tap v < n+2+C.size) ∧
        ∀ xs : List Bool, xs.length = n →
          let val := fun h => (C.wires (xs ++ [false,true])).getD h false
          Finset.univ.filter (fun v => val (tap v)) = lift (val p) (val z)) := by
  intro a f
  constructor
  · intro hns
    obtain ⟨S, i, j, hij, hi, hj, hlt⟩ := local_of_not_sub f hns
    obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, δ = f S + f (insert i (insert j S)) - (f (insert i S) + f (insert j S)) :=
      ⟨_, rfl⟩
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = f S + f (insert i S) + f (insert j S) := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : Fin a → Bool → ℕ, u = fun v b =>
        if v = i then (if b then f S else f (insert i S))
        else if v = j then (if b then f S else f (insert j S))
        else if b = decide (v ∈ S) then 0 else K + δ := ⟨_, rfl⟩
    refine ⟨i, j, S, δ, K, u, hij, hi, hj, by omega, ?_⟩
    intro lift price bias
    have memL : ∀ x y v, v ∈ lift x y ↔
        (if v = i then x else if v = j then y else decide (v ∈ S)) = true := by
      intro x y v; simp [lift]
    have hiL : ∀ x y, decide (i ∈ lift x y) = x := by intro x y; simp [memL]
    have hjL : ∀ x y, decide (j ∈ lift x y) = y := by intro x y; simp [memL, Ne.symm hij]
    have L00 : lift false false = S := by
      ext v; rw [memL]
      by_cases h1 : v = i
      · subst h1; simp [hi]
      · by_cases h2 : v = j
        · subst h2; simp [hj, h1]
        · simp [h1, h2]
    have L10 : lift true false = insert i S := by
      ext v; rw [memL]
      by_cases h1 : v = i
      · subst h1; simp
      · by_cases h2 : v = j
        · subst h2; simp [hj, h1]
        · simp [h1, h2]
    have L01 : lift false true = insert j S := by
      ext v; rw [memL]
      by_cases h1 : v = i
      · subst h1; simp [hi, hij]
      · by_cases h2 : v = j
        · subst h2; simp [h1]
        · simp [h1, h2]
    have L11 : lift true true = insert i (insert j S) := by
      ext v; rw [memL]
      by_cases h1 : v = i
      · subst h1; simp
      · by_cases h2 : v = j
        · subst h2; simp [h1]
        · simp [h1, h2]
    have ui : ∀ b, u i b = if b then f S else f (insert i S) := by intro b; rw [hu]; simp
    have uj : ∀ b, u j b = if b then f S else f (insert j S) := by
      intro b; rw [hu]; simp [Ne.symm hij]
    have sumW : ∀ W : Finset (Fin a), (∀ v, v ≠ i → v ≠ j → (v ∈ W ↔ v ∈ S)) →
        Finset.univ.sum (fun v => u v (decide (v ∈ W))) = u i (decide (i ∈ W)) + u j (decide (j ∈ W)) := by
      intro W hm
      rw [Finset.sum_eq_add i j hij]
      · intro c _ hc
        rw [hu]
        simp only [if_neg hc.1, if_neg hc.2]
        rw [if_pos]
        simp [hm c hc.1 hc.2]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro h; exact absurd (Finset.mem_univ j) h
    have Tlift : ∀ x y, f (lift x y) + Finset.univ.sum (fun v => u v (decide (v ∈ lift x y))) =
        K + (if x && y then δ else 0) := by
      intro x y
      rw [sumW (lift x y) (fun v h1 h2 => by rw [memL]; simp [h1, h2]), hiL, hjL, ui, uj]
      cases x <;> cases y
      · rw [L00]; simp; omega
      · rw [L01]; simp; omega
      · rw [L10]; simp; omega
      · rw [L11]; simp; omega
    have matchEq : ∀ W : Finset (Fin a), (∀ v, v ≠ i → v ≠ j → (v ∈ W ↔ v ∈ S)) →
        W = lift (decide (i ∈ W)) (decide (j ∈ W)) := by
      intro W hm
      ext v; rw [memL]
      by_cases h1 : v = i
      · subst h1; simp
      · by_cases h2 : v = j
        · subst h2; simp [h1]
        · simp [h1, h2, hm v h1 h2]
    have Tge : ∀ W : Finset (Fin a), ¬ (∀ v, v ≠ i → v ≠ j → (v ∈ W ↔ v ∈ S)) →
        K + δ ≤ f W + Finset.univ.sum (fun v => u v (decide (v ∈ W))) := by
      intro W hm
      obtain ⟨c, hc⟩ := not_forall.mp hm
      obtain ⟨h1, hc⟩ := not_imp.mp hc
      obtain ⟨h2, hc⟩ := not_imp.mp hc
      have huc : u c (decide (c ∈ W)) = K + δ := by
        rw [hu]
        simp only [if_neg h1, if_neg h2]
        rw [if_neg]
        intro h
        apply hc
        simpa using h
      have hle := Finset.single_le_sum (f := fun v => u v (decide (v ∈ W)))
        (fun v _ => Nat.zero_le _) (Finset.mem_univ c)
      try simp only at hle
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro g W
      simp only [bias, price]
      by_cases hm : ∀ v, v ≠ i → v ≠ j → (v ∈ W ↔ v ∈ S)
      · have e := Tlift (decide (i ∈ W)) (decide (j ∈ W))
        rw [← matchEq W hm] at e
        exact (arithEq g δ K _ _ _ e).symm.le
      · exact arithLe g δ K _ _ _ (Tge W hm)
    · intro g x y
      simp only [bias, price]
      rw [hiL, hjL]
      exact arithEq g δ K _ x y (Tlift x y)
    · intro n C p z _ _ _ hp hz
      refine ⟨fun v => if v = i then p else if v = j then z else if v ∈ S then n + 1 else n,
        by simp, by simp [Ne.symm hij], ?_, ?_⟩
      · intro v
        simp only
        split_ifs <;> omega
      · intro xs hxs val
        have v0 : val n = false := by
          simp only [val]
          rw [wires_prefix C _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hxs]
        have v1 : val (n + 1) = true := by
          simp only [val]
          rw [wires_prefix C _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hxs]
        ext v
        rw [memL]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : v = i
        · subst h1; simp
        · by_cases h2 : v = j
          · subst h2; simp [h1]
          · by_cases h3 : v ∈ S
            · simp [h1, h2, h3, v1]
            · simp [h1, h2, h3, v0]
  · rintro ⟨i, j, S, δ, K, u, hij, hi, hj, hδ, h⟩
    obtain ⟨_, h2, _⟩ := h
    intro hsub
    obtain ⟨L, hL⟩ : ∃ L : Bool → Bool → Finset (Fin a), L = fun x y => Finset.univ.filter
        (fun v : Fin a => if v = i then x else if v = j then y else decide (v ∈ S)) := ⟨_, rfl⟩
    have memL : ∀ x y v, v ∈ L x y ↔
        (if v = i then x else if v = j then y else decide (v ∈ S)) = true := by
      intro x y v; simp [hL]
    have hiL : ∀ x y, decide (i ∈ L x y) = x := by intro x y; simp [memL]
    have hjL : ∀ x y, decide (j ∈ L x y) = y := by intro x y; simp [memL, Ne.symm hij]
    obtain ⟨T, hT⟩ : ∃ T : Bool → Bool → ℕ, ∀ x y,
        T x y = f (L x y) + Finset.univ.sum (fun v => u v (decide (v ∈ L x y))) := ⟨_, fun _ _ => rfl⟩
    have key : ∀ (g : Bool → Bool → ℕ) (x y : Bool),
        (g false false + g true true) * T x y +
          δ * ((if x = false then g false false else 0) + (if y = false then g false false else 0) +
            (if x = true ∧ y = false then g true false else 0) +
            (if y = true ∧ x = false then g false true else 0)) =
        (g false false + g true true) * K + δ * g false false + δ * g x y := by
      intro g x y
      have e := h2 g x y
      rw [hL] at hiL hjL
      simp only [hiL, hjL] at e
      rw [hT, hL]
      exact e
    have k00 := key (fun x y => if x = false ∧ y = false then 1 else 0) false false
    have k10 := key (fun x y => if x = false ∧ y = false then 1 else 0) true false
    have k01 := key (fun x y => if x = false ∧ y = false then 1 else 0) false true
    have k11 := key (fun x y => if x = false ∧ y = false then 1 else 0) true true
    simp at k00 k10 k01 k11
    have hsum : Finset.univ.sum (fun v => u v (decide (v ∈ L true true))) +
        Finset.univ.sum (fun v => u v (decide (v ∈ L false false))) =
        Finset.univ.sum (fun v => u v (decide (v ∈ L true false))) +
        Finset.univ.sum (fun v => u v (decide (v ∈ L false true))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      by_cases h1 : v = i
      · subst h1; simp only [hiL]; try omega
      · by_cases h2 : v = j
        · subst h2; simp only [hjL]; try omega
        · have e : ∀ x y, decide (v ∈ L x y) = decide (v ∈ S) := by
            intro x y; simp [memL, h1, h2]
          rw [e, e, e, e]
    have hcap : L true false ∩ L false true = L false false := by
      ext v; simp only [Finset.mem_inter, memL]
      by_cases h1 : v = i
      · subst h1; simp
      · by_cases h2 : v = j
        · subst h2; simp [h1]
        · simp [h1, h2]
    have hcup : L true false ∪ L false true = L true true := by
      ext v; simp only [Finset.mem_union, memL]
      by_cases h1 : v = i
      · subst h1; simp
      · by_cases h2 : v = j
        · subst h2; simp [h1]
        · simp [h1, h2]
    have hs := hsub (L true false) (L false true)
    rw [hcap, hcup] at hs
    have t00 := hT false false
    have t10 := hT true false
    have t01 := hT false true
    have t11 := hT true true
    omega

end PEqualNP.Outside.L_lib_1372


open PEqualNP.Outside.L_lib_1372 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_lib_1372 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (a : Nat) (f : Finset (Fin a) → Nat),
  (¬ ∀ U V, f (U ∩ V) + f (U ∪ V) ≤ f U + f V) ↔
  ∃ (i j : Fin a) (S : Finset (Fin a)) (δ K : Nat) (u : Fin a → Bool → Nat),
    i ≠ j ∧ i ∉ S ∧ j ∉ S ∧ 0 < δ ∧
    let lift := fun (x y : Bool) => Finset.univ.filter (fun v : Fin a =>
      if v = i then x else if v = j then y else decide (v ∈ S))
    let price := fun (g : Bool → Bool → Nat) (W : Finset (Fin a)) =>
      let x := decide (i ∈ W)
      let y := decide (j ∈ W)
      (g false false + g true true) * (f W + Finset.univ.sum (fun v => u v (decide (v ∈ W)))) +
      δ*((if x = false then g false false else 0) + (if y = false then g false false else 0) +
        (if x = true ∧ y = false then g true false else 0) +
        (if y = true ∧ x = false then g false true else 0))
    let bias := fun (g : Bool → Bool → Nat) => (g false false + g true true)*K + δ*g false false
    (∀ g W, bias g + δ*g (decide (i ∈ W)) (decide (j ∈ W)) ≤ price g W) ∧
    (∀ g x y, price g (lift x y) = bias g + δ*g x y) ∧
    ∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p z : Nat),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
      C.output < n+2+C.size → p < n+2+C.size → z < n+2+C.size →
      ∃ tap : Fin a → Nat, tap i = p ∧ tap j = z ∧ (∀ v, tap v < n+2+C.size) ∧
        ∀ xs : List Bool, xs.length = n →
          let val := fun h => (C.wires (xs ++ [false,true])).getD h false
          Finset.univ.filter (fun v => val (tap v)) = lift (val p) (val z)) := by
  intro a f
  have h := core a f
  dsimp only at h ⊢
  convert h

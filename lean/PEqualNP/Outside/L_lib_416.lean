import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_416_aux

def par (n : ℕ) : Bool := n % 2 == 1

def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> rfl

theorem sgn_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> decide

theorem par_zero : par 0 = false := rfl

theorem par_add (a b : ℕ) : par (a + b) = xor (par a) (par b) := by
  unfold par
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

theorem par_toNat (b : Bool) : par b.toNat = b := by
  cases b <;> rfl

theorem par_sum_add {α : Type} (s : Finset α) (f g : α → ℕ) :
    par (∑ i ∈ s, (f i + g i)) = xor (par (∑ i ∈ s, f i)) (par (∑ i ∈ s, g i)) := by
  rw [Finset.sum_add_distrib, par_add]

theorem par_sum_xor {α : Type} (s : Finset α) (f g : α → Bool) :
    par (∑ i ∈ s, (xor (f i) (g i)).toNat) =
      xor (par (∑ i ∈ s, (f i).toNat)) (par (∑ i ∈ s, (g i).toNat)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [par]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      par_add, par_add, par_add, par_toNat, par_toNat, par_toNat, ih]
    cases f a <;> cases g a <;> cases par (∑ i ∈ s, (f i).toNat) <;>
      cases par (∑ i ∈ s, (g i).toNat) <;> rfl

theorem sgn_par_sum {α : Type} (s : Finset α) (f : α → Bool) :
    sgn (par (∑ i ∈ s, (f i).toNat)) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [par, sgn]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, par_add, par_toNat, sgn_xor, ih]

theorem par_sum_const_false {α : Type} (s : Finset α) :
    par (∑ _i ∈ s, false.toNat) = false := by
  simp [par]

theorem par_sum_ite_eq {α : Type} [DecidableEq α] (s : Finset α) (a : α) (ha : a ∈ s) (b : Bool) :
    par (∑ i ∈ s, (if i = a then b else false).toNat) = b := by
  have : (∑ i ∈ s, (if i = a then b else false).toNat) = b.toNat := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _ hne; simp [hne]
    · intro h; exact absurd ha h
  rw [this, par_toNat]

theorem par_sum_congr_mod {α : Type} (s : Finset α) (f g : α → ℕ)
    (h : ∀ x ∈ s, f x % 2 = g x % 2) :
    par (∑ x ∈ s, f x) = par (∑ x ∈ s, g x) := by
  unfold par
  congr 1
  rw [Finset.sum_nat_mod, Finset.sum_nat_mod (f := g)]
  congr 1
  exact Finset.sum_congr rfl h

theorem par_sum_par_comm {α β : Type} [Fintype α] [Fintype β] (F : α → β → Bool) :
    par (∑ a : α, (par (∑ b : β, (F a b).toNat)).toNat) =
    par (∑ b : β, (par (∑ a : α, (F a b).toNat)).toNat) := by
  have h1 : par (∑ a : α, (par (∑ b : β, (F a b).toNat)).toNat) =
      par (∑ a : α, ∑ b : β, (F a b).toNat) := by
    refine par_sum_congr_mod Finset.univ _ _ fun a _ => ?_
    unfold par
    have hm : (∑ b : β, (F a b).toNat) % 2 = 0 ∨ (∑ b : β, (F a b).toNat) % 2 = 1 := by omega
    rcases hm with hm | hm <;> simp [hm]
  have h2 : par (∑ b : β, (par (∑ a : α, (F a b).toNat)).toNat) =
      par (∑ b : β, ∑ a : α, (F a b).toNat) := by
    refine par_sum_congr_mod Finset.univ _ _ fun b _ => ?_
    unfold par
    have hm : (∑ a : α, (F a b).toNat) % 2 = 0 ∨ (∑ a : α, (F a b).toNat) % 2 = 1 := by omega
    rcases hm with hm | hm <;> simp [hm]
  rw [h1, h2, Finset.sum_comm]

theorem prod_le_prod_nonneg {α : Type} (s : Finset α) (f g : α → ℤ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hfal : f a ≤ g a := hle a (Finset.mem_insert_self a s)
    have hga0 : 0 ≤ g a := hfa0.trans hfal
    have hs0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hsle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
         (fun i hi => hle i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hfal hsle hs0 hga0

theorem gap_eq_natAbs_sum {α : Type} (S : Finset α) (f q : α → Bool) :
    ((2 : ℤ) * ((S.filter (fun w => f w == q w)).card : ℤ) - (S.card : ℤ)) =
      ∑ w ∈ S, sgn (xor (f w) (q w)) := by
  have h1 : ∀ w : α, sgn (xor (f w) (q w)) = (if f w == q w then (2 : ℤ) else 0) - 1 := by
    intro w
    cases f w <;> cases q w <;> decide
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem gap_le_card {α : Type} (S : Finset α) (f q : α → Bool) :
    ((2 : ℤ) * ((S.filter (fun w => f w == q w)).card : ℤ) - (S.card : ℤ)).natAbs ≤ S.card := by
  have hle : (S.filter (fun w => f w == q w)).card ≤ S.card := Finset.card_filter_le _ _
  omega

def linGen {ι : Type} [Fintype ι] (l : ι → Bool) (w : ι → Bool) : Bool :=
  par (∑ j : ι, (l j && w j).toNat)

def quadFormGen {ι : Type} [Fintype ι] (b : Bool) (l : ι → Bool) (a : ι → ι → Bool)
    (w : ι → Bool) : Bool :=
  xor (xor b (linGen l w)) (par (∑ i : ι, ∑ j : ι, (a i j && w i && w j).toNat))

def IsQuadGen {ι : Type} [Fintype ι] (q : (ι → Bool) → Bool) : Prop :=
  ∃ (b : Bool) (l : ι → Bool) (a : ι → ι → Bool), ∀ w, q w = quadFormGen b l a w

theorem linGen_xor {ι : Type} [Fintype ι] (l u v : ι → Bool) :
    linGen l (fun i => xor (u i) (v i)) = xor (linGen l u) (linGen l v) := by
  unfold linGen
  have h : ∀ i, (l i && xor (u i) (v i)) = xor (l i && u i) (l i && v i) := fun i => by
    cases l i <;> cases u i <;> cases v i <;> rfl
  simp_rw [h]
  exact par_sum_xor Finset.univ _ _

theorem linGen_zero {ι : Type} [Fintype ι] (l : ι → Bool) :
    linGen l (fun _ => false) = false := by
  unfold linGen
  simp [par]

theorem sum_sgn_linGen {ι : Type} [Fintype ι] [DecidableEq ι] (l : ι → Bool) :
    (∑ z : ι → Bool, sgn (linGen l z)) =
      if l = fun _ => false then (Fintype.card (ι → Bool) : ℤ) else 0 := by
  by_cases hl : l = fun _ => false
  · subst hl
    simp only [↓reduceIte, linGen, Bool.false_and, Bool.toNat_false, Finset.sum_const_zero, par_zero,
      sgn, Bool.false_eq_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · simp only [hl, ↓reduceIte]
    have hex : ∃ i₀ : ι, l i₀ = true := by
      by_contra hall
      push Not at hall
      apply hl
      funext i
      cases h : l i
      · rfl
      · exact absurd h (hall i)
    obtain ⟨i₀, hi₀⟩ := hex
    let fl : (ι → Bool) → (ι → Bool) := fun z i => xor (z i) (decide (i = i₀))
    have hfl_inv : ∀ z, fl (fl z) = z := fun z => by
      funext i; dsimp only [fl]; cases z i <;> cases decide (i = i₀) <;> rfl
    have hfl_lin : ∀ z, linGen l (fl z) = !(linGen l z) := by
      intro z
      have : linGen l (fl z) = xor (linGen l z) (linGen l (fun i => decide (i = i₀))) :=
        linGen_xor l z (fun i => decide (i = i₀))
      rw [this]
      have h1 : linGen l (fun i => decide (i = i₀)) = true := by
        unfold linGen
        have h2 : ∀ i : ι, (l i && decide (i = i₀)) = if i = i₀ then true else false := fun i => by
          by_cases h : i = i₀
          · subst h; simp [hi₀]
          · simp [h]
        simp_rw [h2]
        exact par_sum_ite_eq Finset.univ i₀ (Finset.mem_univ i₀) true
      rw [h1]
      cases linGen l z <;> rfl
    have hsum : (∑ z : ι → Bool, sgn (linGen l z)) = ∑ z : ι → Bool, sgn (linGen l (fl z)) := by
      refine Fintype.sum_equiv
        { toFun := fl, invFun := fl, left_inv := hfl_inv, right_inv := hfl_inv } _ _ fun z => ?_
      dsimp only [Equiv.coe_fn_mk]
      rw [hfl_inv z]
    have hneg : (∑ z : ι → Bool, sgn (linGen l (fl z))) = -(∑ z : ι → Bool, sgn (linGen l z)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hfl_lin z]
      cases linGen l z <;> rfl
    omega

def polar {ι : Type} (q : (ι → Bool) → Bool) (h t : ι → Bool) : Bool :=
  xor (xor (q (fun i => xor (h i) (t i))) (q h)) (xor (q t) (q (fun _ => false)))

theorem polar_quadFormGen {ι : Type} [Fintype ι] (b : Bool) (l : ι → Bool) (a : ι → ι → Bool)
    (h t : ι → Bool) :
    polar (quadFormGen b l a) h t =
      par (∑ i : ι, ∑ j : ι, (xor (a i j) (a j i) && h i && t j).toNat) := by
  unfold polar quadFormGen
  have h0 : par (∑ i : ι, ∑ j : ι, (a i j && false && false).toNat) = false := by simp [par]
  rw [linGen_xor, linGen_zero, h0]
  have hQ : ∀ u v : ι → Bool,
      par (∑ i : ι, ∑ j : ι, (a i j && xor (u i) (v i) && xor (u j) (v j)).toNat) =
      xor (xor (par (∑ i : ι, ∑ j : ι, (a i j && u i && u j).toNat))
               (par (∑ i : ι, ∑ j : ι, (a i j && v i && v j).toNat)))
          (par (∑ i : ι, ∑ j : ι, (xor (a i j) (a j i) && u i && v j).toNat)) := by
    intro u v
    have hpt : ∀ i j : ι,
        (a i j && xor (u i) (v i) && xor (u j) (v j)) =
        xor (xor (a i j && u i && u j) (a i j && v i && v j))
            (xor (a i j && u i && v j) (a i j && v i && u j)) := fun i j => by
      cases a i j <;> cases u i <;> cases v i <;> cases u j <;> cases v j <;> rfl
    have hpair : ∀ (g : ι → ι → Bool),
        par (∑ i : ι, ∑ j : ι, (g i j).toNat) = par (∑ p : ι × ι, (g p.1 p.2).toNat) := fun g => by
      rw [Fintype.sum_prod_type]
    rw [hpair, hpair, hpair, hpair]
    simp_rw [hpt]
    rw [par_sum_xor, par_sum_xor, par_sum_xor]
    congr 1
    have hswap : (∑ p : ι × ι, (a p.1 p.2 && v p.1 && u p.2).toNat) =
        ∑ p : ι × ι, (a p.2 p.1 && u p.1 && v p.2).toNat := by
      refine Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ fun p => ?_
      dsimp only [Equiv.prodComm_apply, Prod.swap]
      cases a p.1 p.2 <;> cases v p.1 <;> cases u p.2 <;> rfl
    rw [hswap, ← par_sum_xor]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    cases a p.1 p.2 <;> cases a p.2 p.1 <;> cases u p.1 <;> cases v p.2 <;> rfl
  rw [hQ h t]
  cases b <;> cases linGen l h <;> cases linGen l t <;>
    cases par (∑ i : ι, ∑ j : ι, (a i j && h i && h j).toNat) <;>
    cases par (∑ i : ι, ∑ j : ι, (a i j && t i && t j).toNat) <;>
    cases par (∑ i : ι, ∑ j : ι, (xor (a i j) (a j i) && h i && t j).toNat) <;> rfl

theorem polar_is_lin {ι : Type} [Fintype ι] {q : (ι → Bool) → Bool} (hq : IsQuadGen q) (h : ι → Bool) :
    ∃ l : ι → Bool, ∀ t, polar q h t = linGen l t := by
  obtain ⟨b, l0, a, hqeq⟩ := hq
  refine ⟨fun j => par (∑ i : ι, (xor (a i j) (a j i) && h i).toNat), fun t => ?_⟩
  have hpeq : polar q h t = polar (quadFormGen b l0 a) h t := by
    unfold polar; simp only [hqeq]
  rw [hpeq, polar_quadFormGen]
  unfold linGen
  rw [Finset.sum_comm]
  have hmul : ∀ j : ι,
      (par (∑ i : ι, (xor (a i j) (a j i) && h i).toNat) && t j).toNat % 2 =
      (∑ i : ι, (xor (a i j) (a j i) && h i && t j).toNat) % 2 := by
    intro j
    cases t j
    · simp
    · simp only [Bool.and_true, par]
      have hmod : (∑ i : ι, (xor (a i j) (a j i) && h i).toNat) % 2 = 0 ∨
          (∑ i : ι, (xor (a i j) (a j i) && h i).toNat) % 2 = 1 := by omega
      rcases hmod with hm | hm <;> simp [hm]
  exact par_sum_congr_mod Finset.univ _ _ fun j _ => (hmul j).symm

theorem polar_symm {ι : Type} (q : (ι → Bool) → Bool) (h t : ι → Bool) :
    polar q h t = polar q t h := by
  unfold polar
  have : (fun i => xor (h i) (t i)) = (fun i => xor (t i) (h i)) := by
    funext i; exact Bool.xor_comm _ _
  rw [this]
  cases q (fun i => xor (t i) (h i)) <;> cases q h <;> cases q t <;> cases q (fun _ => false) <;> rfl

theorem polar_self {ι : Type} [Fintype ι] {q : (ι → Bool) → Bool} (hq : IsQuadGen q) (h : ι → Bool) :
    polar q h h = false := by
  unfold polar
  have : (fun i => xor (h i) (h i)) = (fun _ => false) := by
    funext i; exact Bool.xor_self _
  rw [this]
  cases q h <;> cases q (fun _ => false) <;> rfl

theorem polar_xor_right {ι : Type} [Fintype ι] {q : (ι → Bool) → Bool} (hq : IsQuadGen q)
    (h t₁ t₂ : ι → Bool) :
    polar q h (fun i => xor (t₁ i) (t₂ i)) = xor (polar q h t₁) (polar q h t₂) := by
  obtain ⟨l, hl⟩ := polar_is_lin hq h
  rw [hl, hl, hl, linGen_xor]

theorem polar_xor_left {ι : Type} [Fintype ι] {q : (ι → Bool) → Bool} (hq : IsQuadGen q)
    (h₁ h₂ t : ι → Bool) :
    polar q (fun i => xor (h₁ i) (h₂ i)) t = xor (polar q h₁ t) (polar q h₂ t) := by
  rw [polar_symm, polar_xor_right hq, polar_symm, polar_symm q t h₂]

theorem quad_add_expand {ι : Type} (q : (ι → Bool) → Bool) (h t : ι → Bool) :
    q (fun i => xor (h i) (t i)) = xor (xor (q h) (xor (q t) (q (fun _ => false)))) (polar q h t) := by
  unfold polar
  cases q (fun i => xor (h i) (t i)) <;> cases q h <;> cases q t <;> cases q (fun _ => false) <;> rfl

def wt {m : ℕ} (h : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => h i = true)).card

def IsSubgroup {m : ℕ} (H : Finset (Fin m → Bool)) : Prop :=
  (fun _ => false) ∈ H ∧ ∀ a ∈ H, ∀ b ∈ H, (fun i => xor (a i) (b i)) ∈ H

def consBool {m : ℕ} (b : Bool) (u : Fin m → Bool) : Fin (m + 1) → Bool :=
  Fin.cons (α := fun _ => Bool) b u

theorem consBool_zero {m : ℕ} (b : Bool) (u : Fin m → Bool) : consBool b u 0 = b := rfl

theorem consBool_succ {m : ℕ} (b : Bool) (u : Fin m → Bool) (j : Fin m) :
    consBool b u j.succ = u j := rfl

theorem consBool_inj {m : ℕ} (b : Bool) : Function.Injective (consBool (m := m) b) := by
  intro u v huv
  funext j
  exact congrFun huv j.succ

def xorEmb {m : ℕ} (hstar : Fin m → Bool) : (Fin m → Bool) ↪ (Fin m → Bool) :=
  ⟨fun u j => xor (hstar j) (u j), fun a b hab => by
    funext j
    have := congrFun hab j
    dsimp only at this
    revert this; cases hstar j <;> cases a j <;> cases b j <;> simp⟩

theorem xorEmb_apply {m : ℕ} (hstar u : Fin m → Bool) :
    xorEmb hstar u = fun j => xor (hstar j) (u j) := rfl

theorem subgroup_wt_bound : ∀ (m : ℕ) (H : Finset (Fin m → Bool)), IsSubgroup H →
    ∃ k ≤ m, H.card = 2 ^ k ∧
      ∀ c : Fin m → Bool,
        ∑ h ∈ H, 2 ^ (m - wt (fun i => xor (c i) (h i))) ≤ 3 ^ k * 2 ^ (m - k) := by
  intro m
  induction m with
  | zero =>
    intro H hH
    have hHeq : H = {fun _ => false} := by
      ext h
      simp only [Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · rintro rfl; exact hH.1
    refine ⟨0, le_refl 0, by simp [hHeq], fun c => ?_⟩
    simp [hHeq]
  | succ m ih =>
    intro H hH
    let H0 : Finset (Fin m → Bool) :=
      Finset.univ.filter (fun h' => consBool false h' ∈ H)
    let H1 : Finset (Fin m → Bool) :=
      Finset.univ.filter (fun h' => consBool true h' ∈ H)
    have hH0_sub : IsSubgroup H0 := by
      refine ⟨?_, ?_⟩
      · simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
        have : consBool false (fun _ : Fin m => false) = fun _ => false := by
          funext i; cases i using Fin.cases <;> rfl
        rw [this]; exact hH.1
      · intro a ha b hb
        simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
        have : consBool false (fun i => xor (a i) (b i)) =
            (fun i => xor (consBool false a i) (consBool false b i)) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [this]; exact hH.2 _ ha _ hb
    obtain ⟨k, hkm, hH0card, hH0sum⟩ := ih H0 hH0_sub
    have hwt_cons : ∀ (b : Bool) (u : Fin m → Bool),
        wt (consBool b u) = b.toNat + wt u := by
      intro b u
      unfold wt
      have hsplit : (Finset.univ.filter (fun i : Fin (m + 1) => consBool b u i = true)) =
          (if b = true then {0} else ∅) ∪
            (Finset.univ.filter (fun j : Fin m => u j = true)).map (Fin.succEmb m) := by
        ext i
        cases i using Fin.cases with
        | zero =>
          cases b <;> simp [Fin.succEmb, consBool_zero]
        | succ j =>
          cases b <;> simp [Fin.succEmb, consBool_succ]
      rw [hsplit, Finset.card_union_of_disjoint, Finset.card_map]
      · cases b <;> simp
      · rw [Finset.disjoint_left]
        intro x hx hx2
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx2
        obtain ⟨j, _, rfl⟩ := hx2
        cases b
        · simp at hx
        · simp only [↓reduceIte, Finset.mem_singleton] at hx
          exact Fin.succ_ne_zero j hx
    have hwt_le : ∀ (u : Fin m → Bool), wt u ≤ m := fun u => by
      unfold wt
      calc (Finset.univ.filter (fun i : Fin m => u i = true)).card
          ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
        _ = m := Finset.card_fin m
    let emb0 : (Fin m → Bool) ↪ (Fin (m + 1) → Bool) := ⟨consBool false, consBool_inj false⟩
    let emb1 : (Fin m → Bool) ↪ (Fin (m + 1) → Bool) := ⟨consBool true, consBool_inj true⟩
    have hsplitH : H = H0.map emb0 ∪ H1.map emb1 := by
      ext h
      simp only [Finset.mem_union, Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk, H0, H1,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hh
        have heq : consBool (h 0) (Fin.tail h) = h := Fin.cons_self_tail h
        cases h0 : h 0
        · left; refine ⟨Fin.tail h, ?_, ?_⟩ <;> rwa [← h0, heq]
        · right; refine ⟨Fin.tail h, ?_, ?_⟩ <;> rwa [← h0, heq]
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> exact hu
    have hdisj : Disjoint (H0.map emb0) (H1.map emb1) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨a, _, rfl⟩ := hx1
      obtain ⟨b, _, hab⟩ := hx2
      have := congrFun hab 0
      simp [consBool_zero] at this
    by_cases hH1e : H1 = ∅
    · refine ⟨k, by omega, ?_, fun c => ?_⟩
      · rw [hsplitH, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
          hH1e, Finset.card_empty, Nat.add_zero, hH0card]
      · rw [hsplitH, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map, hH1e,
          Finset.sum_empty, Nat.add_zero]
        dsimp only [emb0, Function.Embedding.coeFn_mk]
        have hstep : ∀ u ∈ H0,
            2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i))) ≤
            2 * 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) := by
          intro u _
          have hc : (fun i => xor (c i) (consBool false u i)) =
              consBool (c 0) (fun j => xor (Fin.tail c j) (u j)) := by
            funext i; cases i using Fin.cases <;> simp [Fin.tail, consBool_zero, consBool_succ]
          rw [hc, hwt_cons]
          have hw := hwt_le (fun j => xor (Fin.tail c j) (u j))
          cases c 0
          · simp only [Bool.toNat_false, Nat.zero_add]
            have : m + 1 - wt (fun j => xor (Fin.tail c j) (u j)) =
                (m - wt (fun j => xor (Fin.tail c j) (u j))) + 1 := by omega
            rw [this, pow_succ']
          · simp only [Bool.toNat_true]
            have : m + 1 - (1 + wt (fun j => xor (Fin.tail c j) (u j))) =
                m - wt (fun j => xor (Fin.tail c j) (u j)) := by omega
            rw [this]
            omega
        calc ∑ u ∈ H0, 2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i)))
            ≤ ∑ u ∈ H0, 2 * 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) :=
              Finset.sum_le_sum hstep
          _ = 2 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) :=
              (Finset.mul_sum ..).symm
          _ ≤ 2 * (3 ^ k * 2 ^ (m - k)) := Nat.mul_le_mul_left 2 (hH0sum (Fin.tail c))
          _ = 3 ^ k * 2 ^ (m + 1 - k) := by
              have : m + 1 - k = (m - k) + 1 := by omega
              rw [this, pow_succ']; ring
    · obtain ⟨hstar, hhstar⟩ := Finset.nonempty_iff_ne_empty.mpr hH1e
      have hhstarH : consBool true hstar ∈ H := (Finset.mem_filter.mp hhstar).2
      have hH1_bij : H1 = H0.map (xorEmb hstar) := by
        ext u
        simp only [H1, H0, Finset.mem_map, xorEmb_apply, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hu
          refine ⟨fun j => xor (hstar j) (u j), ?_, ?_⟩
          · have : consBool false (fun j => xor (hstar j) (u j)) =
                fun i => xor (consBool true hstar i) (consBool true u i) := by
              funext i; cases i using Fin.cases <;> rfl
            rw [this]; exact hH.2 _ hhstarH _ hu
          · funext j; dsimp only; cases hstar j <;> cases u j <;> rfl
        · rintro ⟨v, hv, rfl⟩
          have : consBool true (fun j => xor (hstar j) (v j)) =
              fun i => xor (consBool true hstar i) (consBool false v i) := by
            funext i; cases i using Fin.cases <;> rfl
          rw [this]; exact hH.2 _ hhstarH _ hv
      have hH1card : H1.card = 2 ^ k := by rw [hH1_bij, Finset.card_map, hH0card]
      refine ⟨k + 1, by omega, ?_, fun c => ?_⟩
      · rw [hsplitH, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
          hH0card, hH1card, pow_succ']
        omega
      · rw [hsplitH, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map, hH1_bij,
          Finset.sum_map]
        simp only [emb0, emb1, Function.Embedding.coeFn_mk, xorEmb_apply]
        have h0_eq : ∀ u : Fin m → Bool,
            2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i))) =
            (if c 0 = false then 2 else 1) * 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) := by
          intro u
          have hc : (fun i => xor (c i) (consBool false u i)) =
              consBool (c 0) (fun j => xor (Fin.tail c j) (u j)) := by
            funext i; cases i using Fin.cases <;> simp [Fin.tail, consBool_zero, consBool_succ]
          rw [hc, hwt_cons]
          have hw := hwt_le (fun j => xor (Fin.tail c j) (u j))
          cases c 0
          · simp only [Bool.toNat_false, Nat.zero_add, ↓reduceIte]
            have : m + 1 - wt (fun j => xor (Fin.tail c j) (u j)) =
                (m - wt (fun j => xor (Fin.tail c j) (u j))) + 1 := by omega
            rw [this, pow_succ']
          · simp only [Bool.toNat_true, Bool.true_eq_false, ↓reduceIte, one_mul]
            congr 1; omega
        have h1_eq : ∀ u : Fin m → Bool,
            2 ^ (m + 1 - wt (fun i => xor (c i) (consBool true (fun j => xor (hstar j) (u j)) i))) =
            (if c 0 = true then 2 else 1) *
              2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j))) := by
          intro u
          have hc : (fun i => xor (c i) (consBool true (fun j => xor (hstar j) (u j)) i)) =
              consBool (!(c 0)) (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)) := by
            funext i
            cases i using Fin.cases with
            | zero => cases c 0 <;> rfl
            | succ j =>
              simp only [consBool_succ, Fin.tail]
              cases c j.succ <;> cases hstar j <;> cases u j <;> rfl
          rw [hc, hwt_cons]
          have hw := hwt_le (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j))
          cases c 0
          · simp only [Bool.not_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte, one_mul]
            congr 1; omega
          · simp only [Bool.not_true, Bool.toNat_false, Nat.zero_add, ↓reduceIte]
            have : m + 1 - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)) =
                (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j))) + 1 := by omega
            rw [this, pow_succ']
        simp_rw [h0_eq, h1_eq]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        have hb0 := hH0sum (Fin.tail c)
        have hb1 := hH0sum (fun j => xor (Fin.tail c j) (hstar j))
        have hadd : (if c 0 = false then 2 else 1) + (if c 0 = true then 2 else 1) = 3 := by
          cases c 0 <;> rfl
        have hsub : m + 1 - (k + 1) = m - k := by omega
        rw [hsub, pow_succ']
        calc (if c 0 = false then 2 else 1) *
                (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) +
              (if c 0 = true then 2 else 1) *
                (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j))))
            ≤ (if c 0 = false then 2 else 1) * (3 ^ k * 2 ^ (m - k)) +
              (if c 0 = true then 2 else 1) * (3 ^ k * 2 ^ (m - k)) :=
              Nat.add_le_add (Nat.mul_le_mul_left _ hb0) (Nat.mul_le_mul_left _ hb1)
          _ = ((if c 0 = false then 2 else 1) + (if c 0 = true then 2 else 1)) *
                (3 ^ k * 2 ^ (m - k)) := (Nat.add_mul ..).symm
          _ = 3 * (3 ^ k * 2 ^ (m - k)) := by rw [hadd]
          _ = 3 * 3 ^ k * 2 ^ (m - k) := by ring

theorem walsh_quad_sq {m : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R) (α : Fin m → Bool) :
    let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
    (∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))) ^ 2 =
      (2 ^ m : ℤ) * ∑ h ∈ Rad, sgn (xor (xor (R h) (R (fun _ => false))) (linGen α h)) := by
  intro Rad
  let S : ℤ := ∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))
  have hsq : S ^ 2 = ∑ h : Fin m → Bool, ∑ z : Fin m → Bool,
      sgn (xor (R z) (linGen α z)) * sgn (xor (R (fun i => xor (z i) (h i)))
        (linGen α (fun i => xor (z i) (h i)))) := by
    dsimp only [S]
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    refine Fintype.sum_equiv
      { toFun := fun y i => xor (z i) (y i)
        invFun := fun y i => xor (z i) (y i)
        left_inv := fun y => by funext i; dsimp only; cases z i <;> cases y i <;> rfl
        right_inv := fun y => by funext i; dsimp only; cases z i <;> cases y i <;> rfl }
      _ _ fun y => ?_
    dsimp only [Equiv.coe_fn_mk]
    have hinv : (fun i => xor (z i) (xor (z i) (y i))) = y := by
      funext i; cases z i <;> cases y i <;> rfl
    rw [hinv]
  rw [show (∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))) ^ 2 = S ^ 2 from rfl, hsq]
  have hinner : ∀ h : Fin m → Bool,
      (∑ z : Fin m → Bool,
        sgn (xor (R z) (linGen α z)) * sgn (xor (R (fun i => xor (z i) (h i)))
          (linGen α (fun i => xor (z i) (h i))))) =
      if h ∈ Rad then
        (2 ^ m : ℤ) * sgn (xor (xor (R h) (R (fun _ => false))) (linGen α h))
      else 0 := by
    intro h
    have hpt : ∀ z : Fin m → Bool,
        sgn (xor (R z) (linGen α z)) * sgn (xor (R (fun i => xor (z i) (h i)))
          (linGen α (fun i => xor (z i) (h i)))) =
        sgn (xor (xor (R h) (R (fun _ => false))) (linGen α h)) * sgn (polar R h z) := by
      intro z
      rw [← sgn_xor, ← sgn_xor, quad_add_expand R z h, linGen_xor, polar_symm R z h]
      congr 1
      cases R z <;> cases R h <;> cases R (fun _ => false) <;>
        cases linGen α z <;> cases linGen α h <;> cases polar R h z <;> rfl
    simp_rw [hpt, ← Finset.mul_sum]
    obtain ⟨l, hl⟩ := polar_is_lin hR h
    simp_rw [hl]
    rw [sum_sgn_linGen l]
    by_cases hmem : h ∈ Rad
    · have hl0 : l = fun _ => false := by
        funext i
        have hpol := (Finset.mem_filter.mp hmem).2 (fun j => decide (j = i))
        rw [hl] at hpol
        unfold linGen at hpol
        have h2 : ∀ j : Fin m, (l j && decide (j = i)) = if j = i then l i else false := fun j => by
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        simp_rw [h2] at hpol
        rw [par_sum_ite_eq Finset.univ i (Finset.mem_univ i) (l i)] at hpol
        exact hpol
      simp only [hmem, ↓reduceIte, hl0, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      push_cast
      ring
    · have hlne : l ≠ fun _ => false := by
        intro hl0
        apply hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
        rw [hl, hl0]
        unfold linGen
        simp [par]
      simp [hmem, hlne]
  simp_rw [hinner]
  rw [← Finset.sum_filter, Finset.mul_sum]
  congr 1
  ext h
  simp

theorem walsh_rad_linear_sum {m : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R) (α : Fin m → Bool) :
    let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
    let χ : (Fin m → Bool) → Bool := fun h => xor (xor (R h) (R (fun _ => false))) (linGen α h)
    (∑ h ∈ Rad, sgn (χ h)) = if ∀ h ∈ Rad, χ h = false then (Rad.card : ℤ) else 0 := by
  intro Rad χ
  have hχ_xor : ∀ h₁ ∈ Rad, ∀ h₂ ∈ Rad, χ (fun i => xor (h₁ i) (h₂ i)) = xor (χ h₁) (χ h₂) := by
    intro h₁ hh₁ h₂ _
    have hpol : polar R h₁ h₂ = false := (Finset.mem_filter.mp hh₁).2 h₂
    dsimp only [χ]
    rw [quad_add_expand R h₁ h₂, hpol, linGen_xor]
    cases R h₁ <;> cases R h₂ <;> cases R (fun _ => false) <;>
      cases linGen α h₁ <;> cases linGen α h₂ <;> rfl
  by_cases hall : ∀ h ∈ Rad, χ h = false
  · rw [if_pos hall]
    have : ∀ h ∈ Rad, sgn (χ h) = 1 := fun h hh => by rw [hall h hh]; rfl
    rw [Finset.sum_congr rfl this]
    simp
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨h₀, hh₀, hχ0⟩ := hall
    have hχ0t : χ h₀ = true := by cases h : χ h₀ <;> simp_all
    have hRad_sub : IsSubgroup Rad := by
      refine ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
        unfold polar
        have : (fun i => xor false (t i)) = t := by funext i; simp
        rw [this]
        cases R t <;> cases R (fun _ => false) <;> rfl
      · intro a ha b hb
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
        rw [polar_xor_left hR, (Finset.mem_filter.mp ha).2 t, (Finset.mem_filter.mp hb).2 t]
        rfl
    have hbij : (∑ h ∈ Rad, sgn (χ h)) = ∑ h ∈ Rad, sgn (χ (fun i => xor (h₀ i) (h i))) := by
      refine Finset.sum_bij (fun h _ => fun i => xor (h₀ i) (h i)) ?_ ?_ ?_ ?_
      · intro h hh; exact hRad_sub.2 h₀ hh₀ h hh
      · intro a _ b _ hab
        funext i
        have := congrFun hab i
        revert this; cases h₀ i <;> cases a i <;> cases b i <;> simp
      · intro h hh
        refine ⟨fun i => xor (h₀ i) (h i), hRad_sub.2 h₀ hh₀ h hh, ?_⟩
        funext i; dsimp only; cases h₀ i <;> cases h i <;> rfl
      · intro h _
        congr 2; funext i; dsimp only; cases h₀ i <;> cases h i <;> rfl
    have hneg : (∑ h ∈ Rad, sgn (χ (fun i => xor (h₀ i) (h i)))) = -(∑ h ∈ Rad, sgn (χ h)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hχ_xor h₀ hh₀ h hh, hχ0t]
      cases χ h <;> rfl
    omega

theorem walsh_abs_eq_rad_sum {m s : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R)
    (hs : 2 * s ≤ m)
    (hrad : (Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false)).card =
      2 ^ (m - 2 * s))
    (α : Fin m → Bool) :
    let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
    (Rad.card : ℤ) * |∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))| =
      (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad, sgn (xor (xor (R h) (R (fun _ => false))) (linGen α h)) := by
  intro Rad
  have hsq := walsh_quad_sq R hR α
  have hlin := walsh_rad_linear_sum R hR α
  dsimp only at hsq hlin
  rw [hlin] at hsq ⊢
  by_cases hall : ∀ h ∈ Rad, xor (xor (R h) (R (fun _ => false))) (linGen α h) = false
  · rw [if_pos hall] at hsq ⊢
    have hval : (∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))) ^ 2 = ((2 ^ (m - s) : ℤ)) ^ 2 := by
      rw [hsq, hrad]
      push_cast
      rw [← pow_add, ← pow_mul]
      congr 1
      omega
    have habs : |∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))| = (2 ^ (m - s) : ℤ) := by
      have h1 : |∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))| ^ 2 = ((2 ^ (m - s) : ℤ)) ^ 2 := by
        rw [sq_abs]; exact hval
      have hnonneg1 : 0 ≤ |∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))| := abs_nonneg _
      have hnonneg2 : (0 : ℤ) ≤ 2 ^ (m - s) := by positivity
      nlinarith
    rw [habs, mul_comm]
  · rw [if_neg hall] at hsq ⊢
    simp only [mul_zero] at hsq ⊢
    have h0 : ∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z)) = 0 := sq_eq_zero_iff.mp hsq
    simp [h0]

theorem two_bit_and_bias (c d0 d1 : Bool) :
    |∑ u : Fin 2 → Bool, sgn (xor (u 0 && u 1) (xor c (xor (d0 && u 0) (d1 && u 1))))| = 2 := by
  cases c <;> cases d0 <;> cases d1 <;> decide

theorem two_bit_lin_bias (c d0 d1 : Bool) :
    |∑ u : Fin 2 → Bool, sgn (xor c (xor (d0 && u 0) (d1 && u 1)))| ≤ 4 := by
  cases c <;> cases d0 <;> cases d1 <;> decide

def otherIdx (l : Fin 3) (k : Fin 2) : Fin 3 :=
  match l.val, k.val with
  | 0, 0 => 1
  | 0, _ => 2
  | 1, 0 => 0
  | 1, _ => 2
  | _, 0 => 0
  | _, _ => 1

def mergeLane {m : ℕ} (lane : Fin m → Fin 3)
    (u : Fin m → Fin 2 → Bool) (z : Fin m → Bool) : Fin m → Fin 3 → Bool :=
  fun i j =>
    if j = lane i then z i
    else if j = otherIdx (lane i) 0 then u i 0
    else u i 1

def splitLaneEquiv (m : ℕ) (lane : Fin m → Fin 3) :
    (Fin m → Fin 3 → Bool) ≃ (Fin m → Fin 2 → Bool) × (Fin m → Bool) where
  toFun w := (fun i k => w i (otherIdx (lane i) k), fun i => w i (lane i))
  invFun p := mergeLane lane p.1 p.2
  left_inv w := by
    funext i j
    dsimp only [mergeLane]
    generalize hl : lane i = li
    fin_cases li <;> fin_cases j <;> simp [otherIdx]
  right_inv p := by
    apply Prod.ext
    · funext i k
      dsimp only [mergeLane]
      generalize hl : lane i = li
      fin_cases li <;> fin_cases k <;> simp [otherIdx]
    · funext i
      unfold mergeLane
      simp

theorem mergeLane_eq_xor {m : ℕ} (lane : Fin m → Fin 3)
    (u : Fin m → Fin 2 → Bool) (z : Fin m → Bool) :
    mergeLane lane u z = fun i j =>
      xor (mergeLane lane u (fun _ => false) i j) ((j == lane i) && z i) := by
  funext i j
  unfold mergeLane
  by_cases h : j = lane i
  · subst h; simp
  · simp [h, beq_false_of_ne h]

theorem prod_three_mergeLane {m : ℕ} (lane : Fin m → Fin 3)
    (u : Fin m → Fin 2 → Bool) (z : Fin m → Bool) (i : Fin m) :
    (mergeLane lane u z i 0 && mergeLane lane u z i 1 && mergeLane lane u z i 2) =
      ((u i 0 && u i 1) && z i) := by
  unfold mergeLane otherIdx
  generalize hl : lane i = li
  fin_cases li <;> cases u i 0 <;> cases u i 1 <;> cases z i <;> simp

theorem sum_prod_fin_fun {m : ℕ} {α : Type} [Fintype α] (F : Fin m → α → ℤ) :
    (∑ u : Fin m → α, ∏ i : Fin m, F i (u i)) = ∏ i : Fin m, ∑ x : α, F i x := by
  exact (Fintype.prod_sum F).symm

theorem abs_prod_eq_prod_abs {α : Type} (s : Finset α) (f : α → ℤ) :
    |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, abs_mul, ih]

theorem quad_to_gen {m : ℕ} (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat))) :
    IsQuadGen (fun v : (Fin m × Fin 3) → Bool => q (fun i j => v (i, j))) := by
  obtain ⟨b, l, a, hqeq⟩ := hq
  exact ⟨b, l, a, fun v => hqeq (fun i j => v (i, j))⟩

theorem restrict_isQuadGen {m : ℕ} (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3) :
    IsQuadGen (fun z : Fin m → Bool => q (fun i j => (j == lane i) && z i)) := by
  obtain ⟨b, l, a, hqeq⟩ := hq
  refine ⟨b, fun i => l (i, lane i), fun i j => a (i, lane i) (j, lane j), fun z => ?_⟩
  dsimp only
  rw [hqeq]
  unfold quadFormGen linGen
  congr 1
  · congr 1
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (lane i)]
    · simp
    · intro k _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (lane i)]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (lane j)]
      · simp
      · intro k _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro k _ hne
      refine Finset.sum_eq_zero fun p _ => ?_
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_split_lane (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3) :
    let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
    let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
      fun u p => mergeLane lane u (fun _ => false) p.1 p.2
    let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
    let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
      par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
    (∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
      ∑ u : Fin m → Fin 2 → Bool,
        sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
          ∑ z : Fin m → Bool,
            sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z)) := by
  intro R uVec Bcoeff ν
  let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun i j => v (i, j))
  let zVec : (Fin m → Bool) → (Fin m × Fin 3) → Bool := fun z p => (p.2 == lane p.1) && z p.1
  have hpolar_uz : ∀ u z, polar Qv (uVec u) (zVec z) = linGen (ν u) z := by
    intro u z
    have hpeq : polar Qv (uVec u) (zVec z) = polar (quadFormGen b0 l0 a0) (uVec u) (zVec z) := by
      unfold polar Qv; simp only [hqeq]; rfl
    rw [hpeq, polar_quadFormGen]
    unfold linGen ν
    rw [Finset.sum_comm]
    have hsum_eq : (∑ p₂ : Fin m × Fin 3, ∑ p₁ : Fin m × Fin 3,
        (Bcoeff p₁ p₂ && uVec u p₁ && zVec z p₂).toNat) =
        ∑ i : Fin m, ∑ p₁ : Fin m × Fin 3,
          (Bcoeff p₁ (i, lane i) && uVec u p₁ && z i).toNat := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single (lane i)]
      · refine Finset.sum_congr rfl fun p₁ _ => by simp [zVec]
      · intro k _ hne
        refine Finset.sum_eq_zero fun p₁ _ => by simp [zVec, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum_eq]
    refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
    cases z i
    · simp
    · simp only [Bool.and_true, par]
      have hmod : (∑ p₁ : Fin m × Fin 3, (Bcoeff p₁ (i, lane i) && uVec u p₁).toNat) % 2 = 0 ∨
          (∑ p₁ : Fin m × Fin 3, (Bcoeff p₁ (i, lane i) && uVec u p₁).toNat) % 2 = 1 := by omega
      rcases hmod with hm | hm <;> simp [hm]
  trans (∑ p : (Fin m → Fin 2 → Bool) × (Fin m → Bool),
    sgn (xor (par (∑ i : Fin m,
        (mergeLane lane p.1 p.2 i 0 && mergeLane lane p.1 p.2 i 1 && mergeLane lane p.1 p.2 i 2).toNat))
      (q (mergeLane lane p.1 p.2))))
  · refine Fintype.sum_equiv (splitLaneEquiv m lane) _ _ fun w => ?_
    have hw : mergeLane lane ((splitLaneEquiv m lane) w).1 ((splitLaneEquiv m lane) w).2 = w :=
      (splitLaneEquiv m lane).left_inv w
    rw [hw]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← sgn_xor]
    congr 1
    have hf : par (∑ i : Fin m,
        (mergeLane lane u z i 0 && mergeLane lane u z i 1 && mergeLane lane u z i 2).toNat) =
        linGen (fun i => u i 0 && u i 1) z := by
      unfold linGen
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [prod_three_mergeLane]
    have hq_exp : q (mergeLane lane u z) =
        xor (xor (q (mergeLane lane u (fun _ => false))) (xor (R z) (q (fun _ _ => false))))
            (linGen (ν u) z) := by
      have hm := mergeLane_eq_xor lane u z
      have hq1 : q (mergeLane lane u z) = Qv (fun p => xor (uVec u p) (zVec z p)) := by
        dsimp only [Qv, uVec, zVec]
        congr 1
      rw [hq1, quad_add_expand Qv (uVec u) (zVec z), hpolar_uz u z]
    rw [hf, hq_exp]
    have hlin_xor : linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z =
        xor (linGen (fun i => u i 0 && u i 1) z) (linGen (ν u) z) := by
      unfold linGen
      have hpt : ∀ i, (xor (u i 0 && u i 1) (ν u i) && z i) =
          xor ((u i 0 && u i 1) && z i) (ν u i && z i) := fun i => by
        cases u i 0 <;> cases u i 1 <;> cases ν u i <;> cases z i <;> rfl
      simp_rw [hpt]
      exact par_sum_xor Finset.univ _ _
    rw [hlin_xor]
    cases linGen (fun i => u i 0 && u i 1) z <;> cases q (mergeLane lane u (fun _ => false)) <;>
      cases R z <;> cases q (fun _ _ => false) <;> cases linGen (ν u) z <;> rfl

theorem factor_u_product (m : ℕ) (h d0 d1 : Fin m → Bool) :
    |∑ u : Fin m → Fin 2 → Bool,
      ∏ j : Fin m, sgn (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1)))| ≤
      (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ) := by
  have hrewrite : (∑ u : Fin m → Fin 2 → Bool,
      ∏ j : Fin m, sgn (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1)))) =
      ∏ j : Fin m, ∑ x : Fin 2 → Bool,
        sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1))) :=
    sum_prod_fin_fun (fun (j : Fin m) (x : Fin 2 → Bool) =>
      sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1))))
  rw [hrewrite, abs_prod_eq_prod_abs]
  have hprod_le : (∏ j : Fin m,
      |∑ x : Fin 2 → Bool,
        sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1)))|) ≤
      ∏ j : Fin m, (if h j = true then (2 : ℤ) else 4) := by
    refine prod_le_prod_nonneg Finset.univ _ _ (fun j _ => abs_nonneg _) (fun j _ => ?_)
    cases h j
    · simp only [Bool.false_and, Bool.false_xor, Bool.false_eq_true, ↓reduceIte]
      have := two_bit_lin_bias false (d0 j) (d1 j)
      simpa only [Bool.false_xor] using this
    · simp only [Bool.true_and, ↓reduceIte]
      have := two_bit_and_bias false (d0 j) (d1 j)
      simpa only [Bool.false_xor] using le_of_eq this
  have hprod_eq : (∏ j : Fin m, (if h j = true then (2 : ℤ) else 4)) =
      (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ) := by
    have hsplit : ∀ j : Fin m,
        (if h j = true then (2 : ℤ) else 4) = 2 * (if h j = false then (2 : ℤ) else 1) := fun j => by
      cases h j <;> rfl
    simp_rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    have hsum_card : (Finset.univ.filter (fun j : Fin m => h j = false)).card +
        (Finset.univ.filter (fun j : Fin m => h j = true)).card = m := by
      have hcomp : Finset.univ.filter (fun j : Fin m => h j = false) =
          (Finset.univ.filter (fun j : Fin m => h j = true))ᶜ := by
        ext j; cases h j <;> simp
      rw [hcomp, Finset.card_compl, Fintype.card_fin]
      have hle : (Finset.univ.filter (fun j : Fin m => h j = true)).card ≤ m := by
        calc (Finset.univ.filter (fun j : Fin m => h j = true)).card
            ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
          _ = m := Finset.card_fin m
      omega
    unfold wt
    omega
  exact hprod_le.trans_eq hprod_eq

theorem lane_u_factor_bound (m : ℕ) (lane : Fin m → Fin 3)
    (Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool) (h : Fin m → Bool) :
    let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
      fun u p => mergeLane lane u (fun _ => false) p.1 p.2
    let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
      par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
    |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| ≤
      (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ) := by
  intro uVec ν
  let d0 : Fin m → Bool := fun j =>
    par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat)
  let d1 : Fin m → Bool := fun j =>
    par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat)
  have hlin_u : ∀ u : Fin m → Fin 2 → Bool,
      linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h =
      par (∑ j : Fin m,
        (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1))).toNat) := by
    intro u
    have h1 : linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h =
        xor (par (∑ j : Fin m, (h j && (u j 0 && u j 1)).toNat)) (linGen (ν u) h) := by
      unfold linGen
      have hpt : ∀ i, (xor (u i 0 && u i 1) (ν u i) && h i) =
          xor (h i && (u i 0 && u i 1)) (ν u i && h i) := fun i => by
        cases u i 0 <;> cases u i 1 <;> cases ν u i <;> cases h i <;> rfl
      simp_rw [hpt]
      exact par_sum_xor Finset.univ _ _
    have h2 : linGen (ν u) h = par (∑ j : Fin m, (xor (d0 j && u j 0) (d1 j && u j 1)).toNat) := by
      unfold linGen ν
      have hmod1 : par (∑ i : Fin m,
          (par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) && h i).toNat) =
          par (∑ i : Fin m, ∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p && h i).toNat) := by
        refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
        cases h i
        · simp
        · simp only [Bool.and_true, par]
          have hm : (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) % 2 = 0 ∨
              (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      rw [hmod1, Finset.sum_comm, Fintype.sum_prod_type]
      have htriple : ∀ j : Fin m,
          (∑ l : Fin 3, ∑ i : Fin m, (Bcoeff (j, l) (i, lane i) && uVec u (j, l) && h i).toNat) =
          (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i && u j 0).toNat) +
          (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i && u j 1).toNat) := by
        intro j
        rw [Fin.sum_univ_three]
        have hlane_cases : ∀ (lj : Fin 3),
            (∑ i : Fin m, (Bcoeff (j, 0) (i, lane i) &&
              (if (0 : Fin 3) = lj then false else if (0 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) +
            (∑ i : Fin m, (Bcoeff (j, 1) (i, lane i) &&
              (if (1 : Fin 3) = lj then false else if (1 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) +
            (∑ i : Fin m, (Bcoeff (j, 2) (i, lane i) &&
              (if (2 : Fin 3) = lj then false else if (2 : Fin 3) = otherIdx lj 0 then u j 0 else u j 1) && h i).toNat) =
            (∑ i : Fin m, (Bcoeff (j, otherIdx lj 0) (i, lane i) && h i && u j 0).toNat) +
            (∑ i : Fin m, (Bcoeff (j, otherIdx lj 1) (i, lane i) && h i && u j 1).toNat) := by
          intro lj
          fin_cases lj <;> simp [otherIdx, Bool.and_right_comm]
        simpa only [uVec, mergeLane] using hlane_cases (lane j)
      simp_rw [htriple]
      refine par_sum_congr_mod Finset.univ _ _ fun j _ => ?_
      have ha : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i && u j 0).toNat) % 2 =
          (d0 j && u j 0).toNat % 2 := by
        cases u j 0
        · simp
        · simp only [Bool.and_true, d0, par]
          have hm : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat) % 2 = 0 ∨
              (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      have hb : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i && u j 1).toNat) % 2 =
          (d1 j && u j 1).toNat % 2 := by
        cases u j 1
        · simp
        · simp only [Bool.and_true, d1, par]
          have hm : (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat) % 2 = 0 ∨
              (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      rw [Nat.add_mod, ha, hb]
      cases d0 j && u j 0 <;> cases d1 j && u j 1 <;> rfl
    rw [h1, h2, ← par_sum_xor]
  have hcongr : (∑ u : Fin m → Fin 2 → Bool,
      sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) =
      ∑ u : Fin m → Fin 2 → Bool,
        ∏ j : Fin m, sgn (xor (h j && (u j 0 && u j 1)) (xor (d0 j && u j 0) (d1 j && u j 1))) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hlin_u u, sgn_par_sum]
  rw [hcongr]
  exact factor_u_product m h d0 d1

theorem lane_rank_bound (m s : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3) (hs : 2 * s ≤ m)
    (hrad : ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t : Fin m → Bool,
      xor (xor (q (fun i j => (j == lane i) && xor (h i) (t i)))
               (q (fun i j => (j == lane i) && h i)))
          (xor (q (fun i j => (j == lane i) && t i))
               (q (fun i j => (j == lane i) && false))) = false)).card = 2 ^ (m - 2 * s)) :
    9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    8 ^ s * 6 ^ m := by
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hRquad : IsQuadGen R := restrict_isQuadGen q hq lane
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  have hRad_card : Rad.card = 2 ^ (m - 2 * s) := hrad
  obtain ⟨b0, l0, a0, hqeq⟩ := hq
  let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
    fun u p => mergeLane lane u (fun _ => false) p.1 p.2
  let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
    par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
  have hsum_split := sum_split_lane m q b0 l0 a0 hqeq lane
  dsimp only at hsum_split
  have htri : |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      ∑ u : Fin m → Fin 2 → Bool,
        |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := by
    rw [hsum_split]
    calc |∑ u : Fin m → Fin 2 → Bool,
            sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
              ∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))|
        ≤ ∑ u : Fin m → Fin 2 → Bool,
            |sgn (xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))) *
              ∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u : Fin m → Fin 2 → Bool,
            |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := by
          refine Finset.sum_congr rfl fun u _ => by rw [abs_mul, sgn_abs, one_mul]
  have hmul_rad : (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
        |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
    have h1 : (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
        (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
          |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| :=
      mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg _)
    have h2 : (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
        |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| =
        (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
          sgn (xor (R h) (R (fun _ => false))) *
            ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := by
      rw [Finset.mul_sum]
      have hterm : ∀ u : Fin m → Fin 2 → Bool,
          (Rad.card : ℤ) *
            |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| =
          (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            sgn (xor (R h) (R (fun _ => false))) *
              sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := fun u => by
        have hw := walsh_abs_eq_rad_sum R hRquad hs hRad_card (fun i => xor (u i 0 && u i 1) (ν u i))
        dsimp only at hw
        rw [hw]
        congr 1
        refine Finset.sum_congr rfl fun h _ => sgn_xor _ _
      simp_rw [hterm, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => (Finset.mul_sum ..).symm
    have h3 : ∑ h ∈ Rad,
        sgn (xor (R h) (R (fun _ => false))) *
          ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) ≤
        ∑ h ∈ Rad,
          |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
      refine Finset.sum_le_sum fun h _ => ?_
      calc sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)
          ≤ |sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| :=
            le_abs_self _
        _ = |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
            rw [abs_mul, sgn_abs, one_mul]
    calc (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|
        ≤ (Rad.card : ℤ) * ∑ u : Fin m → Fin 2 → Bool,
            |∑ z : Fin m → Bool, sgn (xor (R z) (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) z))| := h1
      _ = (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            sgn (xor (R h) (R (fun _ => false))) *
              ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) := h2
      _ ≤ (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hu_bound : ∀ h : Fin m → Bool,
      |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| ≤
        (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ) :=
    lane_u_factor_bound m lane Bcoeff
  have hRad_sub : IsSubgroup Rad := by
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      unfold polar
      have : (fun i => xor false (t i)) = t := by funext i; simp
      rw [this]
      cases R t <;> cases R (fun _ => false) <;> rfl
    · intro a ha b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      rw [polar_xor_left hRquad, (Finset.mem_filter.mp ha).2 t, (Finset.mem_filter.mp hb).2 t]
      rfl
  obtain ⟨k, hkm, hRad_k, hwt_sum⟩ := subgroup_wt_bound m Rad hRad_sub
  have hk_eq : k = m - 2 * s := by
    have hpow : 2 ^ k = 2 ^ (m - 2 * s) := hRad_k.symm.trans hRad_card
    exact Nat.pow_right_injective (by omega) hpow
  have hwt_nat : ∑ h ∈ Rad, 2 ^ (m - wt h) ≤ 3 ^ (m - 2 * s) * 2 ^ (2 * s) := by
    have h0 := hwt_sum (fun _ => false)
    have hsimpl : ∀ h ∈ Rad, 2 ^ (m - wt (fun i => xor false (h i))) = 2 ^ (m - wt h) := fun h _ => by
      simp
    rw [Finset.sum_congr rfl hsimpl, hk_eq] at h0
    have hsub : m - (m - 2 * s) = 2 * s := by omega
    rwa [hsub] at h0
  have hwt_int : (∑ h ∈ Rad, (2 ^ (m - wt h) : ℤ)) ≤ (3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ) := by
    exact_mod_cast hwt_nat
  have hmain : (2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)) := by
    calc (2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|
        = (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| := by
          rw [hRad_card]; push_cast; rfl
      _ ≤ (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := hmul_rad
      _ ≤ (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad, (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => hu_bound h) (by positivity)
      _ = (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ∑ h ∈ Rad, (2 ^ (m - wt h) : ℤ) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)) :=
          mul_le_mul_of_nonneg_left hwt_int (by positivity)
  have hmul9 : (2 ^ (m - 2 * s) : ℤ) * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) ≤
      (2 ^ (m - 2 * s) : ℤ) * (8 ^ s * 6 ^ m) := by
    have hrhs : (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
        ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) =
        (2 ^ (m - 2 * s) : ℤ) * (8 ^ s * 6 ^ m) := by
      have h9 : (9 ^ s : ℤ) = 3 ^ (2 * s) := by
        rw [pow_mul]; norm_num
      have h8 : (8 ^ s : ℤ) = 2 ^ (3 * s) := by
        rw [pow_mul]; norm_num
      have h6 : (6 ^ m : ℤ) = 2 ^ m * 3 ^ m := by
        rw [← mul_pow]; norm_num
      rw [h9, h8, h6]
      have h2exp : (2 ^ (m - s) : ℤ) * 2 ^ m * 2 ^ (2 * s) = 2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1; omega
      have h3exp : (3 ^ (2 * s) : ℤ) * 3 ^ (m - 2 * s) = 3 ^ m := by
        rw [← pow_add]; congr 1; omega
      calc (3 ^ (2 * s) : ℤ) * (2 ^ (m - s) * 2 ^ m * (3 ^ (m - 2 * s) * 2 ^ (2 * s)))
          = (3 ^ (2 * s) * 3 ^ (m - 2 * s)) * (2 ^ (m - s) * 2 ^ m * 2 ^ (2 * s)) := by ring
        _ = 3 ^ m * (2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m) := by rw [h3exp, h2exp]
        _ = 2 ^ (m - 2 * s) * (2 ^ (3 * s) * (2 ^ m * 3 ^ m)) := by ring
    calc (2 ^ (m - 2 * s) : ℤ) * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)
        = (9 ^ s : ℤ) * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by ring
      _ ≤ (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
            ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = (2 ^ (m - 2 * s) : ℤ) * (8 ^ s * 6 ^ m) := hrhs
  exact le_of_mul_le_mul_left hmul9 (by positivity)

theorem symplectic_subspace_rad {m : ℕ} (B : (Fin m → Bool) → (Fin m → Bool) → Bool)
    (hself : ∀ x, B x x = false)
    (hsymm : ∀ x y, B x y = B y x)
    (hxor : ∀ x y z, B x (fun i => xor (y i) (z i)) = xor (B x y) (B x z)) :
    ∀ (d : ℕ) (V : Finset (Fin m → Bool)), IsSubgroup V → V.card = 2 ^ d →
      ∃ s : ℕ, 2 * s ≤ d ∧
        (V.filter (fun h => ∀ t ∈ V, B h t = false)).card = 2 ^ (d - 2 * s) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro V hV hVcard
    have hB0 : ∀ x, B x (fun _ => false) = false := fun x => by
      have := hxor x (fun _ => false) (fun _ => false)
      have h0 : (fun i => xor false false) = (fun _ : Fin m => false) := rfl
      rw [h0] at this
      cases h : B x (fun _ => false) <;> simp_all
    by_cases hzero : ∀ x ∈ V, ∀ y ∈ V, B x y = false
    · refine ⟨0, by omega, ?_⟩
      have hfilt : V.filter (fun h => ∀ t ∈ V, B h t = false) = V := by
        ext h; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hzero h
      rw [hfilt, hVcard]; simp
    · push Not at hzero
      obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hzero
      have he12 : B e₁ e₂ = true := by cases h : B e₁ e₂ <;> simp_all
      have he21 : B e₂ e₁ = true := by rw [hsymm, he12]
      let W : Finset (Fin m → Bool) := V.filter (fun v => B e₁ v = false ∧ B e₂ v = false)
      have hWsub : IsSubgroup W := by
        refine ⟨?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨hV.1, hB0 e₁, hB0 e₂⟩
        · intro a ha b hb
          obtain ⟨haV, ha1, ha2⟩ := Finset.mem_filter.mp ha
          obtain ⟨hbV, hb1, hb2⟩ := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨hV.2 a haV b hbV,
            by rw [hxor, ha1, hb1]; rfl, by rw [hxor, ha2, hb2]; rfl⟩
      let comb : (Bool × Bool) × (Fin m → Bool) → (Fin m → Bool) :=
        fun p i => xor (p.2 i) (xor (p.1.1 && e₁ i) (p.1.2 && e₂ i))
      have hB_scale : ∀ (x y : Fin m → Bool) (c : Bool),
          B x (fun i => c && y i) = (c && B x y) := fun x y c => by
        cases c
        · simp [hB0]
        · simp
      have hB_comb : ∀ (x : Fin m → Bool) (b₁ b₂ : Bool) (w : Fin m → Bool),
          B x (comb ((b₁, b₂), w)) = xor (B x w) (xor (b₁ && B x e₁) (b₂ && B x e₂)) := by
        intro x b₁ b₂ w
        change B x (fun i => xor (w i) (xor (b₁ && e₁ i) (b₂ && e₂ i))) = _
        rw [hxor, hxor, hB_scale, hB_scale]
      have hcomb_mem : ∀ b₁ b₂ : Bool, ∀ w ∈ V, comb ((b₁, b₂), w) ∈ V := by
        intro b₁ b₂ w hw
        have h1 : (fun i => b₁ && e₁ i) ∈ V := by
          cases b₁
          · simpa using hV.1
          · simpa using he₁
        have h2 : (fun i => b₂ && e₂ i) ∈ V := by
          cases b₂
          · simpa using hV.1
          · simpa using he₂
        exact hV.2 w hw _ (hV.2 _ h1 _ h2)
      have hV_eq : V = ((Finset.univ : Finset (Bool × Bool)) ×ˢ W).image comb := by
        ext v
        simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
        constructor
        · intro hv
          let b₁ := B e₂ v
          let b₂ := B e₁ v
          let w : Fin m → Bool := comb ((b₁, b₂), v)
          have hwV : w ∈ V := hcomb_mem b₁ b₂ v hv
          have hw1 : B e₁ w = false := by
            rw [hB_comb, hself, he12]
            dsimp only [b₁, b₂]
            cases B e₁ v <;> cases B e₂ v <;> rfl
          have hw2 : B e₂ w = false := by
            rw [hB_comb, hself, he21]
            dsimp only [b₁, b₂]
            cases B e₁ v <;> cases B e₂ v <;> rfl
          refine ⟨((b₁, b₂), w), Finset.mem_filter.mpr ⟨hwV, hw1, hw2⟩, ?_⟩
          funext i
          dsimp only [comb, w]
          cases v i <;> cases b₁ <;> cases b₂ <;> cases e₁ i <;> cases e₂ i <;> rfl
        · rintro ⟨⟨⟨b₁, b₂⟩, w⟩, hw, rfl⟩
          exact hcomb_mem b₁ b₂ w (Finset.mem_filter.mp hw).1
      have hcomb_inj : Set.InjOn comb ↑((Finset.univ : Finset (Bool × Bool)) ×ˢ W) := by
        intro p₁ hp₁ p₂ hp₂ heq
        rcases p₁ with ⟨⟨a₁, a₂⟩, w₁⟩
        rcases p₂ with ⟨⟨b₁, b₂⟩, w₂⟩
        simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and,
          Finset.mem_coe] at hp₁ hp₂
        obtain ⟨_, hw11, hw12⟩ := Finset.mem_filter.mp hp₁
        obtain ⟨_, hw21, hw22⟩ := Finset.mem_filter.mp hp₂
        have hb1 : a₁ = b₁ := by
          have := congrArg (B e₂) heq
          rw [hB_comb, hB_comb, hw12, hw22, he21, hself] at this
          simpa using this
        have hb2 : a₂ = b₂ := by
          have := congrArg (B e₁) heq
          rw [hB_comb, hB_comb, hw11, hw21, he12, hself] at this
          simpa using this
        subst hb1; subst hb2
        congr 1
        funext i
        have hi := congrFun heq i
        dsimp only [comb] at hi
        revert hi
        cases w₁ i <;> cases w₂ i <;> cases a₁ <;> cases a₂ <;> cases e₁ i <;> cases e₂ i <;> simp
      have hcard4 : V.card = 4 * W.card := by
        rw [hV_eq, Finset.card_image_of_injOn hcomb_inj, Finset.card_product]
        have : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
        rw [this]
      have hd2 : 2 ≤ d := by
        by_contra hlt
        have : d = 0 ∨ d = 1 := by omega
        have hWpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hWsub.1⟩
        rcases this with rfl | rfl <;> omega
      have hWcard : W.card = 2 ^ (d - 2) := by
        have hpow : 2 ^ d = 4 * 2 ^ (d - 2) := by
          have : d = (d - 2) + 2 := by omega
          conv_lhs => rw [this]
          rw [pow_add]; ring
        omega
      have hRad_eq : V.filter (fun h => ∀ t ∈ V, B h t = false) =
          W.filter (fun h => ∀ t ∈ W, B h t = false) := by
        ext h
        simp only [W, Finset.mem_filter]
        constructor
        · rintro ⟨hhV, hht⟩
          refine ⟨⟨hhV, ?_, ?_⟩, fun t ht => hht t ht.1⟩
          · rw [hsymm]; exact hht e₁ he₁
          · rw [hsymm]; exact hht e₂ he₂
        · rintro ⟨⟨hhV, hh1, hh2⟩, hht⟩
          refine ⟨hhV, fun t ht => ?_⟩
          rw [hV_eq] at ht
          obtain ⟨⟨⟨b₁, b₂⟩, w⟩, hw, rfl⟩ := Finset.mem_image.mp ht
          have hwW : w ∈ W := (Finset.mem_product.mp hw).2
          rw [hB_comb, hht w (Finset.mem_filter.mp hwW), hsymm h e₁, hh1, hsymm h e₂, hh2]
          cases b₁ <;> cases b₂ <;> rfl
      obtain ⟨s', hs'le, hs'card⟩ := ih (d - 2) (by omega) W hWsub hWcard
      refine ⟨s' + 1, by omega, ?_⟩
      rw [hRad_eq, hs'card]
      congr 1; omega

theorem symplectic_rad_card {m : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R) :
    ∃ s : ℕ, 2 * s ≤ m ∧
      (Finset.univ.filter (fun h : Fin m → Bool => ∀ t : Fin m → Bool, polar R h t = false)).card =
        2 ^ (m - 2 * s) := by
  have huniv_sub : IsSubgroup (Finset.univ : Finset (Fin m → Bool)) :=
    ⟨Finset.mem_univ _, fun _ _ _ _ => Finset.mem_univ _⟩
  have huniv_card : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
    simp [Fintype.card_fun]
  obtain ⟨s, hsle, hcard⟩ := symplectic_subspace_rad (polar R) (polar_self hR) (polar_symm R)
    (polar_xor_right hR) m Finset.univ huniv_sub huniv_card
  refine ⟨s, hsle, ?_⟩
  convert hcard using 2
  ext h; simp

theorem gap_univ_le (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat))) :
    |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤ 6 ^ m := by
  let lane : Fin m → Fin 3 := fun _ => 0
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  obtain ⟨s, hs, hrad⟩ := symplectic_rad_card R (restrict_isQuadGen q hq lane)
  have hrb := lane_rank_bound m s q hq lane hs hrad
  have h89 : (8 ^ s : ℤ) ≤ 9 ^ s := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : 8 ≤ 9) s
  have hstep : (9 ^ s : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (9 ^ s : ℤ) * 6 ^ m :=
    hrb.trans (mul_le_mul_of_nonneg_right h89 (by positivity))
  exact le_of_mul_le_mul_left hstep (by positivity)

theorem flip_second_diff {m : ℕ} (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (i j : Fin m × Fin 3) (w : Fin m → Fin 3 → Bool) :
    let flip := fun (w : Fin m → Fin 3 → Bool) (p : Fin m × Fin 3) (h : Fin m) (l : Fin 3) =>
      xor (w h l) (decide ((h, l) = p))
    xor (xor (q w) (q (flip w i))) (xor (q (flip w j)) (q (flip (flip w i) j))) =
      xor (a0 i j) (a0 j i) := by
  intro flip
  let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun h l => v (h, l))
  have hQv : IsQuadGen Qv := ⟨b0, l0, a0, fun v => hqeq (fun h l => v (h, l))⟩
  let v : (Fin m × Fin 3) → Bool := fun p => w p.1 p.2
  let ei : (Fin m × Fin 3) → Bool := fun p => decide (p = i)
  let ej : (Fin m × Fin 3) → Bool := fun p => decide (p = j)
  have hqw : q w = Qv v := rfl
  have hqi : q (flip w i) = Qv (fun p => xor (v p) (ei p)) := rfl
  have hqj : q (flip w j) = Qv (fun p => xor (v p) (ej p)) := rfl
  have hqij : q (flip (flip w i) j) = Qv (fun p => xor (xor (v p) (ei p)) (ej p)) := rfl
  rw [hqw, hqi, hqj, hqij]
  rw [quad_add_expand Qv (fun p => xor (v p) (ei p)) ej, polar_xor_left hQv v ei ej,
      quad_add_expand Qv v ei, quad_add_expand Qv v ej]
  have hcancel : ∀ a b c d e f g : Bool,
      xor (xor a (xor (xor a (xor b c)) d))
          (xor (xor (xor a (xor e c)) f)
               (xor (xor (xor (xor a (xor b c)) d) (xor e c)) (xor f g))) = g := by
    intro a b c d e f g
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl
  rw [hcancel]
  have hpeq : polar Qv ei ej = polar (quadFormGen b0 l0 a0) ei ej := by
    unfold polar Qv; simp only [hqeq]; rfl
  rw [hpeq, polar_quadFormGen]
  have hsum : (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
      (xor (a0 p₁ p₂) (a0 p₂ p₁) && ei p₁ && ej p₂).toNat) = (xor (a0 i j) (a0 j i)).toNat := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [ei, ej]
      · intro p₂ _ hne; simp [ej, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p₁ _ hne
      refine Finset.sum_eq_zero fun p₂ _ => by simp [ei, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, par_toNat]

theorem cross_gap_bound (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (i j : Fin m × Fin 3) (hij : i.1 ≠ j.1) (hcross : xor (a0 i j) (a0 j i) = true) :
    9 * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))| ≤ 8 * 6 ^ m := by
  let lane : Fin m → Fin 3 := fun k => if k = i.1 then i.2 else if k = j.1 then j.2 else 0
  have hlane_i : lane i.1 = i.2 := by simp [lane]
  have hlane_j : lane j.1 = j.2 := by simp [lane, hij.symm]
  let R : (Fin m → Bool) → Bool := fun z => q (fun k l => (l == lane k) && z k)
  have hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)) :=
    ⟨b0, l0, a0, hqeq⟩
  obtain ⟨s, hs, hrad⟩ := symplectic_rad_card R (restrict_isQuadGen q hq lane)
  have hpol_true : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = true := by
    let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun h l => v (h, l))
    let ei : (Fin m × Fin 3) → Bool := fun p => decide (p = i)
    let ej : (Fin m × Fin 3) → Bool := fun p => decide (p = j)
    have hR1 : ∀ z : Fin m → Bool, R z = Qv (fun p => (p.2 == lane p.1) && z p.1) := fun _ => rfl
    have he1 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && decide (p.1 = i.1)) = ei := by
      funext ⟨k, l⟩
      rcases i with ⟨i1, i2⟩
      by_cases hk : k = i1
      · subst hk; by_cases hl : l = i2
        · subst hl; simp [ei, hlane_i]
        · simp [ei, hlane_i, hl, beq_false_of_ne hl]
      · simp [ei, hk]
    have he2 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && decide (p.1 = j.1)) = ej := by
      funext ⟨k, l⟩
      rcases j with ⟨j1, j2⟩
      by_cases hk : k = j1
      · subst hk; by_cases hl : l = j2
        · subst hl; simp [ej, hlane_j]
        · simp [ej, hlane_j, hl, beq_false_of_ne hl]
      · simp [ej, hk]
    have he12 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && xor (decide (p.1 = i.1)) (decide (p.1 = j.1))) =
        fun p => xor (ei p) (ej p) := by
      funext p
      have h1 := congrFun he1 p
      have h2 := congrFun he2 p
      rw [← h1, ← h2]
      cases (p.2 == lane p.1) <;> cases decide (p.1 = i.1) <;> cases decide (p.1 = j.1) <;> rfl
    have he0 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && false) = fun _ => false := by
      funext p; simp
    have hpeq : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = polar Qv ei ej := by
      unfold polar
      rw [hR1, hR1, hR1, hR1, he1, he2, he12, he0]
    rw [hpeq]
    have hpeq2 : polar Qv ei ej = polar (quadFormGen b0 l0 a0) ei ej := by
      unfold polar Qv; simp only [hqeq]; rfl
    rw [hpeq2, polar_quadFormGen]
    have hsum : (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
        (xor (a0 p₁ p₂) (a0 p₂ p₁) && ei p₁ && ej p₂).toNat) = (xor (a0 i j) (a0 j i)).toNat := by
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp [ei, ej]
        · intro p₂ _ hne; simp [ej, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p₁ _ hne
        refine Finset.sum_eq_zero fun p₂ _ => by simp [ei, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, par_toNat, hcross]
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    subst hs_eq
    simp only [mul_zero, Nat.sub_zero] at hrad
    have hRad_univ : (Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hrad]; simp [Fintype.card_fun]
    have hmem : (fun k => decide (k = i.1)) ∈
        Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false) := by
      rw [hRad_univ]; exact Finset.mem_univ _
    have hf := (Finset.mem_filter.mp hmem).2 (fun k => decide (k = j.1))
    rw [hpol_true] at hf
    exact Bool.noConfusion hf
  have hrb := lane_rank_bound m s q hq lane hs hrad
  have h89 : (9 : ℤ) * 8 ^ s ≤ 8 * 9 ^ s := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    conv_rhs => rw [this, pow_succ]
    have hle : (8 ^ (s - 1) : ℤ) ≤ 9 ^ (s - 1) := by
      exact_mod_cast Nat.pow_le_pow_left (by omega : 8 ≤ 9) (s - 1)
    nlinarith
  have hstep : (9 ^ s : ℤ) * (9 * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|) ≤
      (9 ^ s : ℤ) * (8 * 6 ^ m) := by
    calc (9 ^ s : ℤ) * (9 * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|)
        = 9 * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|) := by ring
      _ ≤ 9 * (8 ^ s * 6 ^ m) := mul_le_mul_of_nonneg_left hrb (by norm_num)
      _ = (9 * 8 ^ s) * 6 ^ m := by ring
      _ ≤ (8 * 9 ^ s) * 6 ^ m := mul_le_mul_of_nonneg_right h89 (by positivity)
      _ = 9 ^ s * (8 * 6 ^ m) := by ring
  exact le_of_mul_le_mul_left hstep (by positivity)

def evalQuad3 (c0 l0 l1 l2 q01 q02 q12 : Bool) (b0 b1 b2 : Bool) : Bool :=
  xor (xor c0 (xor (l0 && b0) (xor (l1 && b1) (l2 && b2))))
      (xor (q01 && b0 && b1) (xor (q02 && b0 && b2) (q12 && b1 && b2)))

theorem evalQuad3_check : ∀ c0 l0 l1 l2 q01 q02 q12 : Bool,
    let S : ℤ := ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool,
      sgn (xor (b0 && b1 && b2) (evalQuad3 c0 l0 l1 l2 q01 q02 q12 b0 b1 b2))
    |S| ≤ 6 ∧ (|S| = 6 →
      ∃ c p0 p1 p2 : Bool, ∀ b0 b1 b2 : Bool,
        evalQuad3 c0 l0 l1 l2 q01 q02 q12 b0 b1 b2 =
          xor (b0 && b1 && b2) (xor c (decide (b0 = p0 ∧ b1 = p1 ∧ b2 = p2)))) := by
  decide

theorem single_triple_quad_bound (b0 : Bool) (l0 : Fin 3 → Bool) (a0 : Fin 3 → Fin 3 → Bool) :
    let g := quadFormGen b0 l0 a0
    |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (g x))| ≤ 6 ∧
    (|∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (g x))| = 6 →
      ∃ (c : Bool) (pt : Fin 3 → Bool), ∀ x : Fin 3 → Bool,
        g x = xor (x 0 && x 1 && x 2) (xor c (decide (x = pt)))) := by
  intro g
  let c0 := b0
  let k0 := xor (l0 0) (a0 0 0)
  let k1 := xor (l0 1) (a0 1 1)
  let k2 := xor (l0 2) (a0 2 2)
  let q01 := xor (a0 0 1) (a0 1 0)
  let q02 := xor (a0 0 2) (a0 2 0)
  let q12 := xor (a0 1 2) (a0 2 1)
  have hgeq : ∀ x : Fin 3 → Bool, g x = evalQuad3 c0 k0 k1 k2 q01 q02 q12 (x 0) (x 1) (x 2) := by
    intro x
    dsimp only [g, quadFormGen, linGen, evalQuad3, c0, k0, k1, k2, q01, q02, q12]
    simp only [Fin.sum_univ_three, par_add, par_toNat]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> simp only [Bool.and_false, Bool.and_true,
      Bool.false_and, Bool.true_and, Bool.xor_false, Bool.false_xor]
    all_goals
      try rfl
    · cases b0 <;> cases l0 2 <;> cases a0 2 2 <;> rfl
    · cases b0 <;> cases l0 1 <;> cases a0 1 1 <;> rfl
    · cases b0 <;> cases l0 1 <;> cases l0 2 <;> cases a0 1 1 <;> cases a0 1 2 <;>
        cases a0 2 1 <;> cases a0 2 2 <;> rfl
    · cases b0 <;> cases l0 0 <;> cases a0 0 0 <;> rfl
    · cases b0 <;> cases l0 0 <;> cases l0 2 <;> cases a0 0 0 <;> cases a0 0 2 <;>
        cases a0 2 0 <;> cases a0 2 2 <;> rfl
    · cases b0 <;> cases l0 0 <;> cases l0 1 <;> cases a0 0 0 <;> cases a0 0 1 <;>
        cases a0 1 0 <;> cases a0 1 1 <;> rfl
    · simp only [Bool.xor_assoc]
      have hcomm : ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Bool,
          xor x1 (xor x2 (xor x3 (xor x4 (xor x5 (xor x6 (xor x7 (xor x8 (xor x9 (xor x10 (xor x11 x12)))))))))) =
          xor x1 (xor x4 (xor x2 (xor x8 (xor x3 (xor x12 (xor x5 (xor x7 (xor x6 (xor x10 (xor x9 x11)))))))))) := by
        decide
      exact congrArg (xor b0) (hcomm (l0 0) (l0 1) (l0 2) (a0 0 0) (a0 0 1) (a0 0 2)
        (a0 1 0) (a0 1 1) (a0 1 2) (a0 2 0) (a0 2 1) (a0 2 2))
  let eq3 : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun p i => match i.val with | 0 => p.1 | 1 => p.2.1 | _ => p.2.2
      left_inv := fun x => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hsum_eq : (∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (g x))) =
      ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool,
        sgn (xor (b0 && b1 && b2) (evalQuad3 c0 k0 k1 k2 q01 q02 q12 b0 b1 b2)) := by
    trans (∑ p : Bool × Bool × Bool,
      sgn (xor (p.1 && p.2.1 && p.2.2) (evalQuad3 c0 k0 k1 k2 q01 q02 q12 p.1 p.2.1 p.2.2)))
    · refine Fintype.sum_equiv eq3 _ _ fun x => ?_
      rw [hgeq x]; rfl
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b0 _ => Fintype.sum_prod_type _
  rw [hsum_eq]
  obtain ⟨hle, heq_imp⟩ := evalQuad3_check c0 k0 k1 k2 q01 q02 q12
  refine ⟨hle, fun h6 => ?_⟩
  obtain ⟨c, p0, p1, p2, hpt⟩ := heq_imp h6
  let pt : Fin 3 → Bool := fun i => match i.val with | 0 => p0 | 1 => p1 | _ => p2
  refine ⟨c, pt, fun x => ?_⟩
  rw [hgeq x, hpt (x 0) (x 1) (x 2)]
  congr 2
  have hdec : (x 0 = p0 ∧ x 1 = p1 ∧ x 2 = p2) ↔ x = pt := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      funext i; fin_cases i <;> simp [pt, h0, h1, h2]
    · rintro rfl; simp [pt]
  simp [hdec]

theorem gap_eq_six_pow_iff (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat))) :
    (|∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| = 6 ^ m) ↔
      ∃ (constant : Bool) (point : Fin m → Fin 3 → Bool), ∀ w,
        q w = xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat))
          (xor constant (par (∑ i : Fin m, (decide (w i = point i)).toNat))) := by
  constructor
  · intro heq
    obtain ⟨b0, l0, a0, hqeq⟩ := hq
    have hno_cross : ∀ p₁ p₂ : Fin m × Fin 3, p₁.1 ≠ p₂.1 → a0 p₁ p₂ = a0 p₂ p₁ := by
      intro p₁ p₂ hne
      by_contra hdiff
      have hxt : xor (a0 p₁ p₂) (a0 p₂ p₁) = true := by
        cases h1 : a0 p₁ p₂ <;> cases h2 : a0 p₂ p₁ <;> simp_all
      have hb := cross_gap_bound m q b0 l0 a0 hqeq p₁ p₂ hne hxt
      rw [heq] at hb
      have hpos : (0 : ℤ) < 6 ^ m := by positivity
      linarith
    let qi : Fin m → (Fin 3 → Bool) → Bool := fun i x =>
      quadFormGen false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂)) x
    have hq_split : ∀ w : Fin m → Fin 3 → Bool,
        q w = xor b0 (par (∑ i : Fin m, (qi i (w i)).toNat)) := by
      intro w
      rw [hqeq w]
      have hlin_split : par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat) =
          par (∑ i : Fin m, (linGen (fun k => l0 (i, k)) (w i)).toNat) := by
        rw [Fintype.sum_prod_type]
        refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
        unfold linGen par
        have hm : (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 0 ∨
            (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 1 := by omega
        rcases hm with hm | hm <;> simp [hm]
      have hquad_split : par (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
          (a0 p₁ p₂ && w p₁.1 p₁.2 && w p₂.1 p₂.2).toNat) =
          par (∑ i : Fin m, (par (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
            (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat)).toNat) := by
        have hpair : (∑ p₁ : Fin m × Fin 3, ∑ p₂ : Fin m × Fin 3,
            (a0 p₁ p₂ && w p₁.1 p₁.2 && w p₂.1 p₂.2).toNat) =
            ∑ p : (Fin m × Fin 3) × (Fin m × Fin 3),
              (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat :=
          (Fintype.sum_prod_type (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) =>
            (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat)).symm
        rw [hpair]
        let F : (Fin m × Fin 3) × (Fin m × Fin 3) → ℕ :=
          fun p => (a0 p.1 p.2 && w p.1.1 p.1.2 && w p.2.1 p.2.2).toNat
        have hpart : ∑ p : (Fin m × Fin 3) × (Fin m × Fin 3), F p =
            (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 = p.2.1), F p) +
            (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 < p.2.1), F p) +
            (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.2.1 < p.1.1), F p) := by
          rw [← Finset.sum_union, ← Finset.sum_union]
          · congr 1
            ext p
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            rcases lt_trichotomy p.1.1 p.2.1 with h | h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
            rcases hp1 with h | h <;> omega
          · rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
            omega
        have hlt_gt : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.2.1 < p.1.1), F p) =
            ∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 < p.2.1), F p := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
          · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p₁ _ p₂ _ h; exact Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
          · intro p hp
            refine ⟨(p.2, p.1), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p hp
            have hne : p.1.1 ≠ p.2.1 := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; omega
            dsimp only [F]
            rw [hno_cross p.1 p.2 hne]
            congr 1
            cases a0 p.2 p.1 <;> cases w p.1.1 p.1.2 <;> cases w p.2.1 p.2.2 <;> rfl
        have hdiag : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 = p.2.1), F p) =
            ∑ i : Fin m, ∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat := by
          rw [Finset.sum_filter]
          trans (∑ i : Fin m, ∑ k₁ : Fin 3, ∑ p₂ : Fin m × Fin 3,
              if i = p₂.1 then F ((i, k₁), p₂) else 0)
          · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
          · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k₁ _ => ?_
            rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
            · simp [F]
            · intro j _ hne
              refine Finset.sum_eq_zero fun k₂ _ => by simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
        rw [hpart, hlt_gt, hdiag]
        have heven : ∀ a b : ℕ, par (a + b + b) = par a := fun a b => by
          have : (a + b + b) % 2 = a % 2 := by omega
          simp [par, this]
        rw [heven]
        refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
        unfold par
        have hm : (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 0 ∨
            (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 1 := by omega
        rcases hm with hm | hm <;> simp [hm]
      rw [hlin_split, hquad_split]
      have hcomb : xor (xor b0 (par (∑ i : Fin m, (linGen (fun k => l0 (i, k)) (w i)).toNat)))
          (par (∑ i : Fin m, (par (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
            (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat)).toNat)) =
          xor b0 (par (∑ i : Fin m, (qi i (w i)).toNat)) := by
        rw [Bool.xor_assoc, ← par_sum_xor]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [qi, quadFormGen]
        simp
      exact hcomb
    have hprod : |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| =
        ∏ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| := by
      have h1 : ∀ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w)) =
          sgn b0 * ∏ i : Fin m, sgn (xor (w i 0 && w i 1 && w i 2) (qi i (w i))) := fun w => by
        rw [hq_split w, ← sgn_par_sum, ← sgn_xor, par_sum_xor]
        congr 1
        cases par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) <;>
          cases b0 <;> cases par (∑ i : Fin m, (qi i (w i)).toNat) <;> rfl
      simp_rw [h1, ← Finset.mul_sum, abs_mul, sgn_abs, one_mul]
      rw [sum_prod_fin_fun (fun i x => sgn (xor (x 0 && x 1 && x 2) (qi i x))), abs_prod_eq_prod_abs]
    rw [hprod] at heq
    have hle_each : ∀ i : Fin m,
        |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| ≤ 6 := fun i =>
      (single_triple_quad_bound false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂))).1
    have heq_each : ∀ i : Fin m,
        |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| = 6 := by
      intro i
      by_contra hne
      have hlt : |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| < 6 :=
        lt_of_le_of_ne (hle_each i) hne
      have hprod_lt : (∏ j : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|) <
          ∏ _j : Fin m, (6 : ℤ) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
            ← Finset.mul_prod_erase Finset.univ (fun _ => (6 : ℤ)) (Finset.mem_univ i)]
        have hrest_le : (∏ j ∈ Finset.univ.erase i,
            |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|) ≤
            ∏ _j ∈ Finset.univ.erase i, (6 : ℤ) :=
          prod_le_prod_nonneg _ _ _ (fun j _ => abs_nonneg _) (fun j _ => hle_each j)
        have hrest_pos : (0 : ℤ) < ∏ _j ∈ Finset.univ.erase i, (6 : ℤ) := by
          rw [Finset.prod_const]; positivity
        calc |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| *
                ∏ j ∈ Finset.univ.erase i,
                  |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|
            ≤ |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| *
                ∏ _j ∈ Finset.univ.erase i, (6 : ℤ) :=
              mul_le_mul_of_nonneg_left hrest_le (abs_nonneg _)
          _ < 6 * ∏ _j ∈ Finset.univ.erase i, (6 : ℤ) :=
              mul_lt_mul_of_pos_right hlt hrest_pos
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod_lt
      omega
    have hex : ∀ i : Fin m, ∃ (c : Bool) (pt : Fin 3 → Bool), ∀ x : Fin 3 → Bool,
        qi i x = xor (x 0 && x 1 && x 2) (xor c (decide (x = pt))) := fun i =>
      (single_triple_quad_bound false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂))).2 (heq_each i)
    choose ci pti hpti using hex
    refine ⟨xor b0 (par (∑ i : Fin m, (ci i).toNat)), pti, fun w => ?_⟩
    rw [hq_split w]
    simp_rw [hpti]
    rw [par_sum_xor, par_sum_xor]
    cases b0 <;> cases par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) <;>
      cases par (∑ i : Fin m, (ci i).toNat) <;>
      cases par (∑ i : Fin m, (decide (w i = pti i)).toNat) <;> rfl
  · rintro ⟨constant, point, hqeq⟩
    have hsum : (∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
        sgn constant * ∏ i : Fin m, ∑ x : Fin 3 → Bool, sgn (decide (x = point i)) := by
      have h1 : ∀ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w)) =
          sgn constant * ∏ i : Fin m, sgn (decide (w i = point i)) := fun w => by
        rw [hqeq w, ← sgn_par_sum, ← sgn_xor]
        congr 1
        cases par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) <;>
          cases constant <;> cases par (∑ i : Fin m, (decide (w i = point i)).toNat) <;> rfl
      simp_rw [h1, ← Finset.mul_sum]
      congr 1
      exact sum_prod_fin_fun (fun i x => sgn (decide (x = point i)))
    have h6 : ∀ pt : Fin 3 → Bool, (∑ x : Fin 3 → Bool, sgn (decide (x = pt))) = 6 := by
      intro pt
      have hpt : ∀ x : Fin 3 → Bool, sgn (decide (x = pt)) = 1 - if x = pt then (2 : ℤ) else 0 := fun x => by
        by_cases h : x = pt <;> simp [h, sgn]
      simp only [hpt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
      norm_num
    rw [hsum]
    simp_rw [h6]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_mul, sgn_abs, one_mul, abs_of_nonneg]
    positivity

theorem two_bit_quad_exact (c a0 a1 : Bool) :
    (∑ z : Fin 2 → Bool, sgn (xor (z 0 && z 1) (xor c (xor (a0 && z 0) (a1 && z 1))))) =
      2 * sgn (xor c (a0 && a1)) := by
  cases c <;> cases a0 <;> cases a1 <;> decide

theorem par_sum_indep_four (F : (Fin 2 → Fin 2 → Bool) → Bool)
    (p₀ : Fin 2 × Fin 2)
    (hind : ∀ u : Fin 2 → Fin 2 → Bool,
      F (fun i k => xor (u i k) (decide ((i, k) = p₀))) = F u) :
    par (∑ u : Fin 2 → Fin 2 → Bool, (F u).toNat) = false := by
  let fl : (Fin 2 → Fin 2 → Bool) → (Fin 2 → Fin 2 → Bool) :=
    fun u i k => xor (u i k) (decide ((i, k) = p₀))
  let S0 : Finset (Fin 2 → Fin 2 → Bool) := Finset.univ.filter (fun u => u p₀.1 p₀.2 = false)
  let S1 : Finset (Fin 2 → Fin 2 → Bool) := Finset.univ.filter (fun u => u p₀.1 p₀.2 = true)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro u hu0 hu1
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hu0 hu1
    rw [hu0] at hu1; exact Bool.noConfusion hu1
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext u; simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases u p₀.1 p₀.2 <;> simp
  have hbij : (∑ u ∈ S1, (F u).toNat) = ∑ u ∈ S0, (F u).toNat := by
    refine Finset.sum_bij (fun u _ => fl u) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      simp [fl, hu]
    · intro a _ b _ hab
      funext i k
      have := congrFun (congrFun hab i) k
      dsimp only [fl] at this
      revert this; cases a i k <;> cases b i k <;> cases decide ((i, k) = p₀) <;> simp
    · intro u hu
      refine ⟨fl u, ?_, ?_⟩
      · simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        simp [fl, hu]
      · funext i k; dsimp only [fl]; cases u i k <;> cases decide ((i, k) = p₀) <;> rfl
    · intro u _; exact (hind u).symm ▸ rfl
  rw [← hunion, Finset.sum_union hdisj, hbij, par_add]
  cases par (∑ u ∈ S0, (F u).toNat) <;> rfl

theorem par_sum_monom3_false (c : Bool) (p₁ p₂ p₃ : Fin 2 × Fin 2) :
    par (∑ u : Fin 2 → Fin 2 → Bool, (c && u p₁.1 p₁.2 && u p₂.1 p₂.2 && u p₃.1 p₃.2).toNat) = false := by
  have hex : ∃ p₀ : Fin 2 × Fin 2, p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₀ ≠ p₃ := by
    have hcard : ({p₁, p₂, p₃} : Finset (Fin 2 × Fin 2)).card ≤ 3 := by
      calc ({p₁, p₂, p₃} : Finset (Fin 2 × Fin 2)).card
          ≤ ({p₂, p₃} : Finset (Fin 2 × Fin 2)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({p₃} : Finset (Fin 2 × Fin 2)).card + 1 + 1 := by
            have := Finset.card_insert_le p₂ ({p₃} : Finset (Fin 2 × Fin 2)); omega
        _ = 3 := by simp
    have hlt : ({p₁, p₂, p₃} : Finset (Fin 2 × Fin 2)).card < (Finset.univ : Finset (Fin 2 × Fin 2)).card := by
      have : (Finset.univ : Finset (Fin 2 × Fin 2)).card = 4 := by decide
      omega
    obtain ⟨p₀, _, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact ⟨p₀, hnot.1, hnot.2.1, hnot.2.2⟩
  obtain ⟨p₀, h1, h2, h3⟩ := hex
  refine par_sum_indep_four _ p₀ fun u => ?_
  have e1 : decide (p₁ = p₀) = false := by simp [h1.symm]
  have e2 : decide (p₂ = p₀) = false := by simp [h2.symm]
  have e3 : decide (p₃ = p₀) = false := by simp [h3.symm]
  simp [e1, e2, e3]

theorem bool_xor_m2 : ∀ z0 z1 c r0 r1 u0 u1 v0 v1 : Bool,
    xor (xor (z0 && z1) (xor c (xor (r0 && z0) (r1 && z1))))
        (xor (xor u0 v0 && z0) (xor u1 v1 && z1)) =
    xor (z0 && z1) (xor c (xor (xor u0 (xor r0 v0) && z0) (xor u1 (xor r1 v1) && z1))) := by
  decide

theorem xor_reassoc5 : ∀ a b c d e : Bool,
    xor (xor (xor (xor a b) c) d) e = xor (xor a (xor d e)) (xor b c) := by
  decide

theorem cross_m2_par_prod (lane : Fin 2 → Fin 3)
    (Bcoeff : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Bool) (r0 r1 : Bool) :
    let uVec : (Fin 2 → Fin 2 → Bool) → (Fin 2 × Fin 3) → Bool :=
      fun u p => mergeLane lane u (fun _ => false) p.1 p.2
    let ν : (Fin 2 → Fin 2 → Bool) → Fin 2 → Bool := fun u k =>
      par (∑ p : Fin 2 × Fin 3, (Bcoeff p (k, lane k) && uVec u p).toNat)
    par (∑ u : Fin 2 → Fin 2 → Bool,
      (xor (u 0 0 && u 0 1) (xor r0 (ν u 0)) && xor (u 1 0 && u 1 1) (xor r1 (ν u 1))).toNat) = true := by
  intro uVec ν
  let A0 : (Fin 2 → Fin 2 → Bool) → Bool := fun u => xor r0 (ν u 0)
  let A1 : (Fin 2 → Fin 2 → Bool) → Bool := fun u => xor r1 (ν u 1)
  have hcoord : ∀ (p : Fin 2 × Fin 3),
      (∃ q : Fin 2 × Fin 2, ∀ u, uVec u p = u q.1 q.2) ∨ (∀ u, uVec u p = false) := by
    intro ⟨k, l⟩
    by_cases h1 : l = lane k
    · right; intro u; simp [uVec, mergeLane, h1]
    · by_cases h2 : l = otherIdx (lane k) 0
      · left; exact ⟨(k, 0), fun u => by dsimp only [uVec, mergeLane]; rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_left_iff.mpr (fun h => absurd h2 h)]⟩
      · left; exact ⟨(k, 1), fun u => by dsimp only [uVec, mergeLane]; rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2)]⟩
  have hexp : ∀ u : Fin 2 → Fin 2 → Bool,
      (xor (u 0 0 && u 0 1) (A0 u) && xor (u 1 0 && u 1 1) (A1 u)) =
      xor (xor (u 0 0 && u 0 1 && u 1 0 && u 1 1)
               ((u 0 0 && u 0 1) && A1 u))
          (xor (A0 u && (u 1 0 && u 1 1))
               (A0 u && A1 u)) := fun u => by
    cases u 0 0 <;> cases u 0 1 <;> cases u 1 0 <;> cases u 1 1 <;> cases A0 u <;> cases A1 u <;> rfl
  change par (∑ u : Fin 2 → Fin 2 → Bool,
    (xor (u 0 0 && u 0 1) (A0 u) && xor (u 1 0 && u 1 1) (A1 u)).toNat) = true
  simp_rw [hexp]
  rw [par_sum_xor, par_sum_xor, par_sum_xor]
  have hdeg4 : par (∑ u : Fin 2 → Fin 2 → Bool, (u 0 0 && u 0 1 && u 1 0 && u 1 1).toNat) = true := by
    have h1 : (∑ u : Fin 2 → Fin 2 → Bool, (u 0 0 && u 0 1 && u 1 0 && u 1 1).toNat) = 1 := by
      rw [Finset.sum_eq_single (fun _ _ => true)]
      · rfl
      · intro u _ hne
        have hex : ∃ i k, u i k = false := by
          by_contra hall
          push Not at hall
          apply hne
          funext i k
          cases h : u i k
          · exact absurd h (hall i k)
          · rfl
        obtain ⟨i, k, hik⟩ := hex
        fin_cases i <;> fin_cases k <;> simp at hik <;> simp [hik]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1]; rfl
  have hterm_pair : ∀ (p₁ p₂ : Fin 2 × Fin 2) (k : Fin 2) (rk : Bool),
      par (∑ u : Fin 2 → Fin 2 → Bool,
        ((u p₁.1 p₁.2 && u p₂.1 p₂.2) && xor rk (ν u k)).toNat) = false := by
    intro p₁ p₂ k rk
    have hpt : ∀ u : Fin 2 → Fin 2 → Bool,
        ((u p₁.1 p₁.2 && u p₂.1 p₂.2) && xor rk (ν u k)) =
        xor (rk && u p₁.1 p₁.2 && u p₂.1 p₂.2)
            (par (∑ p : Fin 2 × Fin 3,
              (Bcoeff p (k, lane k) && uVec u p && u p₁.1 p₁.2 && u p₂.1 p₂.2).toNat)) := by
      intro u
      have hmul_par : ∀ (b : Bool) (s : Finset (Fin 2 × Fin 3)) (f : Fin 2 × Fin 3 → Bool),
          (b && par (∑ p ∈ s, (f p).toNat)) = par (∑ p ∈ s, (f p && b).toNat) := by
        intro b s f
        cases b
        · simp [par]
        · simp
      have h1 : ((u p₁.1 p₁.2 && u p₂.1 p₂.2) && xor rk (ν u k)) =
          xor (rk && u p₁.1 p₁.2 && u p₂.1 p₂.2) ((u p₁.1 p₁.2 && u p₂.1 p₂.2) && ν u k) := by
        cases u p₁.1 p₁.2 <;> cases u p₂.1 p₂.2 <;> cases rk <;> cases ν u k <;> rfl
      rw [h1]
      have h2 : ((u p₁.1 p₁.2 && u p₂.1 p₂.2) && ν u k) =
          par (∑ p : Fin 2 × Fin 3,
            (Bcoeff p (k, lane k) && uVec u p && u p₁.1 p₁.2 && u p₂.1 p₂.2).toNat) := by
        dsimp only [ν]
        rw [hmul_par]
        exact congrArg par (Finset.sum_congr rfl fun p _ =>
          congrArg Bool.toNat (by simp only [Bool.and_assoc]))
      rw [h2]
    simp_rw [hpt]
    rw [par_sum_xor]
    have hfirst : par (∑ u : Fin 2 → Fin 2 → Bool, (rk && u p₁.1 p₁.2 && u p₂.1 p₂.2).toNat) = false := by
      have := par_sum_monom3_false rk p₁ p₂ p₂
      simpa [Bool.and_assoc, Bool.and_self] using this
    have hsecond : par (∑ u : Fin 2 → Fin 2 → Bool,
        (par (∑ p : Fin 2 × Fin 3,
          (Bcoeff p (k, lane k) && uVec u p && u p₁.1 p₁.2 && u p₂.1 p₂.2).toNat)).toNat) = false := by
      rw [par_sum_par_comm (fun u p => Bcoeff p (k, lane k) && uVec u p && u p₁.1 p₁.2 && u p₂.1 p₂.2)]
      have hzero : ∀ p : Fin 2 × Fin 3,
          par (∑ u : Fin 2 → Fin 2 → Bool,
            (Bcoeff p (k, lane k) && uVec u p && u p₁.1 p₁.2 && u p₂.1 p₂.2).toNat) = false := fun p => by
        rcases hcoord p with ⟨q0, hq0⟩ | hf0
        · simp_rw [hq0]; exact par_sum_monom3_false (Bcoeff p (k, lane k)) q0 p₁ p₂
        · simp_rw [hf0]; simp [par]
      simp_rw [hzero]; simp [par]
    rw [hfirst, hsecond]; rfl
  have hA0A1 : par (∑ u : Fin 2 → Fin 2 → Bool, (A0 u && A1 u).toNat) = false := by
    have hpt : ∀ u : Fin 2 → Fin 2 → Bool,
        (A0 u && A1 u) =
        xor (xor (r0 && r1)
                 (par (∑ p : Fin 2 × Fin 3, (r0 && Bcoeff p (1, lane 1) && uVec u p).toNat)))
            (xor (par (∑ p : Fin 2 × Fin 3, (r1 && Bcoeff p (0, lane 0) && uVec u p).toNat))
                 (par (∑ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
                   (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2).toNat))) := by
      intro u
      dsimp only [A0, A1, ν]
      have hmul_and : ∀ (a b : ℕ), (par a && par b) = par (a * b) := fun a b => by
        unfold par
        have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.mul_mod, ha, hb]
      have hprod_sum : (∑ p₁ : Fin 2 × Fin 3, (Bcoeff p₁ (0, lane 0) && uVec u p₁).toNat) *
          (∑ p₂ : Fin 2 × Fin 3, (Bcoeff p₂ (1, lane 1) && uVec u p₂).toNat) =
          ∑ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
            (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2).toNat := by
        rw [Finset.sum_mul, Fintype.sum_prod_type (fun p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3) =>
          (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2).toNat)]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        cases Bcoeff p₁ (0, lane 0) <;> cases uVec u p₁ <;>
          cases Bcoeff p₂ (1, lane 1) <;> cases uVec u p₂ <;> rfl
      have hmul_b : ∀ (c : Bool) (f : Fin 2 × Fin 3 → Bool),
          (c && par (∑ p : Fin 2 × Fin 3, (f p).toNat)) =
          par (∑ p : Fin 2 × Fin 3, (c && f p).toNat) := fun c f => by
        cases c <;> simp [par]
      have h1 : (xor r0 (par (∑ p : Fin 2 × Fin 3, (Bcoeff p (0, lane 0) && uVec u p).toNat)) &&
          xor r1 (par (∑ p : Fin 2 × Fin 3, (Bcoeff p (1, lane 1) && uVec u p).toNat))) =
          xor (xor (r0 && r1)
                   (r0 && par (∑ p : Fin 2 × Fin 3, (Bcoeff p (1, lane 1) && uVec u p).toNat)))
              (xor (r1 && par (∑ p : Fin 2 × Fin 3, (Bcoeff p (0, lane 0) && uVec u p).toNat))
                   (par (∑ p : Fin 2 × Fin 3, (Bcoeff p (0, lane 0) && uVec u p).toNat) &&
                    par (∑ p : Fin 2 × Fin 3, (Bcoeff p (1, lane 1) && uVec u p).toNat))) := by
        cases r0 <;> cases r1 <;>
          cases par (∑ p : Fin 2 × Fin 3, (Bcoeff p (0, lane 0) && uVec u p).toNat) <;>
          cases par (∑ p : Fin 2 × Fin 3, (Bcoeff p (1, lane 1) && uVec u p).toNat) <;> rfl
      rw [h1, hmul_b, hmul_b, hmul_and, hprod_sum]
      simp only [Bool.and_assoc]
    simp_rw [hpt]
    rw [par_sum_xor, par_sum_xor, par_sum_xor]
    have h00 : par (∑ _u : Fin 2 → Fin 2 → Bool, (r0 && r1).toNat) = false :=
      par_sum_indep_four (fun _ => r0 && r1) (0, 0) (fun _ => rfl)
    have hlin_gen : ∀ (c : Fin 2 × Fin 3 → Bool),
        par (∑ u : Fin 2 → Fin 2 → Bool,
          (par (∑ p : Fin 2 × Fin 3, (c p && uVec u p).toNat)).toNat) = false := by
      intro c
      rw [par_sum_par_comm (fun u p => c p && uVec u p)]
      have hz : ∀ p : Fin 2 × Fin 3, par (∑ u : Fin 2 → Fin 2 → Bool, (c p && uVec u p).toNat) = false := fun p => by
        rcases hcoord p with ⟨q0, hq0⟩ | hf0
        · simp_rw [hq0]
          have := par_sum_monom3_false (c p) q0 q0 q0
          simpa [Bool.and_assoc, Bool.and_self] using this
        · simp_rw [hf0]; simp [par]
      simp_rw [hz]; simp [par]
    have hquad_gen : par (∑ u : Fin 2 → Fin 2 → Bool,
        (par (∑ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
          (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2).toNat)).toNat) = false := by
      rw [par_sum_par_comm (fun u (p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3)) =>
        Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2)]
      have hz : ∀ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
          par (∑ u : Fin 2 → Fin 2 → Bool,
            (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1) && uVec u p.1 && uVec u p.2).toNat) = false := fun p => by
        rcases hcoord p.1 with ⟨q1, hq1⟩ | hf1
        · rcases hcoord p.2 with ⟨q2, hq2⟩ | hf2
          · simp_rw [hq1, hq2]
            have := par_sum_monom3_false (Bcoeff p.1 (0, lane 0) && Bcoeff p.2 (1, lane 1)) q1 q2 q2
            simpa [Bool.and_assoc, Bool.and_self] using this
          · simp_rw [hf2]; simp [par]
        · simp_rw [hf1]; simp [par]
      simp_rw [hz]; simp [par]
    rw [h00, hlin_gen (fun p => r0 && Bcoeff p (1, lane 1)),
        hlin_gen (fun p => r1 && Bcoeff p (0, lane 0)), hquad_gen]
    rfl
  have ht1 : par (∑ u : Fin 2 → Fin 2 → Bool, ((u 0 0 && u 0 1) && A1 u).toNat) = false :=
    hterm_pair (0, 0) (0, 1) 1 r1
  have ht2 : par (∑ u : Fin 2 → Fin 2 → Bool, (A0 u && (u 1 0 && u 1 1)).toNat) = false := by
    have : ∀ u, (A0 u && (u 1 0 && u 1 1)) = ((u 1 0 && u 1 1) && A0 u) := fun u => Bool.and_comm _ _
    simp_rw [this]
    exact hterm_pair (1, 0) (1, 1) 0 r0
  rw [hdeg4, ht1, ht2, hA0A1]; rfl

theorem cross_m2_bound (q : (Fin 2 → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin 2 × Fin 3) → Bool) (a0 : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin 2 × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin 2 × Fin 3, ∑ j : Fin 2 × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (i j : Fin 2 × Fin 3) (hij : i.1 ≠ j.1) (hcross : xor (a0 i j) (a0 j i) = true) :
    |∑ w : Fin 2 → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin 2, (w k 0 && w k 1 && w k 2).toNat)) (q w))| ≤ 28 := by
  let lane : Fin 2 → Fin 3 := fun k => if k = i.1 then i.2 else j.2
  have hlane_i : lane i.1 = i.2 := by simp [lane]
  have hlane_j : lane j.1 = j.2 := by simp [lane, hij.symm]
  let R : (Fin 2 → Bool) → Bool := fun z => q (fun k l => (l == lane k) && z k)
  let uVec : (Fin 2 → Fin 2 → Bool) → (Fin 2 × Fin 3) → Bool :=
    fun u p => mergeLane lane u (fun _ => false) p.1 p.2
  let Bcoeff : (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  let ν : (Fin 2 → Fin 2 → Bool) → Fin 2 → Bool := fun u k =>
    par (∑ p : Fin 2 × Fin 3, (Bcoeff p (k, lane k) && uVec u p).toNat)
  have hsum_split := sum_split_lane 2 q b0 l0 a0 hqeq lane
  dsimp only at hsum_split
  let e0 : Fin 2 → Bool := fun k => decide (k = 0)
  let e1 : Fin 2 → Bool := fun k => decide (k = 1)
  have hpol01 : polar R e0 e1 = true := by
    let Qv : ((Fin 2 × Fin 3) → Bool) → Bool := fun v => q (fun h l => v (h, l))
    let ei : (Fin 2 × Fin 3) → Bool := fun p => decide (p = i)
    let ej : (Fin 2 × Fin 3) → Bool := fun p => decide (p = j)
    have hR1 : ∀ z : Fin 2 → Bool, R z = Qv (fun p => (p.2 == lane p.1) && z p.1) := fun _ => rfl
    have he_i : (fun p : Fin 2 × Fin 3 => (p.2 == lane p.1) && decide (p.1 = i.1)) = ei := by
      funext ⟨k, l⟩
      rcases i with ⟨i1, i2⟩
      by_cases hk : k = i1
      · subst hk; by_cases hl : l = i2
        · subst hl; simp [ei, hlane_i]
        · simp [ei, hlane_i, hl, beq_false_of_ne hl]
      · simp [ei, hk]
    have he_j : (fun p : Fin 2 × Fin 3 => (p.2 == lane p.1) && decide (p.1 = j.1)) = ej := by
      funext ⟨k, l⟩
      rcases j with ⟨j1, j2⟩
      by_cases hk : k = j1
      · subst hk; by_cases hl : l = j2
        · subst hl; simp [ej, hlane_j]
        · simp [ej, hlane_j, hl, beq_false_of_ne hl]
      · simp [ej, hk]
    have hpol_ij : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = true := by
      have he12 : (fun p : Fin 2 × Fin 3 => (p.2 == lane p.1) && xor (decide (p.1 = i.1)) (decide (p.1 = j.1))) =
          fun p => xor (ei p) (ej p) := by
        funext p
        have h1 := congrFun he_i p; have h2 := congrFun he_j p
        rw [← h1, ← h2]
        cases (p.2 == lane p.1) <;> cases decide (p.1 = i.1) <;> cases decide (p.1 = j.1) <;> rfl
      have he0 : (fun p : Fin 2 × Fin 3 => (p.2 == lane p.1) && false) = fun _ => false := by
        funext p; simp
      have hpeq : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = polar Qv ei ej := by
        unfold polar; rw [hR1, hR1, hR1, hR1, he_i, he_j, he12, he0]
      rw [hpeq]
      have hpeq2 : polar Qv ei ej = polar (quadFormGen b0 l0 a0) ei ej := by
        unfold polar Qv; simp only [hqeq]; rfl
      rw [hpeq2, polar_quadFormGen]
      have hsum : (∑ p₁ : Fin 2 × Fin 3, ∑ p₂ : Fin 2 × Fin 3,
          (xor (a0 p₁ p₂) (a0 p₂ p₁) && ei p₁ && ej p₂).toNat) = (xor (a0 i j) (a0 j i)).toNat := by
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single j]
          · simp [ei, ej]
          · intro p₂ _ hne; simp [ej, hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro p₁ _ hne
          refine Finset.sum_eq_zero fun p₂ _ => by simp [ei, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum, par_toNat, hcross]
    have hcases : (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) := by
      have hi := i.1.isLt; have hj := j.1.isLt
      rcases Fin.eq_zero_or_eq_succ i.1 with hi0 | ⟨i', hi1⟩
      · rcases Fin.eq_zero_or_eq_succ j.1 with hj0 | ⟨j', hj1⟩
        · exact absurd (hi0.trans hj0.symm) hij
        · left; exact ⟨hi0, by fin_cases j'; exact hj1⟩
      · rcases Fin.eq_zero_or_eq_succ j.1 with hj0 | ⟨j', hj1⟩
        · right; exact ⟨by fin_cases i'; exact hi1, hj0⟩
        · fin_cases i'; fin_cases j'; exact absurd (hi1.trans hj1.symm) hij
    rcases hcases with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · rw [hi0, hj1] at hpol_ij; exact hpol_ij
    · rw [hi1, hj0, polar_symm] at hpol_ij; exact hpol_ij
  let r0 : Bool := xor (R e0) (R (fun _ => false))
  let r1 : Bool := xor (R e1) (R (fun _ => false))
  have hR_form : ∀ z : Fin 2 → Bool,
      R z = xor (z 0 && z 1) (xor (R (fun _ => false)) (xor (r0 && z 0) (r1 && z 1))) := by
    intro z
    have h00 : (fun k : Fin 2 => false) = fun _ => false := rfl
    have h11 : (fun k : Fin 2 => xor (e0 k) (e1 k)) = fun _ => true := by
      funext k; fin_cases k <;> rfl
    cases hz0 : z 0 <;> cases hz1 : z 1
    · have hz : z = fun _ => false := by funext k; fin_cases k <;> assumption
      rw [hz]; simp
    · have hz : z = e1 := by funext k; fin_cases k <;> simp [e1, hz0, hz1]
      rw [hz]; simp only [e1, r1, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.xor_false, Bool.false_xor]
      cases R e1 <;> cases R (fun _ => false) <;> rfl
    · have hz : z = e0 := by funext k; fin_cases k <;> simp [e0, hz0, hz1]
      rw [hz]; simp only [e0, r0, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.xor_false, Bool.false_xor]
      cases R e0 <;> cases R (fun _ => false) <;> rfl
    · have hz : z = fun _ => true := by funext k; fin_cases k <;> assumption
      rw [hz]
      have hp := hpol01
      unfold polar at hp
      rw [h11] at hp
      simp only [r0, r1, Bool.and_true]
      revert hp
      cases R (fun _ => true) <;> cases R e0 <;> cases R e1 <;> cases R (fun _ => false) <;> decide
  let c0u : (Fin 2 → Fin 2 → Bool) → Bool := fun u =>
    xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))
  let A0 : (Fin 2 → Fin 2 → Bool) → Bool := fun u => xor r0 (ν u 0)
  let A1 : (Fin 2 → Fin 2 → Bool) → Bool := fun u => xor r1 (ν u 1)
  let g : (Fin 2 → Fin 2 → Bool) → Bool := fun u =>
    xor (xor (c0u u) (R (fun _ => false)))
        (xor (u 0 0 && u 0 1) (A0 u) && xor (u 1 0 && u 1 1) (A1 u))
  have hsum2 : (∑ w : Fin 2 → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin 2, (w k 0 && w k 1 && w k 2).toNat)) (q w))) =
      2 * ∑ u : Fin 2 → Fin 2 → Bool, sgn (g u) := by
    rw [hsum_split, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hinner : (∑ z : Fin 2 → Bool,
        sgn (xor (R z) (linGen (fun k => xor (u k 0 && u k 1) (ν u k)) z))) =
        2 * sgn (xor (R (fun _ => false))
          (xor (u 0 0 && u 0 1) (A0 u) && xor (u 1 0 && u 1 1) (A1 u))) := by
      have hpt : ∀ z : Fin 2 → Bool,
          xor (R z) (linGen (fun k => xor (u k 0 && u k 1) (ν u k)) z) =
          xor (z 0 && z 1) (xor (R (fun _ => false))
            (xor (xor (u 0 0 && u 0 1) (A0 u) && z 0)
                 (xor (u 1 0 && u 1 1) (A1 u) && z 1))) := by
        intro z
        rw [hR_form z]
        unfold linGen
        simp only [Fin.sum_univ_two, par_add, par_toNat]
        exact bool_xor_m2 (z 0) (z 1) (R (fun _ => false)) r0 r1
          (u 0 0 && u 0 1) (u 1 0 && u 1 1) (ν u 0) (ν u 1)
      simp_rw [hpt]
      exact two_bit_quad_exact _ _ _
    rw [hinner]
    dsimp only [g, c0u]
    simp only [sgn_xor]
    ring
  have hcoord : ∀ (p : Fin 2 × Fin 3),
      (∃ q : Fin 2 × Fin 2, ∀ u, uVec u p = u q.1 q.2) ∨ (∀ u, uVec u p = false) := by
    intro ⟨k, l⟩
    by_cases h1 : l = lane k
    · right; intro u; simp [uVec, mergeLane, h1]
    · by_cases h2 : l = otherIdx (lane k) 0
      · left; exact ⟨(k, 0), fun u => by dsimp only [uVec, mergeLane]; rw [if_neg h1, if_pos h2]⟩
      · left; exact ⟨(k, 1), fun u => by dsimp only [uVec, mergeLane]; rw [if_neg h1, if_neg h2]⟩
  have hpar_c0 : par (∑ u : Fin 2 → Fin 2 → Bool, (xor (c0u u) (R (fun _ => false))).toNat) = false := by
    have hconst : ∀ c : Bool, par (∑ _u : Fin 2 → Fin 2 → Bool, c.toNat) = false := fun c => by
      exact par_sum_indep_four (fun _ => c) (0, 0) (fun _ => rfl)
    have hq_expand : ∀ u : Fin 2 → Fin 2 → Bool,
        xor (c0u u) (R (fun _ => false)) =
        xor (xor b0 (xor (q (fun _ _ => false)) (R (fun _ => false))))
            (xor (par (∑ p : Fin 2 × Fin 3, (l0 p && uVec u p).toNat))
                 (par (∑ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
                    (a0 p.1 p.2 && uVec u p.1 && uVec u p.2).toNat))) := by
      intro u
      dsimp only [c0u]
      rw [hqeq (mergeLane lane u (fun _ => false)),
        Fintype.sum_prod_type (fun p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3) =>
          (a0 p.1 p.2 && uVec u p.1 && uVec u p.2).toNat)]
      exact xor_reassoc5 b0 _ _ _ _
    simp_rw [hq_expand]
    rw [par_sum_xor, hconst, par_sum_xor]
    have hlin_zero : par (∑ u : Fin 2 → Fin 2 → Bool,
        (par (∑ p : Fin 2 × Fin 3, (l0 p && uVec u p).toNat)).toNat) = false := by
      rw [par_sum_par_comm (fun u p => l0 p && uVec u p)]
      have hzero : ∀ p : Fin 2 × Fin 3,
          par (∑ u : Fin 2 → Fin 2 → Bool, (l0 p && uVec u p).toNat) = false := fun p => by
        rcases hcoord p with ⟨q0, hq0⟩ | hf0
        · simp_rw [hq0]
          have := par_sum_monom3_false (l0 p) q0 q0 q0
          simpa [Bool.and_assoc, Bool.and_self] using this
        · simp_rw [hf0]; simp [par]
      simp_rw [hzero]; simp [par]
    have hquad_zero : par (∑ u : Fin 2 → Fin 2 → Bool,
        (par (∑ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
          (a0 p.1 p.2 && uVec u p.1 && uVec u p.2).toNat)).toNat) = false := by
      rw [par_sum_par_comm (fun u (p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3)) =>
        a0 p.1 p.2 && uVec u p.1 && uVec u p.2)]
      have hzero : ∀ p : (Fin 2 × Fin 3) × (Fin 2 × Fin 3),
          par (∑ u : Fin 2 → Fin 2 → Bool,
            (a0 p.1 p.2 && uVec u p.1 && uVec u p.2).toNat) = false := fun p => by
        rcases hcoord p.1 with ⟨q1, hq1⟩ | hf1
        · rcases hcoord p.2 with ⟨q2, hq2⟩ | hf2
          · simp_rw [hq1, hq2]
            have := par_sum_monom3_false (a0 p.1 p.2) q1 q2 q2
            simpa [Bool.and_assoc, Bool.and_self] using this
          · simp_rw [hf2]; simp [par]
        · simp_rw [hf1]; simp [par]
      simp_rw [hzero]; simp [par]
    rw [hlin_zero, hquad_zero]; rfl
  have hpar_prod : par (∑ u : Fin 2 → Fin 2 → Bool,
      (xor (u 0 0 && u 0 1) (A0 u) && xor (u 1 0 && u 1 1) (A1 u)).toNat) = true :=
    cross_m2_par_prod lane Bcoeff r0 r1
  have hg_odd : par (∑ u : Fin 2 → Fin 2 → Bool, (g u).toNat) = true := by
    dsimp only [g]
    rw [par_sum_xor, hpar_c0, hpar_prod]
    rfl
  let k : ℕ := ∑ u : Fin 2 → Fin 2 → Bool, (g u).toNat
  have hk_odd : k % 2 = 1 := by
    have : (k % 2 == 1) = true := hg_odd
    simpa using this
  have hk_le : k ≤ 16 := by
    have : k ≤ ∑ _u : Fin 2 → Fin 2 → Bool, 1 := Finset.sum_le_sum fun u _ => by cases g u <;> decide
    have h16 : (∑ _u : Fin 2 → Fin 2 → Bool, 1) = 16 := by decide
    omega
  have hsum_g : (∑ u : Fin 2 → Fin 2 → Bool, sgn (g u)) = 16 - 2 * (k : ℤ) := by
    have hpt : ∀ u : Fin 2 → Fin 2 → Bool, sgn (g u) = 1 - 2 * ((g u).toNat : ℤ) := fun u => by
      cases g u <;> decide
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h16 : (∑ _u : Fin 2 → Fin 2 → Bool, (1 : ℤ)) = 16 := by decide
    rw [h16]
    dsimp only [k]
    push_cast
    rfl
  rw [hsum2, hsum_g, abs_mul]
  have habs2 : |(2 : ℤ)| = 2 := by norm_num
  rw [habs2]
  have h14 : |16 - 2 * (k : ℤ)| ≤ 14 := by
    rw [abs_le]
    omega
  linarith

theorem isQuadGen_const {ι : Type} [Fintype ι] (c : Bool) :
    IsQuadGen (fun _ : ι → Bool => c) :=
  ⟨c, fun _ => false, fun _ _ => false, fun _ => by simp [quadFormGen, linGen, par]⟩

theorem isQuadGen_lin {ι : Type} [Fintype ι] (l : ι → Bool) :
    IsQuadGen (linGen l) :=
  ⟨false, l, fun _ _ => false, fun _ => by simp [quadFormGen, par]⟩

theorem isQuadGen_xor {ι : Type} [Fintype ι] {f g : (ι → Bool) → Bool}
    (hf : IsQuadGen f) (hg : IsQuadGen g) :
    IsQuadGen (fun w => xor (f w) (g w)) := by
  obtain ⟨b1, l1, a1, hf⟩ := hf
  obtain ⟨b2, l2, a2, hg⟩ := hg
  refine ⟨xor b1 b2, fun j => xor (l1 j) (l2 j), fun i j => xor (a1 i j) (a2 i j), fun w => ?_⟩
  dsimp only
  rw [hf w, hg w]
  unfold quadFormGen linGen
  have hlin : par (∑ j : ι, (xor (l1 j) (l2 j) && w j).toNat) =
      xor (par (∑ j : ι, (l1 j && w j).toNat)) (par (∑ j : ι, (l2 j && w j).toNat)) := by
    have hpt : ∀ j, (xor (l1 j) (l2 j) && w j) = xor (l1 j && w j) (l2 j && w j) := fun j => by
      cases l1 j <;> cases l2 j <;> cases w j <;> rfl
    simp_rw [hpt]; exact par_sum_xor Finset.univ _ _
  have hq : par (∑ i : ι, ∑ j : ι, (xor (a1 i j) (a2 i j) && w i && w j).toNat) =
      xor (par (∑ i : ι, ∑ j : ι, (a1 i j && w i && w j).toNat))
          (par (∑ i : ι, ∑ j : ι, (a2 i j && w i && w j).toNat)) := by
    have hpair : ∀ F : ι → ι → Bool,
        par (∑ i : ι, ∑ j : ι, (F i j).toNat) = par (∑ p : ι × ι, (F p.1 p.2).toNat) := fun F => by
      rw [Fintype.sum_prod_type]
    rw [hpair, hpair, hpair]
    have hpt : ∀ p : ι × ι, (xor (a1 p.1 p.2) (a2 p.1 p.2) && w p.1 && w p.2) =
        xor (a1 p.1 p.2 && w p.1 && w p.2) (a2 p.1 p.2 && w p.1 && w p.2) := fun p => by
      cases a1 p.1 p.2 <;> cases a2 p.1 p.2 <;> cases w p.1 <;> cases w p.2 <;> rfl
    simp_rw [hpt]; exact par_sum_xor Finset.univ _ _
  rw [hlin, hq]
  cases b1 <;> cases b2 <;>
    cases par (∑ j : ι, (l1 j && w j).toNat) <;> cases par (∑ j : ι, (l2 j && w j).toNat) <;>
    cases par (∑ i : ι, ∑ j : ι, (a1 i j && w i && w j).toNat) <;>
    cases par (∑ i : ι, ∑ j : ι, (a2 i j && w i && w j).toNat) <;> rfl

theorem isQuadGen_and_const {ι : Type} [Fintype ι] (c : Bool) {f : (ι → Bool) → Bool}
    (hf : IsQuadGen f) : IsQuadGen (fun w => c && f w) := by
  cases c
  · simpa using isQuadGen_const false
  · simpa using hf

theorem isQuadGen_and_lin {ι : Type} [Fintype ι] (l1 l2 : ι → Bool) :
    IsQuadGen (fun w => linGen l1 w && linGen l2 w) := by
  refine ⟨false, fun _ => false, fun i j => l1 i && l2 j, fun w => ?_⟩
  unfold quadFormGen linGen
  simp only [Bool.false_and, Bool.toNat_false, Finset.sum_const_zero, par_zero, Bool.false_xor]
  have hmul : ∀ a b : ℕ, (par a && par b) = par (a * b) := fun a b => by
    unfold par
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.mul_mod, ha, hb]
  rw [hmul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases l1 i <;> cases w i <;> cases l2 j <;> cases w j <;> rfl

theorem isQuadGen_par_sum {ι α : Type} [Fintype ι] (s : Finset α) (F : α → (ι → Bool) → Bool)
    (hF : ∀ a ∈ s, IsQuadGen (F a)) :
    IsQuadGen (fun w => par (∑ a ∈ s, (F a w).toNat)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [par] using isQuadGen_const false
  | insert a s ha ih =>
    have hfa := hF a (Finset.mem_insert_self a s)
    have hrest := ih (fun x hx => hF x (Finset.mem_insert_of_mem hx))
    have heq : (fun w => par (∑ x ∈ insert a s, (F x w).toNat)) =
        fun w => xor (F a w) (par (∑ x ∈ s, (F x w).toNat)) := by
      funext w; rw [Finset.sum_insert ha, par_add, par_toNat]
    rw [heq]
    exact isQuadGen_xor hfa hrest

theorem isQuadGen_comp_affine {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {q : (ι₂ → Bool) → Bool} (hq : IsQuadGen q)
    (Φ : (ι₁ → Bool) → (ι₂ → Bool))
    (hΦ : ∀ j : ι₂, ∃ (c : Bool) (m : ι₁ → Bool), ∀ u, Φ u j = xor c (linGen m u)) :
    IsQuadGen (fun u => q (Φ u)) := by
  obtain ⟨b, l, a, hqeq⟩ := hq
  choose cΦ mΦ hmΦ using hΦ
  have h1 : ∀ u, q (Φ u) =
      xor (xor b (par (∑ j : ι₂, (l j && Φ u j).toNat)))
          (par (∑ p : ι₂ × ι₂, (a p.1 p.2 && Φ u p.1 && Φ u p.2).toNat)) := fun u => by
    rw [hqeq (Φ u)]
    unfold quadFormGen linGen
    rw [Fintype.sum_prod_type]
  simp_rw [h1]
  refine isQuadGen_xor (isQuadGen_xor (isQuadGen_const b) ?_) ?_
  · refine isQuadGen_par_sum Finset.univ (fun j u => l j && Φ u j) fun j _ => ?_
    have heq : (fun u => l j && Φ u j) = fun u => l j && xor (cΦ j) (linGen (mΦ j) u) := by
      funext u; rw [hmΦ j u]
    rw [heq]
    exact isQuadGen_and_const (l j) (isQuadGen_xor (isQuadGen_const (cΦ j)) (isQuadGen_lin (mΦ j)))
  · refine isQuadGen_par_sum Finset.univ (fun (p : ι₂ × ι₂) u => a p.1 p.2 && Φ u p.1 && Φ u p.2) fun p _ => ?_
    have heq : (fun u => a p.1 p.2 && Φ u p.1 && Φ u p.2) =
        fun u => a p.1 p.2 &&
          xor (xor (cΦ p.1 && cΦ p.2) (cΦ p.1 && linGen (mΦ p.2) u))
              (xor (cΦ p.2 && linGen (mΦ p.1) u) (linGen (mΦ p.1) u && linGen (mΦ p.2) u)) := by
      funext u
      rw [hmΦ p.1 u, hmΦ p.2 u]
      cases a p.1 p.2 <;> cases cΦ p.1 <;> cases cΦ p.2 <;>
        cases linGen (mΦ p.1) u <;> cases linGen (mΦ p.2) u <;> rfl
    rw [heq]
    exact isQuadGen_and_const _ (isQuadGen_xor
      (isQuadGen_xor (isQuadGen_const _) (isQuadGen_and_const _ (isQuadGen_lin _)))
      (isQuadGen_xor (isQuadGen_and_const _ (isQuadGen_lin _)) (isQuadGen_and_lin _ _)))

theorem lin_comp_affine {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (mask : ι₂ → Bool) (Φ : (ι₁ → Bool) → (ι₂ → Bool))
    (hΦ : ∀ j : ι₂, ∃ (c : Bool) (m : ι₁ → Bool), ∀ u, Φ u j = xor c (linGen m u)) :
    ∃ (c : Bool) (m : ι₁ → Bool), ∀ u, linGen mask (Φ u) = xor c (linGen m u) := by
  choose cΦ mΦ hmΦ using hΦ
  refine ⟨par (∑ j : ι₂, (mask j && cΦ j).toNat),
    fun i => par (∑ j : ι₂, (mask j && mΦ j i).toNat), fun u => ?_⟩
  unfold linGen
  have h1 : ∀ j : ι₂, (mask j && Φ u j) = xor (mask j && cΦ j) (mask j && linGen (mΦ j) u) := fun j => by
    rw [hmΦ j u]; cases mask j <;> cases cΦ j <;> cases linGen (mΦ j) u <;> rfl
  simp_rw [h1]
  rw [par_sum_xor]
  congr 1
  unfold linGen
  have hmod : par (∑ j : ι₂, (mask j && par (∑ i : ι₁, (mΦ j i && u i).toNat)).toNat) =
      par (∑ j : ι₂, ∑ i : ι₁, (mask j && mΦ j i && u i).toNat) := by
    refine par_sum_congr_mod Finset.univ _ _ fun j _ => ?_
    cases mask j
    · simp
    · simp only [Bool.true_and, par]
      have hm : (∑ i : ι₁, (mΦ j i && u i).toNat) % 2 = 0 ∨
          (∑ i : ι₁, (mΦ j i && u i).toNat) % 2 = 1 := by omega
      rcases hm with hm | hm <;> simp [hm]
  rw [hmod, Finset.sum_comm]
  refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
  cases u i
  · simp
  · simp only [Bool.and_true, par]
    have hm : (∑ j : ι₂, (mask j && mΦ j i).toNat) % 2 = 0 ∨
        (∑ j : ι₂, (mask j && mΦ j i).toNat) % 2 = 1 := by omega
    rcases hm with hm | hm <;> simp [hm]

def tripleFrom (l0 : Fin 3) (p0 p1 z : Bool) : Fin 3 → Bool :=
  fun l => if l = l0 then z else if l = otherIdx l0 0 then p0 else p1

theorem tripleFrom_prod (l0 : Fin 3) (p0 p1 z : Bool) :
    (tripleFrom l0 p0 p1 z 0 && tripleFrom l0 p0 p1 z 1 && tripleFrom l0 p0 p1 z 2) =
      ((p0 && p1) && z) := by
  unfold tripleFrom otherIdx
  fin_cases l0 <;> cases p0 <;> cases p1 <;> cases z <;> rfl

theorem tripleFrom_eta (l0 : Fin 3) (x : Fin 3 → Bool) :
    tripleFrom l0 (x (otherIdx l0 0)) (x (otherIdx l0 1)) (x l0) = x := by
  funext l
  unfold tripleFrom otherIdx
  fin_cases l0 <;> fin_cases l <;> rfl

def insertTriple {m : ℕ} (i₀ : Fin (m + 1)) (x : Fin 3 → Bool)
    (w' : Fin m → Fin 3 → Bool) : Fin (m + 1) → Fin 3 → Bool :=
  Fin.insertNth (α := fun _ => Fin 3 → Bool) i₀ x w'

theorem insertTriple_same {m : ℕ} (i₀ : Fin (m + 1)) (x : Fin 3 → Bool)
    (w' : Fin m → Fin 3 → Bool) : insertTriple i₀ x w' i₀ = x :=
  Fin.insertNth_apply_same (α := fun _ => Fin 3 → Bool) i₀ x w'

theorem insertTriple_succAbove {m : ℕ} (i₀ : Fin (m + 1)) (x : Fin 3 → Bool)
    (w' : Fin m → Fin 3 → Bool) (j : Fin m) :
    insertTriple i₀ x w' (i₀.succAbove j) = w' j :=
  Fin.insertNth_apply_succAbove (α := fun _ => Fin 3 → Bool) i₀ x w' j

theorem insertTriple_self_removeNth {m : ℕ} (i₀ : Fin (m + 1))
    (w : Fin (m + 1) → Fin 3 → Bool) :
    insertTriple i₀ (w i₀) (Fin.removeNth i₀ w) = w :=
  Fin.insertNth_self_removeNth (α := fun _ => Fin 3 → Bool) i₀ w

theorem removeNth_insertTriple {m : ℕ} (i₀ : Fin (m + 1)) (x : Fin 3 → Bool)
    (w' : Fin m → Fin 3 → Bool) :
    Fin.removeNth i₀ (insertTriple i₀ x w') = w' :=
  Fin.removeNth_insertNth (α := fun _ => Fin 3 → Bool) i₀ x w'

theorem affine_fiber_bound : ∀ (d m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (_hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (masks : Fin d → (Fin m × Fin 3) → Bool) (answers : Fin d → Bool),
    let S := (Finset.univ : Finset (Fin m → Fin 3 → Bool)).filter
      (fun w => ∀ i, par (∑ j : Fin m × Fin 3, (masks i j && w j.1 j.2).toNat) = answers i)
    4 ^ (m - d) *
      ((2 : ℤ) * ((S.filter (fun w =>
        par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) == q w)).card : ℤ) - (S.card : ℤ)).natAbs ≤
      3 ^ (m - d) * S.card := by
  intro d
  induction d with
  | zero =>
    intro m q hq masks answers S
    have hS : S = Finset.univ := by
      ext w; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro i; exact Fin.elim0 i
    rw [hS, Nat.sub_zero]
    have hcard : (Finset.univ : Finset (Fin m → Fin 3 → Bool)).card = 8 ^ m := by
      simp [Fintype.card_fun]
    have hgap : ((2 : ℤ) * (((Finset.univ : Finset (Fin m → Fin 3 → Bool)).filter (fun w =>
        par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) == q w)).card : ℤ) -
        ((Finset.univ : Finset (Fin m → Fin 3 → Bool)).card : ℤ)).natAbs ≤ 6 ^ m := by
      have h1 := gap_eq_natAbs_sum (Finset.univ : Finset (Fin m → Fin 3 → Bool))
        (fun w => par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) q
      have h2 := gap_univ_le m q hq
      rw [h1]
      have h3 : (|∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) =
          ((∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))).natAbs : ℤ) :=
        Int.abs_eq_natAbs _
      rw [h3] at h2
      exact_mod_cast h2
    calc 4 ^ m * ((2 : ℤ) * (((Finset.univ : Finset (Fin m → Fin 3 → Bool)).filter (fun w =>
            par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) == q w)).card : ℤ) -
            ((Finset.univ : Finset (Fin m → Fin 3 → Bool)).card : ℤ)).natAbs
        ≤ 4 ^ m * 6 ^ m := Nat.mul_le_mul_left _ hgap
      _ = 3 ^ m * 8 ^ m := by rw [← mul_pow, ← mul_pow]; rfl
      _ = 3 ^ m * (Finset.univ : Finset (Fin m → Fin 3 → Bool)).card := by rw [hcard]
  | succ d ih =>
    intro m q hq masks answers S
    by_cases hmd : m ≤ d + 1
    · have hsub : m - (d + 1) = 0 := by omega
      rw [hsub, pow_zero, pow_zero, one_mul, one_mul]
      exact gap_le_card S _ _
    · have hm_pos : 1 ≤ m := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      by_cases hm0 : masks 0 = fun _ => false
      · by_cases ha0 : answers 0 = true
        · have hSe : S = ∅ := by
            ext w
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hall
            have h0 := hall 0
            rw [hm0, ha0] at h0
            simp [par] at h0
          rw [hSe]; simp
        · have ha0f : answers 0 = false := by cases h : answers 0 <;> simp_all
          have hS_eq : S = (Finset.univ : Finset (Fin (m' + 1) → Fin 3 → Bool)).filter
              (fun w => ∀ i : Fin d,
                par (∑ j : Fin (m' + 1) × Fin 3, (masks i.succ j && w j.1 j.2).toNat) = answers i.succ) := by
            ext w
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h i; exact h i.succ
            · intro h i
              cases i using Fin.cases with
              | zero => rw [hm0, ha0f]; simp [par]
              | succ k => exact h k
          rw [hS_eq]
          have hih := ih (m' + 1) q hq (fun i => masks i.succ) (fun i => answers i.succ)
          dsimp only at hih
          have hexp : m' + 1 - d = (m' + 1 - (d + 1)) + 1 := by omega
          rw [hexp, pow_succ', pow_succ'] at hih
          have hle : 4 * (4 ^ (m' + 1 - (d + 1)) *
              ((2 : ℤ) * (((Finset.univ.filter (fun w : Fin (m' + 1) → Fin 3 → Bool => ∀ i : Fin d,
                par (∑ j : Fin (m' + 1) × Fin 3, (masks i.succ j && w j.1 j.2).toNat) = answers i.succ)).filter
                  (fun w => par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat) == q w)).card : ℤ) -
                ((Finset.univ.filter (fun w : Fin (m' + 1) → Fin 3 → Bool => ∀ i : Fin d,
                  par (∑ j : Fin (m' + 1) × Fin 3, (masks i.succ j && w j.1 j.2).toNat) = answers i.succ)).card : ℤ)).natAbs) ≤
              4 * (3 ^ (m' + 1 - (d + 1)) *
                (Finset.univ.filter (fun w : Fin (m' + 1) → Fin 3 → Bool => ∀ i : Fin d,
                  par (∑ j : Fin (m' + 1) × Fin 3, (masks i.succ j && w j.1 j.2).toNat) = answers i.succ)).card) := by
            calc 4 * (4 ^ (m' + 1 - (d + 1)) * _)
                = 4 * 4 ^ (m' + 1 - (d + 1)) * _ := by ring
              _ ≤ 3 * 3 ^ (m' + 1 - (d + 1)) * _ := hih
              _ ≤ 4 * 3 ^ (m' + 1 - (d + 1)) * _ :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
              _ = 4 * (3 ^ (m' + 1 - (d + 1)) * _) := by ring
          exact Nat.le_of_mul_le_mul_left hle (by omega)
      · have hex : ∃ p₀ : Fin (m' + 1) × Fin 3, masks 0 p₀ = true := by
          by_contra hall
          push Not at hall
          apply hm0; funext p
          cases h : masks 0 p
          · rfl
          · exact absurd h (hall p)
        obtain ⟨⟨i₀, l₀⟩, hp₀⟩ := hex
        let base0 : Bool → Bool → (Fin m' → Fin 3 → Bool) → Bool := fun p0 p1 w' =>
          par (∑ j : Fin (m' + 1) × Fin 3,
            (masks 0 j && insertTriple i₀ (tripleFrom l₀ p0 p1 false) w' j.1 j.2).toNat)
        let zsol : Bool → Bool → (Fin m' → Fin 3 → Bool) → Bool := fun p0 p1 w' =>
          xor (answers 0) (base0 p0 p1 w')
        let φ : Bool → Bool → (Fin m' → Fin 3 → Bool) → (Fin (m' + 1) → Fin 3 → Bool) :=
          fun p0 p1 w' => insertTriple i₀ (tripleFrom l₀ p0 p1 (zsol p0 p1 w')) w'
        have hlin0_split : ∀ (p0 p1 z : Bool) (w' : Fin m' → Fin 3 → Bool),
            par (∑ j : Fin (m' + 1) × Fin 3,
              (masks 0 j && insertTriple i₀ (tripleFrom l₀ p0 p1 z) w' j.1 j.2).toNat) =
            xor z (base0 p0 p1 w') := by
          intro p0 p1 z w'
          have hdiff : ∀ j : Fin (m' + 1) × Fin 3,
              (masks 0 j && insertTriple i₀ (tripleFrom l₀ p0 p1 z) w' j.1 j.2) =
              xor (if j = (i₀, l₀) then z else false)
                  (masks 0 j && insertTriple i₀ (tripleFrom l₀ p0 p1 false) w' j.1 j.2) := by
            intro ⟨i, l⟩
            by_cases hi : i = i₀
            · subst hi
              rw [insertTriple_same, insertTriple_same]
              by_cases hl : l = l₀
              · subst hl
                simp only [hp₀, Bool.true_and, ↓reduceIte, tripleFrom]
                cases z <;> rfl
              · simp [tripleFrom, hl]
            · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hi
              rw [insertTriple_succAbove, insertTriple_succAbove]
              have hne : (i₀.succAbove j', l) ≠ (i₀, l₀) := fun h => hi (Prod.ext_iff.mp h).1
              simp [hne]
          simp_rw [hdiff]
          rw [par_sum_xor, par_sum_ite_eq Finset.univ (i₀, l₀) (Finset.mem_univ _) z]
        have hbase0_aff : ∀ p0 p1 : Bool,
            ∃ (c : Bool) (m0 : (Fin m' × Fin 3) → Bool), ∀ w' : Fin m' → Fin 3 → Bool,
              base0 p0 p1 w' = xor c (linGen m0 (fun p => w' p.1 p.2)) := by
          intro p0 p1
          let Φ0 : ((Fin m' × Fin 3) → Bool) → ((Fin (m' + 1) × Fin 3) → Bool) :=
            fun v' p => insertTriple i₀ (tripleFrom l₀ p0 p1 false) (fun i l => v' (i, l)) p.1 p.2
          have hΦ0 : ∀ j : Fin (m' + 1) × Fin 3,
              ∃ (c : Bool) (m : (Fin m' × Fin 3) → Bool), ∀ v', Φ0 v' j = xor c (linGen m v') := by
            intro ⟨i, l⟩
            by_cases hi : i = i₀
            · subst hi
              refine ⟨tripleFrom l₀ p0 p1 false l, fun _ => false, fun v' => ?_⟩
              simp [Φ0, insertTriple_same, linGen, par]
            · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hi
              refine ⟨false, fun p => decide (p = (j', l)), fun v' => ?_⟩
              simp only [Φ0, insertTriple_succAbove, Bool.false_xor, linGen]
              have hpt : ∀ p : Fin m' × Fin 3,
                  (decide (p = (j', l)) && v' p) = if p = (j', l) then v' (j', l) else false := fun p => by
                by_cases hp : p = (j', l) <;> simp [hp]
              simp_rw [hpt]
              exact (par_sum_ite_eq Finset.univ (j', l) (Finset.mem_univ _) (v' (j', l))).symm
          obtain ⟨c, m0, hm0⟩ := lin_comp_affine (masks 0) Φ0 hΦ0
          exact ⟨c, m0, fun w' => hm0 (fun p => w' p.1 p.2)⟩
        have hφ_aff : ∀ p0 p1 : Bool,
            ∀ j : Fin (m' + 1) × Fin 3,
              ∃ (c : Bool) (m : (Fin m' × Fin 3) → Bool), ∀ v' : (Fin m' × Fin 3) → Bool,
                φ p0 p1 (fun i l => v' (i, l)) j.1 j.2 = xor c (linGen m v') := by
          intro p0 p1 ⟨i, l⟩
          by_cases hi : i = i₀
          · subst hi
            by_cases hl : l = l₀
            · subst hl
              obtain ⟨c, m0, hm0⟩ := hbase0_aff p0 p1
              refine ⟨xor (answers 0) c, m0, fun v' => ?_⟩
              simp only [φ, insertTriple_same, tripleFrom, ↓reduceIte, zsol, hm0]
              cases answers 0 <;> cases c <;> cases linGen m0 v' <;> rfl
            · refine ⟨if l = otherIdx l₀ 0 then p0 else p1, fun _ => false, fun v' => ?_⟩
              simp [φ, insertTriple_same, tripleFrom, hl, linGen, par]
          · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hi
            refine ⟨false, fun p => decide (p = (j', l)), fun v' => ?_⟩
            simp only [φ, insertTriple_succAbove, Bool.false_xor, linGen]
            have hpt : ∀ p : Fin m' × Fin 3,
                (decide (p = (j', l)) && v' p) = if p = (j', l) then v' (j', l) else false := fun p => by
              by_cases hp : p = (j', l) <;> simp [hp]
            simp_rw [hpt]
            exact (par_sum_ite_eq Finset.univ (j', l) (Finset.mem_univ _) (v' (j', l))).symm
        let fib : Bool × Bool → Finset (Fin (m' + 1) → Fin 3 → Bool) := fun p =>
          S.filter (fun w => w i₀ (otherIdx l₀ 0) = p.1 ∧ w i₀ (otherIdx l₀ 1) = p.2)
        have hfib_bound : ∀ p : Bool × Bool,
            (4 ^ (m' - d) : ℤ) * |∑ w ∈ fib p,
              sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
            (3 ^ (m' - d) : ℤ) * ((fib p).card : ℤ) := by
          intro ⟨p0, p1⟩
          have heq_masks : ∀ k : Fin d, ∃ (ck : Bool) (mk : (Fin m' × Fin 3) → Bool),
              ∀ w' : Fin m' → Fin 3 → Bool,
                par (∑ j : Fin (m' + 1) × Fin 3, (masks k.succ j && φ p0 p1 w' j.1 j.2).toNat) =
                  xor ck (par (∑ j : Fin m' × Fin 3, (mk j && w' j.1 j.2).toNat)) := fun k => by
            obtain ⟨ck, mk, hmk⟩ := lin_comp_affine (masks k.succ)
              (fun v' j => φ p0 p1 (fun i l => v' (i, l)) j.1 j.2) (hφ_aff p0 p1)
            exact ⟨ck, mk, fun w' => hmk (fun j => w' j.1 j.2)⟩
          choose ck masks' hmasks' using heq_masks
          let answers' : Fin d → Bool := fun k => xor (answers k.succ) (ck k)
          let S' : Finset (Fin m' → Fin 3 → Bool) := Finset.univ.filter
            (fun w' => ∀ k : Fin d,
              par (∑ j : Fin m' × Fin 3, (masks' k j && w' j.1 j.2).toNat) = answers' k)
          let q' : (Fin m' → Fin 3 → Bool) → Bool := fun w' =>
            xor ((p0 && p1) && zsol p0 p1 w') (q (φ p0 p1 w'))
          have hq'_quad : ∃ (b : Bool) (l : (Fin m' × Fin 3) → Bool)
              (a : (Fin m' × Fin 3) → (Fin m' × Fin 3) → Bool),
              ∀ w', q' w' = xor (xor b (par (∑ j : Fin m' × Fin 3, (l j && w' j.1 j.2).toNat)))
                (par (∑ i : Fin m' × Fin 3, ∑ j : Fin m' × Fin 3, (a i j && w' i.1 i.2 && w' j.1 j.2).toNat)) := by
            have hQv := quad_to_gen q hq
            have hq_comp : IsQuadGen (fun v' : (Fin m' × Fin 3) → Bool =>
                q (φ p0 p1 (fun i l => v' (i, l)))) :=
              isQuadGen_comp_affine hQv (fun v' j => φ p0 p1 (fun i l => v' (i, l)) j.1 j.2) (hφ_aff p0 p1)
            obtain ⟨cb, mb, hmb⟩ := hbase0_aff p0 p1
            have hz_quad : IsQuadGen (fun v' : (Fin m' × Fin 3) → Bool =>
                (p0 && p1) && zsol p0 p1 (fun i l => v' (i, l))) := by
              have heq : (fun v' : (Fin m' × Fin 3) → Bool =>
                  (p0 && p1) && zsol p0 p1 (fun i l => v' (i, l))) =
                  fun v' => (p0 && p1) && xor (xor (answers 0) cb) (linGen mb v') := by
                funext v'; dsimp only [zsol]; rw [hmb]
                cases answers 0 <;> cases cb <;> cases linGen mb v' <;> rfl
              rw [heq]
              exact isQuadGen_and_const _ (isQuadGen_xor (isQuadGen_const _) (isQuadGen_lin mb))
            obtain ⟨b', l', a', hq'eq⟩ := isQuadGen_xor hz_quad hq_comp
            exact ⟨b', l', a', fun w' => hq'eq (fun j => w' j.1 j.2)⟩
          have hfib_bij : fib (p0, p1) = S'.image (φ p0 p1) := by
            ext w
            simp only [fib, S, S', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hall, hp0w, hp1w⟩
              let w' : Fin m' → Fin 3 → Bool := Fin.removeNth i₀ w
              have hw_eq : φ p0 p1 w' = w := by
                have h0 := hall 0
                have hwtrip : w = insertTriple i₀ (tripleFrom l₀ p0 p1 (w i₀ l₀)) w' := by
                  rw [← hp0w, ← hp1w, tripleFrom_eta l₀ (w i₀)]
                  exact (insertTriple_self_removeNth i₀ w).symm
                rw [hwtrip, hlin0_split] at h0
                have hzeq : w i₀ l₀ = zsol p0 p1 w' := by
                  dsimp only [zsol]
                  rw [← h0]
                  cases w i₀ l₀ <;> cases base0 p0 p1 w' <;> rfl
                dsimp only [φ]
                rw [← hzeq, ← hwtrip]
              refine ⟨w', fun k => ?_, hw_eq⟩
              have hk := hall k.succ
              rw [← hw_eq, hmasks' k w'] at hk
              dsimp only [answers']
              rw [← hk]
              cases ck k <;> cases par (∑ j : Fin m' × Fin 3, (masks' k j && w' j.1 j.2).toNat) <;> rfl
            · rintro ⟨w', hw', rfl⟩
              refine ⟨fun k => ?_, ?_, ?_⟩
              · cases k using Fin.cases with
                | zero =>
                  dsimp only [φ]
                  rw [hlin0_split]
                  dsimp only [zsol]
                  cases answers 0 <;> cases base0 p0 p1 w' <;> rfl
                | succ k =>
                  rw [hmasks' k w', hw' k]
                  dsimp only [answers']
                  cases answers k.succ <;> cases ck k <;> rfl
              · simp only [φ, insertTriple_same, tripleFrom, otherIdx]
                fin_cases l₀ <;> rfl
              · simp only [φ, insertTriple_same, tripleFrom, otherIdx]
                fin_cases l₀ <;> rfl
          have hφ_inj : Function.Injective (φ p0 p1) := by
            intro w1 w2 heq
            have := congrArg (Fin.removeNth i₀) heq
            simpa only [φ, removeNth_insertTriple] using this
          have hcard_eq : (fib (p0, p1)).card = S'.card := by
            rw [hfib_bij, Finset.card_image_of_injective _ hφ_inj]
          have hsum_eq : (∑ w ∈ fib (p0, p1),
              sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
              ∑ w' ∈ S', sgn (xor (par (∑ i : Fin m', (w' i 0 && w' i 1 && w' i 2).toNat)) (q' w')) := by
            rw [hfib_bij, Finset.sum_image (fun a _ b _ h => hφ_inj h)]
            refine Finset.sum_congr rfl fun w' _ => ?_
            congr 1
            rw [Fin.sum_univ_succAbove _ i₀]
            simp only [φ, insertTriple_same, insertTriple_succAbove, tripleFrom_prod]
            rw [par_add, par_toNat]
            dsimp only [q']
            cases ((p0 && p1) && zsol p0 p1 w') <;>
              cases par (∑ i : Fin m', (w' i 0 && w' i 1 && w' i 2).toNat) <;>
              cases q (φ p0 p1 w') <;> rfl
          rw [hcard_eq, hsum_eq]
          have hih := ih m' q' hq'_quad masks' answers'
          dsimp only at hih
          have hgap := gap_eq_natAbs_sum S' (fun w' => par (∑ i : Fin m', (w' i 0 && w' i 1 && w' i 2).toNat)) q'
          have hih_int : (4 ^ (m' - d) : ℤ) *
              |∑ w' ∈ S', sgn (xor (par (∑ i : Fin m', (w' i 0 && w' i 1 && w' i 2).toNat)) (q' w'))| ≤
              (3 ^ (m' - d) : ℤ) * (S'.card : ℤ) := by
            rw [← hgap, Int.abs_eq_natAbs]
            exact_mod_cast hih
          exact hih_int
        have hpart_sum : ∀ (G : (Fin (m' + 1) → Fin 3 → Bool) → ℤ),
            (∑ w ∈ S, G w) = ∑ p : Bool × Bool, ∑ w ∈ fib p, G w := by
          intro G
          have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Bool × Bool)) fib := by
            intro p₁ _ p₂ _ hne
            change Disjoint (fib p₁) (fib p₂)
            rw [Finset.disjoint_left]
            intro w hw1 hw2
            simp only [fib, Finset.mem_filter] at hw1 hw2
            apply hne
            exact Prod.ext (hw1.2.1.symm.trans hw2.2.1) (hw1.2.2.symm.trans hw2.2.2)
          have hbi : (Finset.univ : Finset (Bool × Bool)).biUnion fib = S := by
            ext w
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, fib, Finset.mem_filter]
            constructor
            · rintro ⟨_, hw, _, _⟩; exact hw
            · intro hw; exact ⟨(w i₀ (otherIdx l₀ 0), w i₀ (otherIdx l₀ 1)), hw, rfl, rfl⟩
          rw [← hbi, Finset.sum_biUnion hdisj]
        have hcard_sum : (S.card : ℤ) = ∑ p : Bool × Bool, ((fib p).card : ℤ) := by
          simpa using hpart_sum (fun _ => (1 : ℤ))
        have hmain_int : (4 ^ (m' - d) : ℤ) *
            |∑ w ∈ S, sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
            (3 ^ (m' - d) : ℤ) * (S.card : ℤ) := by
          rw [hpart_sum, hcard_sum, Finset.mul_sum]
          calc (4 ^ (m' - d) : ℤ) * |∑ p : Bool × Bool, ∑ w ∈ fib p,
                  sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))|
              ≤ (4 ^ (m' - d) : ℤ) * ∑ p : Bool × Bool, |∑ w ∈ fib p,
                  sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))| :=
                mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
            _ = ∑ p : Bool × Bool, (4 ^ (m' - d) : ℤ) * |∑ w ∈ fib p,
                  sgn (xor (par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) (q w))| :=
                Finset.mul_sum ..
            _ ≤ ∑ p : Bool × Bool, (3 ^ (m' - d) : ℤ) * ((fib p).card : ℤ) :=
                Finset.sum_le_sum fun p _ => hfib_bound p
        have hgap := gap_eq_natAbs_sum S
          (fun w => par (∑ i : Fin (m' + 1), (w i 0 && w i 1 && w i 2).toNat)) q
        rw [← hgap, Int.abs_eq_natAbs] at hmain_int
        have hsub : m' + 1 - (d + 1) = m' - d := by omega
        rw [hsub]
        exact_mod_cast hmain_int

theorem witness_m2_sum :
    (∑ w : Fin 2 → Fin 3 → Bool,
      sgn (xor (xor (w 0 0 && w 0 1 && w 0 2) (w 1 0 && w 1 1 && w 1 2))
               (w 0 0 && w 1 0))) = 28 := by
  let eq6 : (Fin 2 → Fin 3 → Bool) ≃ (Bool × Bool × Bool) × (Bool × Bool × Bool) :=
    { toFun := fun w => ((w 0 0, w 0 1, w 0 2), (w 1 0, w 1 1, w 1 2))
      invFun := fun p i j =>
        match i.val, j.val with
        | 0, 0 => p.1.1 | 0, 1 => p.1.2.1 | 0, _ => p.1.2.2
        | _, 0 => p.2.1 | _, 1 => p.2.2.1 | _, _ => p.2.2.2
      left_inv := fun w => by funext i j; fin_cases i <;> fin_cases j <;> rfl
      right_inv := fun ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩ => rfl }
  trans (∑ p : (Bool × Bool × Bool) × (Bool × Bool × Bool),
    sgn (xor (xor (p.1.1 && p.1.2.1 && p.1.2.2) (p.2.1 && p.2.2.1 && p.2.2.2)) (p.1.1 && p.2.1)))
  · exact Fintype.sum_equiv eq6 _ _ (fun _ => rfl)
  · decide

theorem witness_one_sum :
    (∑ x : Fin 3 → Bool, sgn (x 0 && x 1 && x 2)) = 6 := by
  let eq3 : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun p j => match j.val with | 0 => p.1 | 1 => p.2.1 | _ => p.2.2
      left_inv := fun x => by funext j; fin_cases j <;> rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  trans (∑ p : Bool × Bool × Bool, sgn (p.1 && p.2.1 && p.2.2))
  · exact Fintype.sum_equiv eq3 _ _ (fun _ => rfl)
  · decide

theorem cross_witness_exists (m : ℕ) (hm : 2 ≤ m) :
    let W := Fin m → Fin 3 → Bool
    let J := Fin m × Fin 3
    let flip := fun (w : W) (i : J) (h : Fin m) (l : Fin 3) =>
      xor (w h l) (decide ((h, l) = i))
    ∃ q : W → Bool,
      (∃ (b : Bool) (l : J → Bool) (a : J → J → Bool),
        ∀ w, q w = xor (xor b (par (∑ j : J, (l j && w j.1 j.2).toNat)))
          (par (∑ i : J, ∑ j : J, (a i j && w i.1 i.2 && w j.1 j.2).toNat))) ∧
      (∃ (i j : J) (w : W), i.1 ≠ j.1 ∧
        xor (xor (q w) (q (flip w i))) (xor (q (flip w j)) (q (flip (flip w i) j))) = true) ∧
      ((2 : ℤ) * (((Finset.univ : Finset W).filter (fun w =>
          par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) == q w)).card : ℤ) -
        ((Finset.univ : Finset W).card : ℤ)).natAbs = 28 * 6 ^ (m - 2) := by
  intro W J flip
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let q : W → Bool := fun w => w i0 0 && w i1 0
  refine ⟨q, ?_, ?_, ?_⟩
  · refine ⟨false, fun _ => false, fun p₁ p₂ => decide (p₁ = (i0, 0) ∧ p₂ = (i1, 0)), fun w => ?_⟩
    simp only [Bool.false_and, Bool.toNat_false, Finset.sum_const_zero, par_zero, Bool.false_xor]
    have hsum : (∑ p₁ : J, ∑ p₂ : J,
        (decide (p₁ = (i0, 0) ∧ p₂ = (i1, 0)) && w p₁.1 p₁.2 && w p₂.1 p₂.2).toNat) =
        (w i0 0 && w i1 0).toNat := by
      rw [Finset.sum_eq_single (i0, 0)]
      · rw [Finset.sum_eq_single (i1, 0)]
        · simp
        · intro p₂ _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p₁ _ hne
        refine Finset.sum_eq_zero fun p₂ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, par_toNat]
  · refine ⟨(i0, 0), (i1, 0), fun _ _ => false, by simp [i0, i1, Fin.ext_iff], ?_⟩
    have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    simp [q, flip, hne, hne.symm]
  · have hgap := gap_eq_natAbs_sum (Finset.univ : Finset W)
      (fun w => par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) q
    rw [hgap]
    let split2 : W ≃ (Fin 2 → Fin 3 → Bool) × (Fin (m - 2) → Fin 3 → Bool) :=
      { toFun := fun w =>
          (fun k => w ⟨k.val, by omega⟩, fun k => w ⟨k.val + 2, by omega⟩)
        invFun := fun p i =>
          if h : i.val < 2 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 2, by omega⟩
        left_inv := fun w => by
          funext i
          by_cases h : i.val < 2
          · simp [h]
          · simp only [h, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp; omega
        right_inv := fun ⟨a, b⟩ => by
          apply Prod.ext
          · funext k; have hk := k.isLt; simp [hk]
          · funext k; have hnot : ¬ (k.val + 2 < 2) := by omega
            simp only [hnot, ↓reduceDIte]
            congr 1 }
    have hsum : (∑ w : W, sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
        28 * 6 ^ (m - 2) := by
      trans (∑ p : (Fin 2 → Fin 3 → Bool) × (Fin (m - 2) → Fin 3 → Bool),
        sgn (xor (xor (p.1 0 0 && p.1 0 1 && p.1 0 2) (p.1 1 0 && p.1 1 1 && p.1 1 2))
                 (p.1 0 0 && p.1 1 0)) *
        ∏ k : Fin (m - 2), sgn (p.2 k 0 && p.2 k 1 && p.2 k 2))
      · refine Fintype.sum_equiv split2 _ _ fun w => ?_
        rw [← sgn_par_sum, ← sgn_xor]
        congr 1
        have hpart : (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat) =
            (w i0 0 && w i0 1 && w i0 2).toNat + (w i1 0 && w i1 1 && w i1 2).toNat +
            ∑ k : Fin (m - 2), (w ⟨k.val + 2, by omega⟩ 0 && w ⟨k.val + 2, by omega⟩ 1 &&
              w ⟨k.val + 2, by omega⟩ 2).toNat := by
          let f3 : Fin m → ℕ := fun i => (w i 0 && w i 1 && w i 2).toNat
          have h1 : (∑ i : Fin m, f3 i) = f3 i0 + f3 i1 +
              ∑ i ∈ (Finset.univ.erase i0).erase i1, f3 i := by
            rw [← Finset.add_sum_erase Finset.univ f3 (Finset.mem_univ i0)]
            have hi1_mem : i1 ∈ (Finset.univ : Finset (Fin m)).erase i0 :=
              Finset.mem_erase.mpr ⟨by simp [i0, i1, Fin.ext_iff], Finset.mem_univ _⟩
            rw [← Finset.add_sum_erase _ f3 hi1_mem]; ring
          rw [h1]
          congr 1
          refine Finset.sum_bij (fun i hi => ⟨i.val - 2, by
            have hne1 : i ≠ i1 := (Finset.mem_erase.mp hi).1
            have hne0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            have hv0 : i.val ≠ 0 := fun h => hne0 (Fin.ext h)
            have hv1 : i.val ≠ 1 := fun h => hne1 (Fin.ext h)
            omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a ha b hb heq
            have ha1 : a ≠ i1 := (Finset.mem_erase.mp ha).1
            have ha0 : a ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
            have hb1 : b ≠ i1 := (Finset.mem_erase.mp hb).1
            have hb0 : b ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
            have hva0 : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
            have hva1 : a.val ≠ 1 := fun h => ha1 (Fin.ext h)
            have hvb0 : b.val ≠ 0 := fun h => hb0 (Fin.ext h)
            have hvb1 : b.val ≠ 1 := fun h => hb1 (Fin.ext h)
            have hval := congrArg Fin.val heq
            dsimp only at hval
            exact Fin.ext (by omega)
          · intro k _
            refine ⟨⟨k.val + 2, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
            simp [i0, i1, Fin.ext_iff]
          · intro i hi
            have hne1 : i ≠ i1 := (Finset.mem_erase.mp hi).1
            have hne0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            have hv0 : i.val ≠ 0 := fun h => hne0 (Fin.ext h)
            have hv1 : i.val ≠ 1 := fun h => hne1 (Fin.ext h)
            have hi_eq : (⟨i.val - 2 + 2, by omega⟩ : Fin m) = i := Fin.ext (by dsimp; omega)
            dsimp only [f3]; rw [hi_eq]
        rw [hpart, par_add, par_add, par_toNat, par_toNat]
        dsimp only [split2, q, i0, i1, Equiv.coe_fn_mk]
        simp only [Fin.val_zero, Fin.val_one]
        cases (w ⟨0, by omega⟩ 0 && w ⟨0, by omega⟩ 1 && w ⟨0, by omega⟩ 2) <;>
          cases (w ⟨1, by omega⟩ 0 && w ⟨1, by omega⟩ 1 && w ⟨1, by omega⟩ 2) <;>
          cases (w ⟨0, by omega⟩ 0 && w ⟨1, by omega⟩ 0) <;>
          cases par (∑ k : Fin (m - 2), (w ⟨k.val + 2, by omega⟩ 0 && w ⟨k.val + 2, by omega⟩ 1 &&
            w ⟨k.val + 2, by omega⟩ 2).toNat) <;> rfl
      · rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, witness_m2_sum,
          sum_prod_fin_fun (fun (_ : Fin (m - 2)) (x : Fin 3 → Bool) => sgn (x 0 && x 1 && x 2))]
        simp_rw [witness_one_sum]
        simp
    rw [hsum]
    have : (28 * 6 ^ (m - 2) : ℤ) = ((28 * 6 ^ (m - 2) : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.natAbs_natCast]

end PEqualNP.Outside.L_lib_416_aux

theorem PEqualNP.Outside.L_lib_416 : (∀ m : Nat,
  let W := Fin m → Fin 3 → Bool
  let J := Fin m × Fin 3
  let get := fun (w : W) (j : J) => w j.1 j.2
  let par := fun (n : Nat) => n % 2 == 1
  let lin := fun (mask : J → Bool) (w : W) =>
    par (∑ j : J, (mask j && get w j).toNat)
  let quad := fun (q : W → Bool) => ∃ (b : Bool) (l : J → Bool) (a : J → J → Bool),
    ∀ w, q w = xor (xor b (lin l w))
      (par (∑ i : J, ∑ j : J, (a i j && get w i && get w j).toNat))
  let f := fun (w : W) => par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)
  let gap := fun (S : Finset W) (q : W → Bool) =>
    ((2 : Int) * ((S.filter (fun w => f w == q w)).card : Int) - (S.card : Int)).natAbs
  let flip := fun (w : W) (i : J) (h : Fin m) (l : Fin 3) =>
    xor (w h l) (decide ((h,l) = i))
  let cross := fun (q : W → Bool) => ∃ (i j : J) (w : W), i.1 ≠ j.1 ∧
    xor (xor (q w) (q (flip w i))) (xor (q (flip w j)) (q (flip (flip w i) j))) = true
  let radicalSize := fun (q : W → Bool) (lane : Fin m → Fin 3) =>
    let restrict := fun (z : Fin m → Bool) => q (fun i j => (j == lane i) && z i)
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t : Fin m → Bool,
      xor (xor (restrict (fun i => xor (h i) (t i))) (restrict h))
        (xor (restrict t) (restrict (fun _ => false))) = false)).card
  (∀ q : W → Bool, quad q →
    gap Finset.univ q ≤ 6^m ∧
    (gap Finset.univ q = 6^m ↔
      ∃ (constant : Bool) (point : Fin m → Fin 3 → Bool), ∀ w,
        q w = xor (f w) (xor constant (par (∑ i : Fin m, (decide (w i = point i)).toNat)))) ∧
    (∀ (lane : Fin m → Fin 3) (s : Nat), 2*s ≤ m →
      radicalSize q lane = 2^(m-2*s) → 9^s * gap Finset.univ q ≤ 8^s * 6^m) ∧
    (cross q → 9 * gap Finset.univ q ≤ 8 * 6^m ∧ (m = 2 → gap Finset.univ q ≤ 28)) ∧
    (∀ (d : Nat) (masks : Fin d → J → Bool) (answers : Fin d → Bool),
      let S := (Finset.univ : Finset W).filter (fun w => ∀ i, lin (masks i) w = answers i)
      4^(m-d) * gap S q ≤ 3^(m-d) * S.card)) ∧
  (2 ≤ m → ∃ q : W → Bool, quad q ∧ cross q ∧ gap Finset.univ q = 28*6^(m-2))) := by
  intro m W J get par lin quad f gap flip cross radicalSize
  constructor
  · intro q hq
    have hgap_int : (gap Finset.univ q : ℤ) =
        |∑ w : Fin m → Fin 3 → Bool,
          PEqualNP.Outside.L_lib_416_aux.sgn
            (xor (PEqualNP.Outside.L_lib_416_aux.par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| := by
      dsimp only [gap]
      rw [← Int.abs_eq_natAbs, PEqualNP.Outside.L_lib_416_aux.gap_eq_natAbs_sum]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := PEqualNP.Outside.L_lib_416_aux.gap_univ_le m q hq
      rw [← hgap_int] at h
      exact_mod_cast h
    · have h := PEqualNP.Outside.L_lib_416_aux.gap_eq_six_pow_iff m q hq
      rw [← hgap_int] at h
      constructor
      · intro heq
        exact h.mp (by exact_mod_cast heq)
      · intro hex
        exact_mod_cast h.mpr hex
    · intro lane s hs hrad
      have h := PEqualNP.Outside.L_lib_416_aux.lane_rank_bound m s q hq lane hs hrad
      rw [← hgap_int] at h
      exact_mod_cast h
    · intro hcr
      obtain ⟨b0, l0, a0, hqeq⟩ := hq
      obtain ⟨i, j, w, hij, hdiff⟩ := hcr
      have hxt : xor (a0 i j) (a0 j i) = true := by
        have := PEqualNP.Outside.L_lib_416_aux.flip_second_diff q b0 l0 a0 hqeq i j w
        dsimp only at this
        rw [← this]; exact hdiff
      refine ⟨?_, ?_⟩
      · have h := PEqualNP.Outside.L_lib_416_aux.cross_gap_bound m q b0 l0 a0 hqeq i j hij hxt
        rw [← hgap_int] at h
        exact_mod_cast h
      · rintro rfl
        have h := PEqualNP.Outside.L_lib_416_aux.cross_m2_bound q b0 l0 a0 hqeq i j hij hxt
        rw [← hgap_int] at h
        exact_mod_cast h
    · intro d masks answers S
      exact PEqualNP.Outside.L_lib_416_aux.affine_fiber_bound d m q hq masks answers
  · intro hm
    exact PEqualNP.Outside.L_lib_416_aux.cross_witness_exists m hm

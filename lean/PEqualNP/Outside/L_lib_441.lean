import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_441

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



def stdBasis {m : ℕ} (i : Fin m) : Fin m → Bool :=
  fun j => decide (j = i)

def IsCoordSubgroup {m : ℕ} (H : Finset (Fin m → Bool)) : Prop :=
  ∀ h ∈ H, ∀ i : Fin m, h i = true → stdBasis i ∈ H

def vecOf {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool :=
  fun i => decide (i ∈ S)

theorem vecOf_inj {m : ℕ} : Function.Injective (vecOf (m := m)) := by
  intro S T h
  ext i
  have hi := congrFun h i
  dsimp only [vecOf] at hi
  simpa using hi

theorem vecOf_mem_of_subset {m : ℕ} {H : Finset (Fin m → Bool)} (hH : IsSubgroup H)
    {P : Finset (Fin m)} (hP : ∀ i ∈ P, stdBasis i ∈ H) :
    ∀ S : Finset (Fin m), S ⊆ P → vecOf S ∈ H := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have : vecOf (∅ : Finset (Fin m)) = fun _ => false := by funext i; simp [vecOf]
    rw [this]
    exact hH.1
  | insert a S ha ih =>
    intro hsub
    have haP : a ∈ P := hsub (Finset.mem_insert_self a S)
    have hSP : S ⊆ P := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have h1 : stdBasis a ∈ H := hP a haP
    have h2 : vecOf S ∈ H := ih hSP
    have heq : vecOf (insert a S) = fun i => xor (stdBasis a i) (vecOf S i) := by
      funext i
      by_cases hi : i = a
      · subst hi; simp [vecOf, stdBasis, ha]
      · simp [vecOf, stdBasis, hi]
    rw [heq]
    exact hH.2 _ h1 _ h2

theorem coordSubgroup_mem_iff {m : ℕ} {H : Finset (Fin m → Bool)}
    (hH : IsSubgroup H) (hC : IsCoordSubgroup H) :
    let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ H)
    ∀ h : Fin m → Bool, h ∈ H ↔ ∀ i : Fin m, i ∉ P → h i = false := by
  intro P h
  constructor
  · intro hh i hi
    by_contra hne
    have ht : h i = true := by cases hv : h i <;> simp_all
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC h hh i ht⟩
  · intro hall
    let S : Finset (Fin m) := Finset.univ.filter (fun i => h i = true)
    have hsub : S ⊆ P := by
      intro i hi
      have ht : h i = true := (Finset.mem_filter.mp hi).2
      by_contra hnot
      have hf := hall i hnot
      rw [ht] at hf
      exact Bool.noConfusion hf
    have heq : h = vecOf S := by
      funext i
      simp only [vecOf, S, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h i <;> rfl
    rw [heq]
    exact vecOf_mem_of_subset hH (fun i hi => (Finset.mem_filter.mp hi).2) S hsub

theorem coordSubgroup_card {m : ℕ} {H : Finset (Fin m → Bool)}
    (hH : IsSubgroup H) (hC : IsCoordSubgroup H) :
    H.card = 2 ^ (Finset.univ.filter (fun i : Fin m => stdBasis i ∈ H)).card := by
  classical
  let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ H)
  have hmem := coordSubgroup_mem_iff hH hC
  dsimp only at hmem
  have hHeq : H = P.powerset.image vecOf := by
    ext h
    simp only [Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro hh
      let S : Finset (Fin m) := Finset.univ.filter (fun i => h i = true)
      refine ⟨S, ?_, ?_⟩
      · intro i hi
        by_contra hnot
        have hf := (hmem h).mp hh i hnot
        have ht := (Finset.mem_filter.mp hi).2
        rw [ht] at hf
        exact Bool.noConfusion hf
      · funext i
        simp only [vecOf, S, Finset.mem_filter, Finset.mem_univ, true_and]
        cases h i <;> rfl
    · rintro ⟨S, hSP, rfl⟩
      exact vecOf_mem_of_subset hH (fun i hi => (Finset.mem_filter.mp hi).2) S hSP
  conv_lhs => rw [hHeq]
  rw [Finset.card_image_of_injective _ vecOf_inj, Finset.card_powerset]

theorem coordSubgroup_half_wt_sum {m k : ℕ} {H : Finset (Fin m → Bool)}
    (hH : IsSubgroup H) (hC : IsCoordSubgroup H) (hHcard : H.card = 2 ^ k)
    (c : Fin m → Bool) (q₀ : Fin m) (hq₀ : stdBasis q₀ ∉ H) (hcq : c q₀ = true) :
    2 * ∑ h ∈ H, 2 ^ (m - wt (fun i => xor (c i) (h i))) ≤ 3 ^ k * 2 ^ (m - k) := by
  let c' : Fin m → Bool := fun i => if i = q₀ then false else c i
  have hterm : ∀ h ∈ H,
      2 * 2 ^ (m - wt (fun i => xor (c i) (h i))) =
      2 ^ (m - wt (fun i => xor (c' i) (h i))) := by
    intro h hh
    have hhq : h q₀ = false := by
      by_contra hne
      have ht : h q₀ = true := by cases hv : h q₀ <;> simp_all
      exact hq₀ (hC h hh q₀ ht)
    have hwt_eq : wt (fun i => xor (c i) (h i)) = wt (fun i => xor (c' i) (h i)) + 1 := by
      unfold wt
      have hset : Finset.univ.filter (fun i : Fin m => xor (c i) (h i) = true) =
          insert q₀ (Finset.univ.filter (fun i : Fin m => xor (c' i) (h i) = true)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hi : i = q₀
        · subst hi; simp [c', hcq, hhq]
        · simp [c', hi]
      have hnotmem : q₀ ∉ Finset.univ.filter (fun i : Fin m => xor (c' i) (h i) = true) := by
        simp [c', hhq]
      rw [hset, Finset.card_insert_of_notMem hnotmem]
    have hwt_le : wt (fun i => xor (c i) (h i)) ≤ m := by
      unfold wt
      calc (Finset.univ.filter (fun i : Fin m => xor (c i) (h i) = true)).card
          ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
        _ = m := Finset.card_fin m
    have hexp : m - wt (fun i => xor (c' i) (h i)) = (m - wt (fun i => xor (c i) (h i))) + 1 := by
      omega
    rw [hexp, pow_succ']
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
  obtain ⟨k', _, hk'card, hk'sum⟩ := subgroup_wt_bound m H hH
  have hkeq : k' = k := Nat.pow_right_injective (by omega) (hk'card.symm.trans hHcard)
  rw [← hkeq]
  exact hk'sum c'

theorem subgroup_wt_bound_noncoord : ∀ (m : ℕ) (H : Finset (Fin m → Bool)),
    IsSubgroup H → ¬ IsCoordSubgroup H →
    ∃ k ≤ m, H.card = 2 ^ k ∧
      ∀ c : Fin m → Bool,
        6 * ∑ h ∈ H, 2 ^ (m - wt (fun i => xor (c i) (h i))) ≤ 5 * (3 ^ k * 2 ^ (m - k)) := by
  intro m
  induction m with
  | zero =>
    intro H _ hNC
    exfalso
    apply hNC
    intro _ _ i _
    exact Fin.elim0 i
  | succ m ih =>
    intro H hH hNC
    let H0 : Finset (Fin m → Bool) := Finset.univ.filter (fun h' => consBool false h' ∈ H)
    let H1 : Finset (Fin m → Bool) := Finset.univ.filter (fun h' => consBool true h' ∈ H)
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
    have hwt_cons : ∀ (b : Bool) (u : Fin m → Bool),
        wt (consBool b u) = b.toNat + wt u := by
      intro b u
      unfold wt
      have hsplit : (Finset.univ.filter (fun i : Fin (m + 1) => consBool b u i = true)) =
          (if b = true then {0} else ∅) ∪
            (Finset.univ.filter (fun j : Fin m => u j = true)).map (Fin.succEmb m) := by
        ext i
        cases i using Fin.cases with
        | zero => cases b <;> simp [Fin.succEmb, consBool_zero]
        | succ j => cases b <;> simp [Fin.succEmb, consBool_succ]
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
    have hcons_std : ∀ j : Fin m, consBool false (stdBasis j) = stdBasis j.succ := by
      intro j; funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ k => simp [consBool_succ, stdBasis]
    by_cases hH1e : H1 = ∅
    · have hH0_nc : ¬ IsCoordSubgroup H0 := by
        intro hH0c
        apply hNC
        intro h hh i hi
        have h0f : h 0 = false := by
          cases h0v : h 0
          · rfl
          · exfalso
            have hmem1 : Fin.tail h ∈ H1 := by
              simp only [H1, Finset.mem_filter, Finset.mem_univ, true_and]
              have : consBool true (Fin.tail h) = h := by rw [← h0v]; exact Fin.cons_self_tail h
              rw [this]; exact hh
            rw [hH1e] at hmem1
            exact Finset.notMem_empty _ hmem1
        cases i using Fin.cases with
        | zero => rw [h0f] at hi; exact Bool.noConfusion hi
        | succ j =>
          have hmem0 : Fin.tail h ∈ H0 := by
            simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
            have : consBool false (Fin.tail h) = h := by rw [← h0f]; exact Fin.cons_self_tail h
            rw [this]; exact hh
          have hstd : stdBasis j ∈ H0 := hH0c (Fin.tail h) hmem0 j hi
          have hstd' : consBool false (stdBasis j) ∈ H := (Finset.mem_filter.mp hstd).2
          rwa [hcons_std j] at hstd'
      obtain ⟨k, hkm, hH0card, hH0sum⟩ := ih H0 hH0_sub hH0_nc
      refine ⟨k, by omega, ?_, fun c => ?_⟩
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
            rw [this]; omega
        have hsum_le : ∑ u ∈ H0, 2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i))) ≤
            2 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) := by
          calc ∑ u ∈ H0, 2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i)))
              ≤ ∑ u ∈ H0, 2 * 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) :=
                Finset.sum_le_sum hstep
            _ = 2 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j))) :=
                (Finset.mul_sum ..).symm
        have hb := hH0sum (Fin.tail c)
        have hexp : m + 1 - k = (m - k) + 1 := by omega
        rw [hexp, pow_succ']
        calc 6 * ∑ u ∈ H0, 2 ^ (m + 1 - wt (fun i => xor (c i) (consBool false u i)))
            ≤ 6 * (2 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) :=
              Nat.mul_le_mul_left 6 hsum_le
          _ = 2 * (6 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) := by ring
          _ ≤ 2 * (5 * (3 ^ k * 2 ^ (m - k))) := Nat.mul_le_mul_left 2 hb
          _ = 5 * (3 ^ k * (2 * 2 ^ (m - k))) := by ring
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
      have hsum_split : ∀ c : Fin (m + 1) → Bool,
          ∑ h ∈ H, 2 ^ (m + 1 - wt (fun i => xor (c i) (h i))) =
          (if c 0 = false then 2 else 1) *
            (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) +
          (if c 0 = true then 2 else 1) *
            (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)))) := by
        intro c
        rw [hsplitH, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map, hH1_bij, Finset.sum_map]
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
      by_cases hH0c : IsCoordSubgroup H0
      · obtain ⟨k, hkm, hH0card, hH0sum⟩ := subgroup_wt_bound m H0 hH0_sub
        have hH1card : H1.card = 2 ^ k := by rw [hH1_bij, Finset.card_map, hH0card]
        have hhstar_not : hstar ∉ H0 := by
          intro hh0
          apply hNC
          have he0 : stdBasis (0 : Fin (m + 1)) ∈ H := by
            have h0H : consBool false hstar ∈ H := (Finset.mem_filter.mp hh0).2
            have heq : stdBasis (0 : Fin (m + 1)) =
                fun i => xor (consBool true hstar i) (consBool false hstar i) := by
              funext i
              cases i using Fin.cases with
              | zero => rfl
              | succ j => simp [stdBasis, consBool_succ]
            rw [heq]
            exact hH.2 _ hhstarH _ h0H
          intro h hh i hi
          cases i using Fin.cases with
          | zero => exact he0
          | succ j =>
            have htail : Fin.tail h ∈ H0 := by
              cases h0v : h 0
              · simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
                have : consBool false (Fin.tail h) = h := by rw [← h0v]; exact Fin.cons_self_tail h
                rw [this]; exact hh
              · have h1m : Fin.tail h ∈ H1 := by
                  simp only [H1, Finset.mem_filter, Finset.mem_univ, true_and]
                  have : consBool true (Fin.tail h) = h := by rw [← h0v]; exact Fin.cons_self_tail h
                  rw [this]; exact hh
                rw [hH1_bij] at h1m
                obtain ⟨v, hv, heqv⟩ := Finset.mem_map.mp h1m
                rw [← heqv]
                exact hH0_sub.2 hstar hh0 v hv
            have hstd : stdBasis j ∈ H0 := hH0c (Fin.tail h) htail j hi
            have hstd' : consBool false (stdBasis j) ∈ H := (Finset.mem_filter.mp hstd).2
            rwa [hcons_std j] at hstd'
        have hmem := coordSubgroup_mem_iff hH0_sub hH0c
        dsimp only at hmem
        have hex_q : ∃ q₀ : Fin m, stdBasis q₀ ∉ H0 ∧ hstar q₀ = true := by
          by_contra hall
          push Not at hall
          apply hhstar_not
          rw [hmem]
          intro i hi
          have hnot : stdBasis i ∉ H0 := fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
          have hne := hall i hnot
          exact Bool.eq_false_iff.mpr hne
        obtain ⟨q₀, hq₀_not, hq₀_t⟩ := hex_q
        refine ⟨k + 1, by omega, ?_, fun c => ?_⟩
        · rw [hsplitH, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
            hH0card, hH1card, pow_succ']
          omega
        · rw [hsum_split c]
          let S0 := ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))
          let S1 := ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)))
          let B := 3 ^ k * 2 ^ (m - k)
          have hS0_le : S0 ≤ B := hH0sum (Fin.tail c)
          have hS1_le : S1 ≤ B := hH0sum (fun j => xor (Fin.tail c j) (hstar j))
          have hhalf : 2 * S0 ≤ B ∨ 2 * S1 ≤ B := by
            cases hcq : Fin.tail c q₀
            · right
              have hx : xor (Fin.tail c q₀) (hstar q₀) = true := by rw [hcq, hq₀_t]; rfl
              exact coordSubgroup_half_wt_sum hH0_sub hH0c hH0card
                (fun j => xor (Fin.tail c j) (hstar j)) q₀ hq₀_not hx
            · left
              exact coordSubgroup_half_wt_sum hH0_sub hH0c hH0card (Fin.tail c) q₀ hq₀_not hcq
          have hsub : m + 1 - (k + 1) = m - k := by omega
          rw [hsub, pow_succ']
          have hrhs : 5 * (3 * 3 ^ k * 2 ^ (m - k)) = 15 * B := by dsimp only [B]; ring
          rw [hrhs]
          change 6 * ((if c 0 = false then 2 else 1) * S0 + (if c 0 = true then 2 else 1) * S1) ≤ 15 * B
          cases c 0 <;> rcases hhalf with h0 | h1 <;> simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true] <;> omega
      · obtain ⟨k, hkm, hH0card, hH0sum⟩ := ih H0 hH0_sub hH0c
        have hH1card : H1.card = 2 ^ k := by rw [hH1_bij, Finset.card_map, hH0card]
        refine ⟨k + 1, by omega, ?_, fun c => ?_⟩
        · rw [hsplitH, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
            hH0card, hH1card, pow_succ']
          omega
        · rw [hsum_split c]
          have hb0 := hH0sum (Fin.tail c)
          have hb1 := hH0sum (fun j => xor (Fin.tail c j) (hstar j))
          have hsub : m + 1 - (k + 1) = m - k := by omega
          rw [hsub, pow_succ']
          have hadd : (if c 0 = false then 2 else 1) + (if c 0 = true then 2 else 1) = 3 := by
            cases c 0 <;> rfl
          calc 6 * ((if c 0 = false then 2 else 1) *
                  (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) +
                (if c 0 = true then 2 else 1) *
                  (∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)))))
              = (if c 0 = false then 2 else 1) *
                  (6 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (Fin.tail c j) (u j)))) +
                (if c 0 = true then 2 else 1) *
                  (6 * ∑ u ∈ H0, 2 ^ (m - wt (fun j => xor (xor (Fin.tail c j) (hstar j)) (u j)))) := by ring
            _ ≤ (if c 0 = false then 2 else 1) * (5 * (3 ^ k * 2 ^ (m - k))) +
                (if c 0 = true then 2 else 1) * (5 * (3 ^ k * 2 ^ (m - k))) :=
                Nat.add_le_add (Nat.mul_le_mul_left _ hb0) (Nat.mul_le_mul_left _ hb1)
            _ = ((if c 0 = false then 2 else 1) + (if c 0 = true then 2 else 1)) *
                  (5 * (3 ^ k * 2 ^ (m - k))) := (Nat.add_mul ..).symm
            _ = 3 * (5 * (3 ^ k * 2 ^ (m - k))) := by rw [hadd]
            _ = 5 * (3 * 3 ^ k * 2 ^ (m - k)) := by ring

theorem two_bit_lin_zero (c d0 d1 : Bool) (h : d0 = true ∨ d1 = true) :
    (∑ u : Fin 2 → Bool, sgn (xor c (xor (d0 && u 0) (d1 && u 1)))) = 0 := by
  rcases h with rfl | rfl
  · cases c <;> cases d1 <;> decide
  · cases c <;> cases d0 <;> decide

theorem lane_u_factor_eq_zero (m : ℕ) (lane : Fin m → Fin 3)
    (Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool) (h : Fin m → Bool)
    (j₀ : Fin m) (hj₀ : h j₀ = false)
    (hd : par (∑ i : Fin m, (Bcoeff (j₀, otherIdx (lane j₀) 0) (i, lane i) && h i).toNat) = true ∨
          par (∑ i : Fin m, (Bcoeff (j₀, otherIdx (lane j₀) 1) (i, lane i) && h i).toNat) = true) :
    let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
      fun u p => mergeLane lane u (fun _ => false) p.1 p.2
    let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
      par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
    (∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)) = 0 := by
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
      ∏ j : Fin m, ∑ x : Fin 2 → Bool,
        sgn (xor (h j && (x 0 && x 1)) (xor (d0 j && x 0) (d1 j && x 1))) := by
    rw [← sum_prod_fin_fun]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hlin_u u, sgn_par_sum]
  rw [hcongr]
  refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
  rw [hj₀]
  have hzero := two_bit_lin_zero false (d0 j₀) (d1 j₀) hd
  simpa only [Bool.false_and, Bool.false_xor] using hzero

def sympComb {m s : ℕ} (e f : Fin s → (Fin m → Bool))
    (p : (Fin s → Bool) × (Fin s → Bool)) : Fin m → Bool :=
  fun i => par (∑ a : Fin s, ((p.1 a && e a i).toNat + (p.2 a && f a i).toNat))

theorem sympComb_cons {m s : ℕ} (e₀ f₀ : Fin m → Bool)
    (e' f' : Fin s → (Fin m → Bool))
    (x₀ y₀ : Bool) (x' y' : Fin s → Bool) :
    sympComb (Fin.cons (α := fun _ => Fin m → Bool) e₀ e')
             (Fin.cons (α := fun _ => Fin m → Bool) f₀ f')
             (Fin.cons (α := fun _ => Bool) x₀ x', Fin.cons (α := fun _ => Bool) y₀ y') =
    fun i => xor (sympComb e' f' (x', y') i) (xor (x₀ && e₀ i) (y₀ && f₀ i)) := by
  funext i
  dsimp only [sympComb]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [par_add, par_add, par_toNat, par_toNat]
  cases x₀ && e₀ i <;> cases y₀ && f₀ i <;>
    cases par (∑ a : Fin s, ((x' a && e' a i).toNat + (y' a && f' a i).toNat)) <;> rfl

theorem exists_symplectic_basis {m : ℕ} (B : (Fin m → Bool) → (Fin m → Bool) → Bool)
    (hself : ∀ x, B x x = false)
    (hsymm : ∀ x y, B x y = B y x)
    (hxor : ∀ x y z, B x (fun i => xor (y i) (z i)) = xor (B x y) (B x z)) :
    ∀ (s : ℕ) (V : Finset (Fin m → Bool)), IsSubgroup V → V.card = 2 ^ (2 * s) →
      (∀ h ∈ V, (∀ t ∈ V, B h t = false) → h = fun _ => false) →
      ∃ e f : Fin s → (Fin m → Bool),
        (∀ a, e a ∈ V ∧ f a ∈ V) ∧
        (∀ a b, B (e a) (e b) = false ∧ B (f a) (f b) = false ∧ B (e a) (f b) = decide (a = b)) ∧
        V = Finset.univ.image (sympComb e f) ∧
        Function.Injective (sympComb e f) := by
  intro s
  induction s with
  | zero =>
    intro V hV hVcard _
    have hV0 : V = {fun _ => false} := by
      have hcard1 : V.card = 1 := by simpa using hVcard
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard1
      have h0 : (fun _ : Fin m => false) ∈ V := hV.1
      rw [hv, Finset.mem_singleton] at h0
      rw [hv, h0]
    refine ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a, ?_, ?_⟩
    · rw [hV0]
      ext v
      simp only [Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro rfl
        refine ⟨(Fin.elim0, Fin.elim0), ?_⟩
        funext i; simp [sympComb, par]
      · rintro ⟨_, rfl⟩
        funext i; simp [sympComb, par]
    · intro p₁ p₂ _
      apply Prod.ext <;> funext a <;> exact Fin.elim0 a
  | succ s ih =>
    intro V hV hVcard hnondeg
    have hB0 : ∀ x, B x (fun _ => false) = false := fun x => by
      have := hxor x (fun _ => false) (fun _ => false)
      have h0 : (fun _ : Fin m => xor false false) = (fun _ : Fin m => false) := rfl
      rw [h0] at this
      cases h : B x (fun _ => false) <;> simp_all
    have hB_scale : ∀ (x y : Fin m → Bool) (c : Bool),
        B x (fun i => c && y i) = (c && B x y) := fun x y c => by
      cases c <;> simp [hB0]
    have hgt1 : 1 < V.card := by
      rw [hVcard]
      have : 2 * (s + 1) = 2 * s + 2 := by omega
      rw [this, pow_add]
      have : 1 ≤ 2 ^ (2 * s) := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨e₀, he₀, he₀_ne⟩ : ∃ v ∈ V, v ≠ fun _ => false := by
      by_contra hall
      push Not at hall
      have hsub : V ⊆ {fun _ => false} := fun v hv => Finset.mem_singleton.mpr (hall v hv)
      have hle : V.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
      omega
    have hex_f₀ : ∃ f₀ ∈ V, B e₀ f₀ = true := by
      by_contra hall
      push Not at hall
      apply he₀_ne
      apply hnondeg e₀ he₀
      intro t ht
      cases hv : B e₀ t
      · rfl
      · exact absurd hv (hall t ht)
    obtain ⟨f₀, hf₀, hef⟩ := hex_f₀
    have hfe : B f₀ e₀ = true := by rw [hsymm, hef]
    let W : Finset (Fin m → Bool) := V.filter (fun w => B e₀ w = false ∧ B f₀ w = false)
    have hWsub : IsSubgroup W := by
      refine ⟨Finset.mem_filter.mpr ⟨hV.1, hB0 e₀, hB0 f₀⟩, fun a ha b hb => ?_⟩
      obtain ⟨haV, ha1, ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbV, hb1, hb2⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨hV.2 a haV b hbV,
        by rw [hxor, ha1, hb1]; rfl, by rw [hxor, ha2, hb2]; rfl⟩
    let comb : (Bool × Bool) × (Fin m → Bool) → (Fin m → Bool) :=
      fun p i => xor (p.2 i) (xor (p.1.1 && e₀ i) (p.1.2 && f₀ i))
    have hB_comb : ∀ (x : Fin m → Bool) (b₁ b₂ : Bool) (w : Fin m → Bool),
        B x (comb ((b₁, b₂), w)) = xor (B x w) (xor (b₁ && B x e₀) (b₂ && B x f₀)) := by
      intro x b₁ b₂ w
      change B x (fun i => xor (w i) (xor (b₁ && e₀ i) (b₂ && f₀ i))) = _
      rw [hxor, hxor, hB_scale, hB_scale]
    have hcomb_mem : ∀ b₁ b₂ : Bool, ∀ w ∈ V, comb ((b₁, b₂), w) ∈ V := by
      intro b₁ b₂ w hw
      have h1 : (fun i => b₁ && e₀ i) ∈ V := by
        cases b₁
        · simpa using hV.1
        · simpa using he₀
      have h2 : (fun i => b₂ && f₀ i) ∈ V := by
        cases b₂
        · simpa using hV.1
        · simpa using hf₀
      exact hV.2 w hw _ (hV.2 _ h1 _ h2)
    have hV_eq : V = ((Finset.univ : Finset (Bool × Bool)) ×ˢ W).image comb := by
      ext v
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · intro hv
        let b₁ := B f₀ v
        let b₂ := B e₀ v
        let w : Fin m → Bool := comb ((b₁, b₂), v)
        have hwV : w ∈ V := hcomb_mem b₁ b₂ v hv
        have hw1 : B e₀ w = false := by
          rw [hB_comb, hself, hef]; dsimp only [b₁, b₂]; cases B e₀ v <;> cases B f₀ v <;> rfl
        have hw2 : B f₀ w = false := by
          rw [hB_comb, hself, hfe]; dsimp only [b₁, b₂]; cases B e₀ v <;> cases B f₀ v <;> rfl
        refine ⟨((b₁, b₂), w), Finset.mem_filter.mpr ⟨hwV, hw1, hw2⟩, ?_⟩
        funext i; dsimp only [comb, w]
        cases v i <;> cases b₁ <;> cases b₂ <;> cases e₀ i <;> cases f₀ i <;> rfl
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
        have := congrArg (B f₀) heq
        rw [hB_comb, hB_comb, hw12, hw22, hfe, hself] at this
        simpa using this
      have hb2 : a₂ = b₂ := by
        have := congrArg (B e₀) heq
        rw [hB_comb, hB_comb, hw11, hw21, hef, hself] at this
        simpa using this
      subst hb1; subst hb2
      congr 1
      funext i
      have hi := congrFun heq i
      dsimp only [comb] at hi
      revert hi
      cases w₁ i <;> cases w₂ i <;> cases a₁ <;> cases a₂ <;> cases e₀ i <;> cases f₀ i <;> simp
    have hWcard : W.card = 2 ^ (2 * s) := by
      have hcard4 : V.card = 4 * W.card := by
        rw [hV_eq, Finset.card_image_of_injOn hcomb_inj, Finset.card_product]
        have : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
        rw [this]
      have hpow : 2 ^ (2 * (s + 1)) = 4 * 2 ^ (2 * s) := by
        have : 2 * (s + 1) = 2 * s + 2 := by omega
        rw [this, pow_add]; ring
      omega
    have hWnondeg : ∀ h ∈ W, (∀ t ∈ W, B h t = false) → h = fun _ => false := by
      intro h hh hht
      obtain ⟨hhV, hh1, hh2⟩ := Finset.mem_filter.mp hh
      apply hnondeg h hhV
      intro t ht
      rw [hV_eq] at ht
      obtain ⟨⟨⟨b₁, b₂⟩, w⟩, hw, rfl⟩ := Finset.mem_image.mp ht
      have hwW : w ∈ W := (Finset.mem_product.mp hw).2
      rw [hB_comb, hht w hwW, hsymm h e₀, hh1, hsymm h f₀, hh2]
      cases b₁ <;> cases b₂ <;> rfl
    obtain ⟨e', f', hmem', hB', hWeq, hinj'⟩ := ih W hWsub hWcard hWnondeg
    let e : Fin (s + 1) → (Fin m → Bool) := Fin.cons e₀ e'
    let f : Fin (s + 1) → (Fin m → Bool) := Fin.cons f₀ f'
    refine ⟨e, f, ?_, ?_, ?_, ?_⟩
    · intro a
      cases a using Fin.cases with
      | zero => exact ⟨he₀, hf₀⟩
      | succ k => exact ⟨(Finset.mem_filter.mp (hmem' k).1).1, (Finset.mem_filter.mp (hmem' k).2).1⟩
    · intro a b
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero =>
          dsimp only [e, f]
          simp only [Fin.cons_zero, decide_true]
          exact ⟨hself e₀, hself f₀, hef⟩
        | succ k =>
          have hek := Finset.mem_filter.mp (hmem' k).1
          have hfk := Finset.mem_filter.mp (hmem' k).2
          dsimp only [e, f]
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨hek.2.1, hfk.2.2, by rw [hfk.2.1]; simp [eq_comm, Fin.succ_ne_zero]⟩
      | succ j =>
        have hej := Finset.mem_filter.mp (hmem' j).1
        have hfj := Finset.mem_filter.mp (hmem' j).2
        cases b using Fin.cases with
        | zero =>
          dsimp only [e, f]
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨by rw [hsymm]; exact hej.2.1, by rw [hsymm]; exact hfj.2.2,
            by rw [hsymm, hej.2.2]; simp [Fin.succ_ne_zero]⟩
        | succ k =>
          obtain ⟨h1, h2, h3⟩ := hB' j k
          dsimp only [e, f]
          simp only [Fin.cons_succ]
          exact ⟨h1, h2, by simpa using h3⟩
    · rw [hV_eq]
      ext v
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨x₀, y₀⟩, w⟩, hw, rfl⟩
        rw [hWeq] at hw
        obtain ⟨⟨x', y'⟩, _, rfl⟩ := Finset.mem_image.mp hw
        refine ⟨(Fin.cons x₀ x', Fin.cons y₀ y'), ?_⟩
        exact sympComb_cons e₀ f₀ e' f' x₀ y₀ x' y'
      · rintro ⟨⟨x, y⟩, rfl⟩
        have hxe : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
        have hye : y = Fin.cons (y 0) (Fin.tail y) := (Fin.cons_self_tail y).symm
        refine ⟨((x 0, y 0), sympComb e' f' (Fin.tail x, Fin.tail y)), ?_, ?_⟩
        · rw [hWeq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · conv_rhs => rw [hxe, hye]
          exact (sympComb_cons e₀ f₀ e' f' (x 0) (y 0) (Fin.tail x) (Fin.tail y)).symm
    · intro p₁ p₂ heq
      rcases p₁ with ⟨x₁, y₁⟩
      rcases p₂ with ⟨x₂, y₂⟩
      have hx1 : x₁ = Fin.cons (x₁ 0) (Fin.tail x₁) := (Fin.cons_self_tail x₁).symm
      have hy1 : y₁ = Fin.cons (y₁ 0) (Fin.tail y₁) := (Fin.cons_self_tail y₁).symm
      have hx2 : x₂ = Fin.cons (x₂ 0) (Fin.tail x₂) := (Fin.cons_self_tail x₂).symm
      have hy2 : y₂ = Fin.cons (y₂ 0) (Fin.tail y₂) := (Fin.cons_self_tail y₂).symm
      rw [hx1, hy1, hx2, hy2, sympComb_cons, sympComb_cons] at heq
      have hmem1 : ((x₁ 0, y₁ 0), sympComb e' f' (Fin.tail x₁, Fin.tail y₁)) ∈
          ((Finset.univ : Finset (Bool × Bool)) ×ˢ W) :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, by rw [hWeq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      have hmem2 : ((x₂ 0, y₂ 0), sympComb e' f' (Fin.tail x₂, Fin.tail y₂)) ∈
          ((Finset.univ : Finset (Bool × Bool)) ×ˢ W) :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, by rw [hWeq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
      have hinj_c := hcomb_inj hmem1 hmem2 heq
      have h0eq : (x₁ 0, y₁ 0) = (x₂ 0, y₂ 0) := (Prod.ext_iff.mp hinj_c).1
      have hteq : (Fin.tail x₁, Fin.tail y₁) = (Fin.tail x₂, Fin.tail y₂) :=
        hinj' (Prod.ext_iff.mp hinj_c).2
      have hx0 : x₁ 0 = x₂ 0 := (Prod.ext_iff.mp h0eq).1
      have hy0 : y₁ 0 = y₂ 0 := (Prod.ext_iff.mp h0eq).2
      have hxt : Fin.tail x₁ = Fin.tail x₂ := (Prod.ext_iff.mp hteq).1
      have hyt : Fin.tail y₁ = Fin.tail y₂ := (Prod.ext_iff.mp hteq).2
      apply Prod.ext
      · dsimp only; rw [hx1, hx2, hx0, hxt]
      · dsimp only; rw [hy1, hy2, hy0, hyt]

theorem sum_quad_symplectic {m s : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R)
    (e f : Fin s → (Fin m → Bool))
    (hB : ∀ a b, polar R (e a) (e b) = false ∧ polar R (f a) (f b) = false ∧
      polar R (e a) (f b) = decide (a = b))
    (hsurj : Finset.univ = Finset.univ.image (sympComb e f))
    (hinj : Function.Injective (sympComb e f))
    (α : Fin m → Bool) :
    let re : Fin s → Bool := fun a => xor (R (e a)) (R (fun _ => false))
    let rf : Fin s → Bool := fun a => xor (R (f a)) (R (fun _ => false))
    (∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))) =
      (2 ^ s : ℤ) * sgn (xor (R (fun _ => false))
        (par (∑ a : Fin s, (xor (linGen α (e a)) (re a) && xor (linGen α (f a)) (rf a)).toNat))) := by
  intro re rf
  let term : Fin s → Bool → Bool → (Fin m → Bool) :=
    fun a x y i => xor (x && e a i) (y && f a i)
  have hpol0 : ∀ v : Fin m → Bool, polar R v (fun _ => false) = false := fun v => by
    unfold polar
    have : (fun i => xor (v i) false) = v := by funext i; simp
    rw [this]; cases R v <;> cases R (fun _ => false) <;> rfl
  have hpol_scale : ∀ (u v : Fin m → Bool) (c : Bool),
      polar R u (fun i => c && v i) = (c && polar R u v) := fun u v c => by
    cases c <;> simp [hpol0]
  have hpol_term : ∀ a b x₁ y₁ x₂ y₂, a ≠ b →
      polar R (term a x₁ y₁) (term b x₂ y₂) = false := by
    intro a b x₁ y₁ x₂ y₂ hab
    have h1 : polar R (e a) (term b x₂ y₂) = false := by
      dsimp only [term]
      rw [polar_xor_right hR, hpol_scale, hpol_scale, (hB a b).1, (hB a b).2.2]
      simp [hab]
    have h2 : polar R (f a) (term b x₂ y₂) = false := by
      dsimp only [term]
      rw [polar_xor_right hR, hpol_scale, hpol_scale, polar_symm R (f a) (e b),
        (hB b a).2.2, (hB a b).2.1]
      simp [hab.symm]
    dsimp only [term]
    rw [polar_xor_left hR, polar_symm, hpol_scale, polar_symm, h1,
        polar_symm _ (fun i => y₁ && f a i), hpol_scale, polar_symm, h2]
    simp
  have hR_term : ∀ a x y,
      R (term a x y) = xor (R (fun _ => false))
        (xor (x && y) (xor (re a && x) (rf a && y))) := by
    intro a x y
    cases x <;> cases y
    · have : term a false false = fun _ => false := by funext i; simp [term]
      rw [this]; simp
    · have : term a false true = f a := by funext i; simp [term]
      rw [this]; simp only [Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.false_xor]
      dsimp only [rf]; cases R (f a) <;> cases R (fun _ => false) <;> rfl
    · have : term a true false = e a := by funext i; simp [term]
      rw [this]; simp only [Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.false_xor]
      dsimp only [re]; cases R (e a) <;> cases R (fun _ => false) <;> rfl
    · have heq : term a true true = fun i => xor (e a i) (f a i) := by funext i; simp [term]
      rw [heq, quad_add_expand R (e a) (f a), (hB a a).2.2]
      simp only [decide_true, Bool.and_true]
      dsimp only [re, rf]
      cases R (e a) <;> cases R (f a) <;> cases R (fun _ => false) <;> rfl
  have hR_sub : ∀ (T : Finset (Fin s)) (x y : Fin s → Bool),
      R (fun i => par (∑ a ∈ T, (term a (x a) (y a) i).toNat)) =
      xor (R (fun _ => false))
        (par (∑ a ∈ T, (xor (x a && y a) (xor (re a && x a) (rf a && y a))).toNat)) := by
    classical
    intro T x y
    induction T using Finset.induction_on with
    | empty =>
      have : (fun i : Fin m => par (∑ a ∈ (∅ : Finset (Fin s)), (term a (x a) (y a) i).toNat)) =
          fun _ => false := by funext i; simp [par]
      rw [this]; simp [par]
    | insert a T ha ih =>
      let vT : Fin m → Bool := fun i => par (∑ b ∈ T, (term b (x b) (y b) i).toNat)
      have hvec : (fun i => par (∑ b ∈ insert a T, (term b (x b) (y b) i).toNat)) =
          fun i => xor (term a (x a) (y a) i) (vT i) := by
        funext i
        rw [Finset.sum_insert ha, par_add, par_toNat]
      have hpol_T : polar R (term a (x a) (y a)) vT = false := by
        have hgen : ∀ U : Finset (Fin s), a ∉ U →
            polar R (term a (x a) (y a)) (fun i => par (∑ b ∈ U, (term b (x b) (y b) i).toNat)) = false := by
          intro U
          induction U using Finset.induction_on with
          | empty => intro _; simpa [par] using hpol0 (term a (x a) (y a))
          | insert b U hb ihU =>
            intro haU
            have hab : a ≠ b := fun h => haU (h ▸ Finset.mem_insert_self b U)
            have haU' : a ∉ U := fun h => haU (Finset.mem_insert_of_mem h)
            have hstep : (fun i => par (∑ c ∈ insert b U, (term c (x c) (y c) i).toNat)) =
                fun i => xor (term b (x b) (y b) i) (par (∑ c ∈ U, (term c (x c) (y c) i).toNat)) := by
              funext i; rw [Finset.sum_insert hb, par_add, par_toNat]
            rw [hstep, polar_xor_right hR, hpol_term a b _ _ _ _ hab, ihU haU']
            rfl
        exact hgen T ha
      rw [hvec, quad_add_expand R (term a (x a) (y a)) vT, hpol_T, hR_term a (x a) (y a), ih,
        Finset.sum_insert ha, par_add, par_toNat]
      cases R (fun _ => false) <;>
        cases xor (x a && y a) (xor (re a && x a) (rf a && y a)) <;>
        cases par (∑ b ∈ T, (xor (x b && y b) (xor (re b && x b) (rf b && y b))).toNat) <;> rfl
  have hsymp_eq : ∀ p : (Fin s → Bool) × (Fin s → Bool),
      sympComb e f p = fun i => par (∑ a : Fin s, (term a (p.1 a) (p.2 a) i).toNat) := by
    intro ⟨x, y⟩
    funext i
    dsimp only [sympComb, term]
    refine par_sum_congr_mod Finset.univ _ _ fun a _ => ?_
    cases x a && e a i <;> cases y a && f a i <;> rfl
  have hlin_symp : ∀ p : (Fin s → Bool) × (Fin s → Bool),
      linGen α (sympComb e f p) =
      par (∑ a : Fin s, (xor (linGen α (e a) && p.1 a) (linGen α (f a) && p.2 a)).toNat) := by
    intro ⟨x, y⟩
    rw [hsymp_eq (x, y)]
    have hgen : ∀ U : Finset (Fin s),
        linGen α (fun i => par (∑ a ∈ U, (term a (x a) (y a) i).toNat)) =
        par (∑ a ∈ U, (xor (linGen α (e a) && x a) (linGen α (f a) && y a)).toNat) := by
      classical
      intro U
      induction U using Finset.induction_on with
      | empty =>
        have : (fun i : Fin m => par (∑ a ∈ (∅ : Finset (Fin s)), (term a (x a) (y a) i).toNat)) =
            fun _ => false := by funext i; simp [par]
        rw [this, linGen_zero]; simp [par]
      | insert a U ha ihU =>
        have hstep : (fun i => par (∑ b ∈ insert a U, (term b (x b) (y b) i).toNat)) =
            fun i => xor (term a (x a) (y a) i) (par (∑ b ∈ U, (term b (x b) (y b) i).toNat)) := by
          funext i; rw [Finset.sum_insert ha, par_add, par_toNat]
        have hlin_t : linGen α (term a (x a) (y a)) =
            xor (linGen α (e a) && x a) (linGen α (f a) && y a) := by
          dsimp only [term]
          rw [linGen_xor]
          have hsc : ∀ (v : Fin m → Bool) (c : Bool), linGen α (fun i => c && v i) = (linGen α v && c) := fun v c => by
            cases c <;> simp [linGen_zero]
          rw [hsc, hsc]
        rw [hstep, linGen_xor, hlin_t, ihU, Finset.sum_insert ha, par_add, par_toNat]
    exact hgen Finset.univ
  have hsum_img : (∑ z : Fin m → Bool, sgn (xor (R z) (linGen α z))) =
      ∑ p : (Fin s → Bool) × (Fin s → Bool), sgn (xor (R (sympComb e f p)) (linGen α (sympComb e f p))) := by
    conv_lhs => rw [hsurj]
    exact Finset.sum_image (fun a _ b _ h => hinj h)
  rw [hsum_img]
  have hpt : ∀ p : (Fin s → Bool) × (Fin s → Bool),
      sgn (xor (R (sympComb e f p)) (linGen α (sympComb e f p))) =
      sgn (R (fun _ => false)) *
        ∏ a : Fin s, sgn (xor (p.1 a && p.2 a)
          (xor (xor (linGen α (e a)) (re a) && p.1 a) (xor (linGen α (f a)) (rf a) && p.2 a))) := by
    intro ⟨x, y⟩
    rw [hsymp_eq (x, y), hR_sub Finset.univ x y, ← hsymp_eq (x, y), hlin_symp (x, y)]
    rw [Bool.xor_assoc, ← par_sum_xor, sgn_xor, sgn_par_sum]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    dsimp only
    cases x a <;> cases y a <;> cases re a <;> cases rf a <;>
      cases linGen α (e a) <;> cases linGen α (f a) <;> rfl
  simp_rw [hpt, ← Finset.mul_sum]
  let eqPair : ((Fin s → Bool) × (Fin s → Bool)) ≃ (Fin s → Fin 2 → Bool) :=
    { toFun := fun p a k => if k = 0 then p.1 a else p.2 a
      invFun := fun q => (fun a => q a 0, fun a => q a 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun q => by funext a k; fin_cases k <;> rfl }
  have hfact : (∑ p : (Fin s → Bool) × (Fin s → Bool),
      ∏ a : Fin s, sgn (xor (p.1 a && p.2 a)
        (xor (xor (linGen α (e a)) (re a) && p.1 a) (xor (linGen α (f a)) (rf a) && p.2 a)))) =
      ∏ a : Fin s, ∑ q : Fin 2 → Bool,
        sgn (xor (q 0 && q 1)
          (xor (xor (linGen α (e a)) (re a) && q 0) (xor (linGen α (f a)) (rf a) && q 1))) := by
    rw [← sum_prod_fin_fun]
    refine Fintype.sum_equiv eqPair _ _ fun p => ?_
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [eqPair]
  rw [hfact]
  have h2bit : ∀ a : Fin s,
      (∑ q : Fin 2 → Bool, sgn (xor (q 0 && q 1)
        (xor (xor (linGen α (e a)) (re a) && q 0) (xor (linGen α (f a)) (rf a) && q 1)))) =
      2 * sgn (xor (linGen α (e a)) (re a) && xor (linGen α (f a)) (rf a)) := fun a => by
    have := two_bit_quad_exact false (xor (linGen α (e a)) (re a)) (xor (linGen α (f a)) (rf a))
    simpa only [Bool.false_xor] using this
  simp_rw [h2bit, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← sgn_par_sum, sgn_xor]
  ring

theorem par_sum_deg4_monom :
    par (∑ v : Fin 2 → Fin 2 → Bool, (v 0 0 && v 0 1 && v 1 0 && v 1 1).toNat) = true := by
  have h1 : (∑ v : Fin 2 → Fin 2 → Bool, (v 0 0 && v 0 1 && v 1 0 && v 1 1).toNat) = 1 := by
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

theorem par_sum_quad_deg2_false (b : Bool) (l : (Fin 2 × Fin 2) → Bool)
    (a : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Bool) :
    par (∑ v : Fin 2 → Fin 2 → Bool,
      (xor (xor b (par (∑ p : Fin 2 × Fin 2, (l p && v p.1 p.2).toNat)))
        (par (∑ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
          (a p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat))).toNat) = false := by
  rw [par_sum_xor, par_sum_xor]
  have h0 : par (∑ _v : Fin 2 → Fin 2 → Bool, b.toNat) = false :=
    par_sum_indep_four (fun _ => b) (0, 0) (fun _ => rfl)
  have h1 : par (∑ v : Fin 2 → Fin 2 → Bool,
      (par (∑ p : Fin 2 × Fin 2, (l p && v p.1 p.2).toNat)).toNat) = false := by
    rw [par_sum_par_comm (fun (v : Fin 2 → Fin 2 → Bool) (p : Fin 2 × Fin 2) => l p && v p.1 p.2)]
    have hz : ∀ p : Fin 2 × Fin 2, par (∑ v : Fin 2 → Fin 2 → Bool, (l p && v p.1 p.2).toNat) = false := fun p => by
      have := par_sum_monom3_false (l p) p p p
      simpa [Bool.and_assoc, Bool.and_self] using this
    simp_rw [hz]; simp [par]
  have h2 : par (∑ v : Fin 2 → Fin 2 → Bool,
      (par (∑ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
        (a p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat)).toNat) = false := by
    rw [par_sum_par_comm (fun (v : Fin 2 → Fin 2 → Bool) (p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) =>
      a p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2)]
    have hz : ∀ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
        par (∑ v : Fin 2 → Fin 2 → Bool, (a p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat) = false := fun p => by
      have := par_sum_monom3_false (a p.1 p.2) p.1 p.2 p.2
      simpa [Bool.and_assoc, Bool.and_self] using this
    simp_rw [hz]; simp [par]
  rw [h0, h1, h2]; rfl

theorem bool_expand_quad_pair : ∀ c1 c2 d1 d2 p0 p1 a b : Bool,
    ((xor (xor (c1 && p0) (c2 && p1)) a) && (xor (xor (d1 && p0) (d2 && p1)) b)) =
    xor (xor ((xor (c1 && d2) (c2 && d1)) && (p0 && p1))
             (xor ((c1 && d1) && p0) ((c2 && d2) && p1)))
        (xor (xor (c1 && p0 && b) (c2 && p1 && b))
             (xor (xor (d1 && p0 && a) (d2 && p1 && a)) (a && b))) := by
  decide

theorem par_sum_pair_aff_false (c r0 : Bool) (p₁ p₂ : Fin 2 × Fin 2)
    (mL : (Fin 2 × Fin 2) → Bool) :
    par (∑ v : Fin 2 → Fin 2 → Bool,
      (c && (v p₁.1 p₁.2 && v p₂.1 p₂.2) &&
        xor r0 (par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat))).toNat) = false := by
  have hpt : ∀ v : Fin 2 → Fin 2 → Bool,
      (c && (v p₁.1 p₁.2 && v p₂.1 p₂.2) &&
        xor r0 (par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat))) =
      xor (c && r0 && v p₁.1 p₁.2 && v p₂.1 p₂.2)
          (par (∑ p : Fin 2 × Fin 2,
            (c && mL p && v p.1 p.2 && v p₁.1 p₁.2 && v p₂.1 p₂.2).toNat)) := by
    intro v
    have hmul_b : ∀ (b : Bool) (f : (Fin 2 × Fin 2) → Bool),
        (b && par (∑ p : Fin 2 × Fin 2, (f p).toNat)) =
        par (∑ p : Fin 2 × Fin 2, (b && f p).toNat) := fun b f => by
      cases b <;> simp [par]
    have h1 : (c && (v p₁.1 p₁.2 && v p₂.1 p₂.2) &&
        xor r0 (par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat))) =
        xor (c && r0 && v p₁.1 p₁.2 && v p₂.1 p₂.2)
            ((c && (v p₁.1 p₁.2 && v p₂.1 p₂.2)) &&
              par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat)) := by
      cases c <;> cases r0 <;> cases v p₁.1 p₁.2 <;> cases v p₂.1 p₂.2 <;>
        cases par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat) <;> rfl
    rw [h1, hmul_b]
    refine congrArg (xor _) (congrArg par (Finset.sum_congr rfl fun p _ => congrArg Bool.toNat ?_))
    cases c <;> cases mL p <;> cases v p.1 p.2 <;> cases v p₁.1 p₁.2 <;> cases v p₂.1 p₂.2 <;> rfl
  simp_rw [hpt]
  rw [par_sum_xor]
  have ha : par (∑ v : Fin 2 → Fin 2 → Bool, (c && r0 && v p₁.1 p₁.2 && v p₂.1 p₂.2).toNat) = false := by
    have := par_sum_monom3_false (c && r0) p₁ p₂ p₂
    simpa [Bool.and_assoc, Bool.and_self] using this
  have hb : par (∑ v : Fin 2 → Fin 2 → Bool,
      (par (∑ p : Fin 2 × Fin 2,
        (c && mL p && v p.1 p.2 && v p₁.1 p₁.2 && v p₂.1 p₂.2).toNat)).toNat) = false := by
    rw [par_sum_par_comm (fun (v : Fin 2 → Fin 2 → Bool) (p : Fin 2 × Fin 2) =>
      c && mL p && v p.1 p.2 && v p₁.1 p₁.2 && v p₂.1 p₂.2)]
    have hz : ∀ p : Fin 2 × Fin 2,
        par (∑ v : Fin 2 → Fin 2 → Bool,
          (c && mL p && v p.1 p.2 && v p₁.1 p₁.2 && v p₂.1 p₂.2).toNat) = false := fun p =>
      par_sum_monom3_false (c && mL p) p p₁ p₂
    simp_rw [hz]; simp [par]
  rw [ha, hb]; rfl

theorem par_sum_aff_prod_false (a0 b0 : Bool) (mA mB : (Fin 2 × Fin 2) → Bool) :
    par (∑ v : Fin 2 → Fin 2 → Bool,
      (xor a0 (par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat)) &&
       xor b0 (par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat))).toNat) = false := by
  have hpt : ∀ v : Fin 2 → Fin 2 → Bool,
      (xor a0 (par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat)) &&
       xor b0 (par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat))) =
      xor (xor (a0 && b0)
               (par (∑ p : Fin 2 × Fin 2, ((xor (a0 && mB p) (b0 && mA p)) && v p.1 p.2).toNat)))
          (par (∑ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
            ((mA p.1 && mB p.2) && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat)) := by
    intro v
    have hmul_and : ∀ (x y : ℕ), (par x && par y) = par (x * y) := fun x y => by
      unfold par
      have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [Nat.mul_mod, hx, hy]
    have hprod : (∑ p₁ : Fin 2 × Fin 2, (mA p₁ && v p₁.1 p₁.2).toNat) *
        (∑ p₂ : Fin 2 × Fin 2, (mB p₂ && v p₂.1 p₂.2).toNat) =
        ∑ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
          ((mA p.1 && mB p.2) && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat := by
      rw [Finset.sum_mul, Fintype.sum_prod_type (fun p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
        ((mA p.1 && mB p.2) && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat)]
      refine Finset.sum_congr rfl fun p₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p₂ _ => ?_
      cases mA p₁ <;> cases mB p₂ <;> cases v p₁.1 p₁.2 <;> cases v p₂.1 p₂.2 <;> rfl
    have hmul_c : ∀ (c : Bool) (f : (Fin 2 × Fin 2) → Bool),
        (c && par (∑ p : Fin 2 × Fin 2, (f p).toNat)) =
        par (∑ p : Fin 2 × Fin 2, (c && f p).toNat) := fun c f => by
      cases c <;> simp [par]
    have h1 : (xor a0 (par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat)) &&
        xor b0 (par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat))) =
        xor (xor (a0 && b0)
                 (xor (a0 && par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat))
                      (b0 && par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat))))
            (par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat) &&
             par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat)) := by
      cases a0 <;> cases b0 <;>
        cases par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat) <;>
        cases par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat) <;> rfl
    rw [h1, hmul_c, hmul_c, ← par_sum_xor, hmul_and, hprod]
    refine congrArg (fun x => xor (xor (a0 && b0) x) _)
      (congrArg par (Finset.sum_congr rfl fun p _ => congrArg Bool.toNat ?_))
    cases a0 <;> cases b0 <;> cases mA p <;> cases mB p <;> cases v p.1 p.2 <;> rfl
  simp_rw [hpt]
  exact par_sum_quad_deg2_false (a0 && b0) (fun p => xor (a0 && mB p) (b0 && mA p))
    (fun p₁ p₂ => mA p₁ && mB p₂)

theorem par_sum_prod_pair_quad (c1 c2 d1 d2 a0 b0 : Bool)
    (mA mB : (Fin 2 × Fin 2) → Bool) :
    let A : (Fin 2 → Fin 2 → Bool) → Bool := fun v =>
      xor a0 (par (∑ p : Fin 2 × Fin 2, (mA p && v p.1 p.2).toNat))
    let B : (Fin 2 → Fin 2 → Bool) → Bool := fun v =>
      xor b0 (par (∑ p : Fin 2 × Fin 2, (mB p && v p.1 p.2).toNat))
    par (∑ v : Fin 2 → Fin 2 → Bool,
      ((xor (xor (c1 && (v 0 0 && v 0 1)) (c2 && (v 1 0 && v 1 1))) (A v)) &&
       (xor (xor (d1 && (v 0 0 && v 0 1)) (d2 && (v 1 0 && v 1 1))) (B v))).toNat) =
    xor (c1 && d2) (c2 && d1) := by
  intro A B
  let P0 : (Fin 2 → Fin 2 → Bool) → Bool := fun v => v 0 0 && v 0 1
  let P1 : (Fin 2 → Fin 2 → Bool) → Bool := fun v => v 1 0 && v 1 1
  have hexp : ∀ v : Fin 2 → Fin 2 → Bool,
      ((xor (xor (c1 && P0 v) (c2 && P1 v)) (A v)) &&
       (xor (xor (d1 && P0 v) (d2 && P1 v)) (B v))) =
      xor (xor ((xor (c1 && d2) (c2 && d1)) && (v 0 0 && v 0 1 && v 1 0 && v 1 1))
               (xor ((c1 && d1) && P0 v) ((c2 && d2) && P1 v)))
          (xor (xor (c1 && P0 v && B v) (c2 && P1 v && B v))
               (xor (xor (d1 && P0 v && A v) (d2 && P1 v && A v)) (A v && B v))) := by
    intro v
    have h4 : (P0 v && P1 v) = (v 0 0 && v 0 1 && v 1 0 && v 1 1) := by
      dsimp only [P0, P1]; simp only [Bool.and_assoc]
    rw [← h4]
    exact bool_expand_quad_pair c1 c2 d1 d2 (P0 v) (P1 v) (A v) (B v)
  change par (∑ v : Fin 2 → Fin 2 → Bool,
    ((xor (xor (c1 && P0 v) (c2 && P1 v)) (A v)) &&
     (xor (xor (d1 && P0 v) (d2 && P1 v)) (B v))).toNat) = _
  simp_rw [hexp]
  rw [par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor, par_sum_xor]
  have hmain : par (∑ v : Fin 2 → Fin 2 → Bool,
      ((xor (c1 && d2) (c2 && d1)) && (v 0 0 && v 0 1 && v 1 0 && v 1 1)).toNat) =
      xor (c1 && d2) (c2 && d1) := by
    cases hcd : xor (c1 && d2) (c2 && d1)
    · simp [par]
    · simpa using par_sum_deg4_monom
  have hp0 : par (∑ v : Fin 2 → Fin 2 → Bool, ((c1 && d1) && P0 v).toNat) = false := by
    have := par_sum_monom3_false (c1 && d1) (0, 0) (0, 1) (0, 1)
    simpa [P0, Bool.and_assoc, Bool.and_self] using this
  have hp1 : par (∑ v : Fin 2 → Fin 2 → Bool, ((c2 && d2) && P1 v).toNat) = false := by
    have := par_sum_monom3_false (c2 && d2) (1, 0) (1, 1) (1, 1)
    simpa [P1, Bool.and_assoc, Bool.and_self] using this
  rw [hmain, hp0, hp1,
      par_sum_pair_aff_false c1 b0 (0, 0) (0, 1) mB,
      par_sum_pair_aff_false c2 b0 (1, 0) (1, 1) mB,
      par_sum_pair_aff_false d1 a0 (0, 0) (0, 1) mA,
      par_sum_pair_aff_false d2 a0 (1, 0) (1, 1) mA,
      par_sum_aff_prod_false a0 b0 mA mB]
  cases xor (c1 && d2) (c2 && d1) <;> rfl

theorem polar_eq_linGen_basis {m : ℕ} (R : (Fin m → Bool) → Bool) (hR : IsQuadGen R)
    (u v : Fin m → Bool) :
    polar R u v = linGen (fun i => polar R u (stdBasis i)) v := by
  have hpol0 : polar R u (fun _ => false) = false := by
    unfold polar
    have : (fun i => xor (u i) false) = u := by funext i; simp
    rw [this]; cases R u <;> cases R (fun _ => false) <;> rfl
  have hgen : ∀ S : Finset (Fin m),
      polar R u (vecOf S) = par (∑ i ∈ S, (polar R u (stdBasis i)).toNat) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : vecOf (∅ : Finset (Fin m)) = fun _ => false := by funext i; simp [vecOf]
      rw [this, hpol0]; simp [par]
    | insert a S ha ih =>
      have heq : vecOf (insert a S) = fun i => xor (stdBasis a i) (vecOf S i) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [vecOf, stdBasis, ha]
        · simp [vecOf, stdBasis, hi]
      rw [heq, polar_xor_right hR, ih, Finset.sum_insert ha, par_add, par_toNat]
  let Sv : Finset (Fin m) := Finset.univ.filter (fun i => v i = true)
  have hv : v = vecOf Sv := by
    funext i
    simp only [vecOf, Sv, Finset.mem_filter, Finset.mem_univ, true_and]
    cases v i <;> rfl
  rw [hv, hgen Sv]
  unfold linGen
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [vecOf, Sv, Finset.mem_filter, Finset.mem_univ, true_and]
  cases v i <;> simp

theorem exists_symp_pair_M {m s : ℕ} (hs : 0 < s) (R : (Fin m → Bool) → Bool) (hRquad : IsQuadGen R)
    (e f : Fin s → (Fin m → Bool))
    (hB : ∀ a b, polar R (e a) (e b) = false ∧ polar R (f a) (f b) = false ∧
      polar R (e a) (f b) = decide (a = b)) :
    ∃ i₁ i₂ : Fin m, i₁ ≠ i₂ ∧
      par (∑ a : Fin s, (xor (e a i₁ && f a i₂) (e a i₂ && f a i₁)).toNat) = true := by
  let M : Fin m → Fin m → Bool := fun i j =>
    par (∑ a : Fin s, (xor (e a i && f a j) (e a j && f a i)).toNat)
  have hex_pair : ∃ i₁ i₂ : Fin m, i₁ ≠ i₂ ∧ M i₁ i₂ = true := by
    let a₀ : Fin s := ⟨0, hs⟩
    let hx : Fin m → Bool := fun i => polar R (e a₀) (stdBasis i)
    let hy : Fin m → Bool := fun j => polar R (f a₀) (stdBasis j)
    have hsum_true : par (∑ p : Fin m × Fin m, (M p.1 p.2 && hx p.1 && hy p.2).toNat) = true := by
      have h1 : ∀ p : Fin m × Fin m,
          (M p.1 p.2 && hx p.1 && hy p.2).toNat % 2 =
          (∑ a : Fin s, (xor (e a p.1 && f a p.2 && hx p.1 && hy p.2)
                             (e a p.2 && f a p.1 && hx p.1 && hy p.2)).toNat) % 2 := by
        intro ⟨i, j⟩
        cases hxi : hx i <;> cases hyj : hy j
        · simp
        · simp
        · simp
        · simp only [Bool.and_true, M, par]
          have hm : (∑ a : Fin s, (xor (e a i && f a j) (e a j && f a i)).toNat) % 2 = 0 ∨
              (∑ a : Fin s, (xor (e a i && f a j) (e a j && f a i)).toNat) % 2 = 1 := by omega
          rcases hm with hm | hm <;> simp [hm]
      rw [par_sum_congr_mod Finset.univ _ _ (fun p _ => h1 p), Finset.sum_comm]
      have hinner : ∀ a : Fin s,
          (∑ p : Fin m × Fin m, (xor (e a p.1 && f a p.2 && hx p.1 && hy p.2)
                                     (e a p.2 && f a p.1 && hx p.1 && hy p.2)).toNat) % 2 =
          (if a = a₀ then true else false).toNat % 2 := by
        intro a
        have hpar_eq : par (∑ p : Fin m × Fin m,
            (xor (e a p.1 && f a p.2 && hx p.1 && hy p.2)
                 (e a p.2 && f a p.1 && hx p.1 && hy p.2)).toNat) =
            if a = a₀ then true else false := by
          rw [par_sum_xor]
          have hmul : ∀ u v : Fin m → Bool,
              par (∑ p : Fin m × Fin m, (u p.1 && v p.2 && hx p.1 && hy p.2).toNat) =
              (linGen hx u && linGen hy v) := by
            intro u v
            have hprod : (∑ p : Fin m × Fin m, (u p.1 && v p.2 && hx p.1 && hy p.2).toNat) =
                (∑ i : Fin m, (hx i && u i).toNat) * (∑ j : Fin m, (hy j && v j).toNat) := by
              rw [Fintype.sum_prod_type, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              cases u i <;> cases v j <;> cases hx i <;> cases hy j <;> rfl
            rw [hprod]
            unfold linGen par
            have ha1 : (∑ i : Fin m, (hx i && u i).toNat) % 2 = 0 ∨
                (∑ i : Fin m, (hx i && u i).toNat) % 2 = 1 := by omega
            have hb1 : (∑ j : Fin m, (hy j && v j).toNat) % 2 = 0 ∨
                (∑ j : Fin m, (hy j && v j).toNat) % 2 = 1 := by omega
            rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;> simp [Nat.mul_mod, ha1, hb1]
          have hswap : (∑ p : Fin m × Fin m, (e a p.2 && f a p.1 && hx p.1 && hy p.2).toNat) =
              ∑ p : Fin m × Fin m, (f a p.1 && e a p.2 && hx p.1 && hy p.2).toNat := by
            refine Finset.sum_congr rfl fun p _ => ?_
            cases e a p.2 <;> cases f a p.1 <;> cases hx p.1 <;> cases hy p.2 <;> rfl
          rw [hswap, hmul (e a) (f a), hmul (f a) (e a)]
          rw [← polar_eq_linGen_basis R hRquad (e a₀) (e a),
              ← polar_eq_linGen_basis R hRquad (f a₀) (f a),
              ← polar_eq_linGen_basis R hRquad (e a₀) (f a),
              ← polar_eq_linGen_basis R hRquad (f a₀) (e a)]
          rw [(hB a₀ a).1, (hB a₀ a).2.1, (hB a₀ a).2.2, polar_symm R (f a₀) (e a), (hB a a₀).2.2]
          by_cases ha0 : a = a₀ <;> simp [ha0, eq_comm]
        have hmod2_helper : ∀ (n : ℕ) (b : Bool), par n = b → n % 2 = b.toNat % 2 := fun n b h => by
          unfold par at h
          have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
          rcases hm with hm | hm
          · rw [hm] at h ⊢; cases b <;> simp at h ⊢
          · rw [hm] at h ⊢; cases b <;> simp at h ⊢
        exact hmod2_helper _ _ hpar_eq
      rw [par_sum_congr_mod Finset.univ _ _ (fun a _ => hinner a)]
      exact par_sum_ite_eq Finset.univ a₀ (Finset.mem_univ _) true
    have hexp : ∃ p : Fin m × Fin m, M p.1 p.2 = true := by
      by_contra hall
      push Not at hall
      have hzero : ∀ p : Fin m × Fin m, (M p.1 p.2 && hx p.1 && hy p.2).toNat = 0 := fun p => by
        cases hM : M p.1 p.2
        · simp
        · exact absurd hM (hall p)
      simp_rw [hzero] at hsum_true
      simp [par] at hsum_true
    obtain ⟨⟨i₁, i₂⟩, hM12⟩ := hexp
    have hne : i₁ ≠ i₂ := by
      rintro rfl
      have hMii : M i₁ i₁ = false := by
        dsimp only [M]
        have hz : ∀ a : Fin s, (xor (e a i₁ && f a i₁) (e a i₁ && f a i₁)).toNat = 0 := fun a => by
          simp
        simp_rw [hz]; simp [par]
      rw [hMii] at hM12
      exact Bool.noConfusion hM12
    exact ⟨i₁, i₂, hne, hM12⟩
  exact hex_pair

theorem nondeg_lane_bound (s : ℕ) (hs : 0 < s) (q : (Fin (2 * s) → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin (2 * s) × Fin 3) → Bool)
      (a : (Fin (2 * s) × Fin 3) → (Fin (2 * s) × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin (2 * s) × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin (2 * s) × Fin 3, ∑ j : Fin (2 * s) × Fin 3,
          (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin (2 * s) → Fin 3)
    (hrad : ((Finset.univ : Finset (Fin (2 * s) → Bool)).filter (fun h => ∀ t : Fin (2 * s) → Bool,
      xor (xor (q (fun i j => (j == lane i) && xor (h i) (t i)))
               (q (fun i j => (j == lane i) && h i)))
          (xor (q (fun i j => (j == lane i) && t i))
               (q (fun i j => (j == lane i) && false))) = false)).card = 1) :
    8 * |∑ w : Fin (2 * s) → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin (2 * s), (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    7 * 2 ^ (5 * s) := by
  let m := 2 * s
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hRquad : IsQuadGen R := restrict_isQuadGen q hq lane
  have hnondeg : ∀ h ∈ (Finset.univ : Finset (Fin m → Bool)),
      (∀ t ∈ (Finset.univ : Finset (Fin m → Bool)), polar R h t = false) → h = fun _ => false := by
    intro h _ hpol
    let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
    have h0mem : (fun _ : Fin m => false) ∈ Rad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      unfold polar
      have : (fun i => xor false (t i)) = t := by funext i; simp
      rw [this]; cases R t <;> cases R (fun _ => false) <;> rfl
    have hhmem : h ∈ Rad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => hpol t (Finset.mem_univ t)⟩
    have hcard1 : Rad.card = 1 := hrad
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard1
    rw [hv, Finset.mem_singleton] at h0mem hhmem
    exact hhmem.trans h0mem.symm
  have huniv_sub : IsSubgroup (Finset.univ : Finset (Fin m → Bool)) :=
    ⟨Finset.mem_univ _, fun _ _ _ _ => Finset.mem_univ _⟩
  have huniv_card : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ (2 * s) := by
    simp [m, Fintype.card_fun]
  obtain ⟨e, f, _, hB, hsurj, hinj⟩ :=
    exists_symplectic_basis (polar R) (polar_self hRquad) (polar_symm R) (polar_xor_right hRquad)
      s Finset.univ huniv_sub huniv_card hnondeg
  obtain ⟨i₁, i₂, hne12, hM12⟩ := exists_symp_pair_M hs R hRquad e f hB

  obtain ⟨b0, l0, a0, hqeq⟩ := hq
  let uVec : (Fin m → Fin 2 → Bool) → (Fin m × Fin 3) → Bool :=
    fun u p => mergeLane lane u (fun _ => false) p.1 p.2
  let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  let ν : (Fin m → Fin 2 → Bool) → Fin m → Bool := fun u i =>
    par (∑ p : Fin m × Fin 3, (Bcoeff p (i, lane i) && uVec u p).toNat)
  let re : Fin s → Bool := fun a => xor (R (e a)) (R (fun _ => false))
  let rf : Fin s → Bool := fun a => xor (R (f a)) (R (fun _ => false))
  let c0u : (Fin m → Fin 2 → Bool) → Bool := fun u =>
    xor (q (mergeLane lane u (fun _ => false))) (q (fun _ _ => false))
  let g : (Fin m → Fin 2 → Bool) → Bool := fun u =>
    xor (xor (c0u u) (R (fun _ => false)))
      (par (∑ a : Fin s,
        (xor (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) (e a)) (re a) &&
         xor (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) (f a)) (rf a)).toNat))
  have hsum_eq : (∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
      (2 ^ s : ℤ) * ∑ u : Fin m → Fin 2 → Bool, sgn (g u) := by
    have hsplit := sum_split_lane m q b0 l0 a0 hqeq lane
    dsimp only at hsplit
    rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hinner := sum_quad_symplectic R hRquad e f hB hsurj hinj
      (fun i => xor (u i 0 && u i 1) (ν u i))
    dsimp only at hinner
    rw [hinner]
    dsimp only [g, c0u, re, rf]
    simp only [sgn_xor]
    ring
  let Rest := {j : Fin m // j ≠ i₁ ∧ j ≠ i₂}
  let ins2 : (Rest → Fin 2 → Bool) → (Fin 2 → Fin 2 → Bool) → (Fin m → Fin 2 → Bool) :=
    fun ur v j k =>
      if h1 : j = i₁ then v 0 k
      else if h2 : j = i₂ then v 1 k
      else ur ⟨j, ⟨h1, h2⟩⟩ k
  let eqU : (Fin m → Fin 2 → Bool) ≃ (Rest → Fin 2 → Bool) × (Fin 2 → Fin 2 → Bool) :=
    { toFun := fun u => (fun r => u r.val, fun t => if t = 0 then u i₁ else u i₂)
      invFun := fun p => ins2 p.1 p.2
      left_inv := fun u => by
        funext j k
        dsimp only [ins2]
        by_cases h1 : j = i₁
        · subst h1; simp
        · by_cases h2 : j = i₂
          · subst h2; simp [h1]
          · simp [h1, h2]
      right_inv := fun ⟨ur, v⟩ => by
        apply Prod.ext
        · funext ⟨j, hj1, hj2⟩ k; simp [ins2, hj1, hj2]
        · funext t k; fin_cases t
          · simp [ins2]
          · simp [ins2, hne12.symm] }
  have hfiber_bound : ∀ ur : Rest → Fin 2 → Bool,
      |∑ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v))| ≤ 14 := by
    intro ur
    have huVec_aff : ∀ p : Fin m × Fin 3,
        ∃ (c : Bool) (ml : (Fin 2 × Fin 2) → Bool), ∀ v : Fin 2 → Fin 2 → Bool,
          uVec (ins2 ur v) p = xor c (linGen ml (fun x => v x.1 x.2)) := by
      intro ⟨j, l⟩
      by_cases hl : l = lane j
      · refine ⟨false, fun _ => false, fun v => ?_⟩
        simp [uVec, mergeLane, hl, linGen, par]
      · let k : Fin 2 := if l = otherIdx (lane j) 0 then 0 else 1
        have hu_eq : ∀ u : Fin m → Fin 2 → Bool, uVec u (j, l) = u j k := fun u => by
          dsimp only [uVec, mergeLane, k]
          rw [if_neg hl]
          by_cases h2 : l = otherIdx (lane j) 0
          · rw [if_pos h2, if_pos h2]
          · rw [if_neg h2, if_neg h2]
        by_cases hj1 : j = i₁
        · refine ⟨false, fun x => decide (x = (0, k)), fun v => ?_⟩
          rw [hu_eq]
          simp only [ins2, dif_pos hj1, Bool.false_xor, linGen]
          have hpt : ∀ x : Fin 2 × Fin 2, (decide (x = (0, k)) && v x.1 x.2) =
              if x = (0, k) then v 0 k else false := fun x => by
            by_cases hx : x = (0, k) <;> simp [hx]
          simp_rw [hpt]
          exact (par_sum_ite_eq Finset.univ (0, k) (Finset.mem_univ _) (v 0 k)).symm
        · by_cases hj2 : j = i₂
          · refine ⟨false, fun x => decide (x = (1, k)), fun v => ?_⟩
            rw [hu_eq]
            simp only [ins2, dif_neg hj1, dif_pos hj2, Bool.false_xor, linGen]
            have hpt : ∀ x : Fin 2 × Fin 2, (decide (x = (1, k)) && v x.1 x.2) =
                if x = (1, k) then v 1 k else false := fun x => by
              by_cases hx : x = (1, k) <;> simp [hx]
            simp_rw [hpt]
            exact (par_sum_ite_eq Finset.univ (1, k) (Finset.mem_univ _) (v 1 k)).symm
          · refine ⟨ur ⟨j, ⟨hj1, hj2⟩⟩ k, fun _ => false, fun v => ?_⟩
            rw [hu_eq]
            simp [ins2, hj1, hj2, linGen, par]
    have hpar_c0 : par (∑ v : Fin 2 → Fin 2 → Bool,
        (xor (c0u (ins2 ur v)) (R (fun _ => false))).toNat) = false := by
      have hQv : IsQuadGen (fun x : (Fin m × Fin 3) → Bool => q (fun j l => x (j, l))) :=
        quad_to_gen q ⟨b0, l0, a0, hqeq⟩
      have hcomp : IsQuadGen (fun x : (Fin 2 × Fin 2) → Bool =>
          q (mergeLane lane (ins2 ur (fun t k => x (t, k))) (fun _ => false))) :=
        isQuadGen_comp_affine hQv (fun x p => uVec (ins2 ur (fun t k => x (t, k))) p)
          (fun p => by
            obtain ⟨c, ml, hml⟩ := huVec_aff p
            exact ⟨c, ml, fun x => hml (fun t k => x (t, k))⟩)
      have htot : IsQuadGen (fun x : (Fin 2 × Fin 2) → Bool =>
          xor (c0u (ins2 ur (fun t k => x (t, k)))) (R (fun _ => false))) := by
        have heq : (fun x : (Fin 2 × Fin 2) → Bool =>
            xor (c0u (ins2 ur (fun t k => x (t, k)))) (R (fun _ => false))) =
            fun x => xor (q (mergeLane lane (ins2 ur (fun t k => x (t, k))) (fun _ => false)))
              (xor (q (fun _ _ => false)) (R (fun _ => false))) := by
          funext x; dsimp only [c0u]; exact Bool.xor_assoc _ _ _
        rw [heq]
        exact isQuadGen_xor hcomp (isQuadGen_const _)
      obtain ⟨bc, lc, ac, hceq⟩ := htot
      have hpt : ∀ v : Fin 2 → Fin 2 → Bool,
          xor (c0u (ins2 ur v)) (R (fun _ => false)) =
          xor (xor bc (par (∑ p : Fin 2 × Fin 2, (lc p && v p.1 p.2).toNat)))
              (par (∑ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
                (ac p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat)) := by
        intro v
        have h := hceq (fun x => v x.1 x.2)
        dsimp only [quadFormGen, linGen] at h
        rw [← Fintype.sum_prod_type (fun p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
          (ac p.1 p.2 && v p.1.1 p.1.2 && v p.2.1 p.2.2).toNat)] at h
        exact h
      simp_rw [hpt]
      exact par_sum_quad_deg2_false bc lc ac
    have hlin_decomp : ∀ (vec : Fin m → Bool) (rconst : Bool),
        ∃ (a₀ : Bool) (mL : (Fin 2 × Fin 2) → Bool), ∀ v : Fin 2 → Fin 2 → Bool,
          xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) vec) rconst =
          xor (xor (vec i₁ && (v 0 0 && v 0 1)) (vec i₂ && (v 1 0 && v 1 1)))
              (xor a₀ (par (∑ p : Fin 2 × Fin 2, (mL p && v p.1 p.2).toNat))) := by
      intro vec rconst
      have hν_aff : ∀ i : Fin m, ∃ (ci : Bool) (mi : (Fin 2 × Fin 2) → Bool),
          ∀ x : (Fin 2 × Fin 2) → Bool,
            ν (ins2 ur (fun t k => x (t, k))) i = xor ci (linGen mi x) := fun i =>
        lin_comp_affine (fun p => Bcoeff p (i, lane i))
          (fun x p => uVec (ins2 ur (fun t k => x (t, k))) p)
          (fun p => by
            obtain ⟨c, ml, hml⟩ := huVec_aff p
            exact ⟨c, ml, fun x => hml (fun t k => x (t, k))⟩)
      obtain ⟨cν, mν, hmν⟩ := lin_comp_affine vec
        (fun x i => ν (ins2 ur (fun t k => x (t, k))) i) hν_aff
      let crest : Bool := par (∑ r : Rest, (vec r.val && (ur r 0 && ur r 1)).toNat)
      refine ⟨xor (xor crest cν) rconst, mν, fun v => ?_⟩
      have hsplit_lin : linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) vec =
          xor (par (∑ i : Fin m, (vec i && (ins2 ur v i 0 && ins2 ur v i 1)).toNat))
              (linGen vec (ν (ins2 ur v))) := by
        unfold linGen
        have hpt : ∀ i, (xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i) && vec i) =
            xor (vec i && (ins2 ur v i 0 && ins2 ur v i 1)) (vec i && ν (ins2 ur v) i) := fun i => by
          cases ins2 ur v i 0 <;> cases ins2 ur v i 1 <;> cases ν (ins2 ur v) i <;> cases vec i <;> rfl
        simp_rw [hpt]
        exact par_sum_xor Finset.univ _ _
      have hsum_m : par (∑ i : Fin m, (vec i && (ins2 ur v i 0 && ins2 ur v i 1)).toNat) =
          xor (xor (vec i₁ && (v 0 0 && v 0 1)) (vec i₂ && (v 1 0 && v 1 1))) crest := by
        let F : Fin m → ℕ := fun i => (vec i && (ins2 ur v i 0 && ins2 ur v i 1)).toNat
        have h1 : (∑ i : Fin m, F i) = F i₁ + F i₂ +
            ∑ i ∈ (Finset.univ.erase i₁).erase i₂, F i := by
          rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ i₁)]
          have hi2 : i₂ ∈ (Finset.univ : Finset (Fin m)).erase i₁ :=
            Finset.mem_erase.mpr ⟨hne12.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ F hi2]; ring
        have h2 : (∑ i ∈ (Finset.univ.erase i₁).erase i₂, F i) =
            ∑ r : Rest, (vec r.val && (ur r 0 && ur r 1)).toNat := by
          refine Finset.sum_bij (fun i hi => ⟨i, ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1,
            (Finset.mem_erase.mp hi).1⟩⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h; exact congrArg Subtype.val h
          · intro r _
            refine ⟨r.val, Finset.mem_erase.mpr ⟨r.property.2, Finset.mem_erase.mpr ⟨r.property.1, Finset.mem_univ _⟩⟩, rfl⟩
          · intro i hi
            have h2ne : i ≠ i₂ := (Finset.mem_erase.mp hi).1
            have h1ne : i ≠ i₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            simp [F, ins2, h1ne, h2ne]
        rw [show (∑ i : Fin m, (vec i && (ins2 ur v i 0 && ins2 ur v i 1)).toNat) = ∑ i : Fin m, F i from rfl,
          h1, h2, par_add, par_add]
        have hFi1 : par (F i₁) = (vec i₁ && (v 0 0 && v 0 1)) := by
          simp [F, ins2, par_toNat]
        have hFi2 : par (F i₂) = (vec i₂ && (v 1 0 && v 1 1)) := by
          simp [F, ins2, hne12.symm, par_toNat]
        rw [hFi1, hFi2]
      have hν_val : linGen vec (ν (ins2 ur v)) = xor cν (par (∑ p : Fin 2 × Fin 2, (mν p && v p.1 p.2).toNat)) :=
        hmν (fun x => v x.1 x.2)
      rw [hsplit_lin, hsum_m, hν_val]
      cases vec i₁ && (v 0 0 && v 0 1) <;> cases vec i₂ && (v 1 0 && v 1 1) <;>
        cases crest <;> cases cν <;> cases rconst <;>
        cases par (∑ p : Fin 2 × Fin 2, (mν p && v p.1 p.2).toNat) <;> rfl
    have hpar_prod : par (∑ v : Fin 2 → Fin 2 → Bool,
        (par (∑ a : Fin s,
          (xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (e a)) (re a) &&
           xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (f a)) (rf a)).toNat)).toNat) =
        true := by
      rw [par_sum_par_comm (fun v a =>
        xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (e a)) (re a) &&
        xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (f a)) (rf a))]
      have hterm : ∀ a : Fin s,
          par (∑ v : Fin 2 → Fin 2 → Bool,
            (xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (e a)) (re a) &&
             xor (linGen (fun i => xor (ins2 ur v i 0 && ins2 ur v i 1) (ν (ins2 ur v) i)) (f a)) (rf a)).toNat) =
          xor (e a i₁ && f a i₂) (e a i₂ && f a i₁) := by
        intro a
        obtain ⟨a₀, mA, hA⟩ := hlin_decomp (e a) (re a)
        obtain ⟨b₀, mB, hB'⟩ := hlin_decomp (f a) (rf a)
        simp_rw [hA, hB']
        exact par_sum_prod_pair_quad (e a i₁) (e a i₂) (f a i₁) (f a i₂) a₀ b₀ mA mB
      simp_rw [hterm]
      exact hM12
    have hg_odd : par (∑ v : Fin 2 → Fin 2 → Bool, (g (ins2 ur v)).toNat) = true := by
      dsimp only [g]
      rw [par_sum_xor, hpar_c0, hpar_prod]
      rfl
    let kv : ℕ := ∑ v : Fin 2 → Fin 2 → Bool, (g (ins2 ur v)).toNat
    have hkv_odd : kv % 2 = 1 := by
      have : (kv % 2 == 1) = true := hg_odd
      simpa using this
    have hkv_le : kv ≤ 16 := by
      have : kv ≤ ∑ _v : Fin 2 → Fin 2 → Bool, 1 := Finset.sum_le_sum fun v _ => by cases g (ins2 ur v) <;> decide
      have h16 : (∑ _v : Fin 2 → Fin 2 → Bool, 1) = 16 := by decide
      omega
    have hsum_g : (∑ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v))) = 16 - 2 * (kv : ℤ) := by
      have hpt : ∀ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v)) = 1 - 2 * ((g (ins2 ur v)).toNat : ℤ) := fun v => by
        cases g (ins2 ur v) <;> decide
      simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have h16 : (∑ _v : Fin 2 → Fin 2 → Bool, (1 : ℤ)) = 16 := by decide
      rw [h16]; dsimp only [kv]; push_cast; rfl
    rw [hsum_g, abs_le]
    omega
  have hsum_u_bound : |∑ u : Fin m → Fin 2 → Bool, sgn (g u)| ≤ 14 * (2 ^ (4 * s - 4) : ℤ) := by
    have hsplit_u : (∑ u : Fin m → Fin 2 → Bool, sgn (g u)) =
        ∑ ur : Rest → Fin 2 → Bool, ∑ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v)) := by
      trans (∑ p : (Rest → Fin 2 → Bool) × (Fin 2 → Fin 2 → Bool), sgn (g (ins2 p.1 p.2)))
      · refine Fintype.sum_equiv eqU _ _ fun u => ?_
        congr 2; exact (eqU.left_inv u).symm
      · exact Fintype.sum_prod_type _
    rw [hsplit_u]
    have hRest_card : Fintype.card Rest = m - 2 := by
      have hsub : (Finset.univ.filter (fun j : Fin m => j ≠ i₁ ∧ j ≠ i₂)).card = m - 2 := by
        have heq : Finset.univ.filter (fun j : Fin m => j ≠ i₁ ∧ j ≠ i₂) =
            (Finset.univ.erase i₁).erase i₂ := by
          ext j; simp [and_comm]
        rw [heq, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne12.symm, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
        omega
      rw [Fintype.card_subtype]
      exact hsub
    have hfun_card : (Fintype.card (Rest → Fin 2 → Bool) : ℤ) = 2 ^ (4 * s - 4) := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hRest_card]
      have h2pow : (4 : ℕ) ^ (m - 2) = 2 ^ (4 * s - 4) := by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this, ← pow_mul]
        congr 1; dsimp only [m]; omega
      exact_mod_cast h2pow
    calc |∑ ur : Rest → Fin 2 → Bool, ∑ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v))|
        ≤ ∑ ur : Rest → Fin 2 → Bool, |∑ v : Fin 2 → Fin 2 → Bool, sgn (g (ins2 ur v))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ur : Rest → Fin 2 → Bool, (14 : ℤ) :=
          Finset.sum_le_sum fun ur _ => hfiber_bound ur
      _ = (Fintype.card (Rest → Fin 2 → Bool) : ℤ) * 14 := by simp
      _ = 14 * (2 ^ (4 * s - 4) : ℤ) := by rw [hfun_card, mul_comm]
  rw [hsum_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ s)]
  have hexp : (8 : ℤ) * ((2 ^ s : ℤ) * (14 * (2 ^ (4 * s - 4) : ℤ))) = 7 * 2 ^ (5 * s) := by
    have h1 : (8 : ℤ) * 14 = 7 * 2 ^ 4 := by norm_num
    calc (8 : ℤ) * (2 ^ s * (14 * 2 ^ (4 * s - 4)))
        = (8 * 14) * (2 ^ s * 2 ^ (4 * s - 4)) := by ring
      _ = (7 * 2 ^ 4) * (2 ^ s * 2 ^ (4 * s - 4)) := by rw [h1]
      _ = 7 * (2 ^ 4 * 2 ^ s * 2 ^ (4 * s - 4)) := by ring
      _ = 7 * 2 ^ (5 * s) := by
          rw [← pow_add, ← pow_add]; congr 2; omega
  calc 8 * ((2 ^ s : ℤ) * |∑ u : Fin m → Fin 2 → Bool, sgn (g u)|)
      ≤ 8 * ((2 ^ s : ℤ) * (14 * (2 ^ (4 * s - 4) : ℤ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_u_bound (by positivity)) (by norm_num)
    _ = 7 * 2 ^ (5 * s) := hexp

def mergeWC3 {m k s : ℕ} (P Q : Finset (Fin m)) (hPQ : ∀ i, i ∉ P → i ∈ Q)
    (eP : Fin k ≃ {i : Fin m // i ∈ P}) (eQ : Fin (2 * s) ≃ {i : Fin m // i ∈ Q})
    (lane : Fin m → Fin 3)
    (uP : Fin k → Fin 2 → Bool) (zP : Fin k → Bool) (wQ : Fin (2 * s) → Fin 3 → Bool) :
    Fin m → Fin 3 → Bool := fun i l =>
  if hi : i ∈ P then
    let a := eP.symm ⟨i, hi⟩
    if l = lane i then zP a
    else if l = otherIdx (lane i) 0 then uP a 0
    else uP a 1
  else
    wQ (eQ.symm ⟨i, hPQ i hi⟩) l

theorem case3_decomp (m k s : ℕ)
    (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3)
    (P Q : Finset (Fin m))
    (hP_def : P = Finset.univ.filter (fun i : Fin m => stdBasis i ∈
      (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hQ_def : Q = Finset.univ.filter (fun i : Fin m => stdBasis i ∉
      (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hPQ : ∀ i, i ∉ P → i ∈ Q)
    (hRad_mem : ∀ h : Fin m → Bool,
      h ∈ (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false) ↔
      ∀ i ∉ P, h i = false)
    (hB_QP_zero : ∀ p ∈ P, ∀ j : Fin m × Fin 3, j.1 ∈ Q → xor (a0 j (p, lane p)) (a0 (p, lane p) j) = false)
    (eP : Fin k ≃ {i : Fin m // i ∈ P}) (eQ : Fin (2 * s) ≃ {i : Fin m // i ∈ Q}) :
    let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
    let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
    let laneP : Fin k → Fin 3 := fun a => lane (eP a).val
    let BcoeffP : (Fin k × Fin 3) → (Fin k × Fin 3) → Bool :=
      fun p₁ p₂ => Bcoeff ((eP p₁.1).val, p₁.2) ((eP p₂.1).val, p₂.2)
    let uVecP : (Fin k → Fin 2 → Bool) → (Fin k × Fin 3) → Bool :=
      fun uP p => mergeLane laneP uP (fun _ => false) p.1 p.2
    let νP : (Fin k → Fin 2 → Bool) → Fin k → Bool := fun uP a =>
      par (∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p).toNat)
    let rP : Fin k → Bool := fun a => xor (R (stdBasis (eP a).val)) (R (fun _ => false))
    let αP : (Fin k → Fin 2 → Bool) → Fin k → Bool :=
      fun uP a => xor (uP a 0 && uP a 1) (νP uP a)
    ∀ (uP : Fin k → Fin 2 → Bool) (zP : Fin k → Bool) (wQ : Fin (2 * s) → Fin 3 → Bool),
      xor (par (∑ i : Fin m, (mergeWC3 P Q hPQ eP eQ lane uP zP wQ i 0 && mergeWC3 P Q hPQ eP eQ lane uP zP wQ i 1 && mergeWC3 P Q hPQ eP eQ lane uP zP wQ i 2).toNat))
          (q (mergeWC3 P Q hPQ eP eQ lane uP zP wQ)) =
      xor (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
               (q (mergeWC3 P Q hPQ eP eQ lane uP (fun _ => false) wQ)))
          (linGen (fun a => xor (rP a) (αP uP a)) zP) := by
  subst hP_def; subst hQ_def
  intro R Bcoeff laneP BcoeffP uVecP νP rP αP
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ Rad)
  let Q : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∉ Rad)
  let mergeW := mergeWC3 P Q hPQ eP eQ lane
  intro uP zP wQ
  let w₀ := mergeW uP (fun _ => false) wQ
  let zExt : Fin m → Bool := fun i => if hi : i ∈ P then zP (eP.symm ⟨i, hi⟩) else false
  let zVec : Fin m → Fin 3 → Bool := fun i l => (l == lane i) && zExt i
  have hw_xor : mergeW uP zP wQ = fun i l => xor (w₀ i l) (zVec i l) := by
    funext i l
    dsimp only [w₀, zVec, zExt, mergeW, mergeWC3]
    by_cases hi : i ∈ P
    · rw [dif_pos hi, dif_pos hi, dif_pos hi]
      by_cases hl : l = lane i
      · subst hl; simp
      · simp [hl, beq_false_of_ne hl]
    · rw [dif_neg hi, dif_neg hi, dif_neg hi]
      simp
  have hzExt_Rad : zExt ∈ Rad := by
    rw [hRad_mem]
    intro i hi; dsimp only [zExt]; rw [dif_neg hi]
  have hq_zVec : xor (q zVec) (q (fun _ _ => false)) = linGen rP zP := by
    have h1 : q zVec = R zExt := rfl
    have h2 : q (fun _ _ => false) = R (fun _ => false) := by
      congr 1; funext i l; simp
    rw [h1, h2]
    have hR_lin : ∀ S : Finset (Fin k),
        xor (R (fun i => if hi : i ∈ P then decide (eP.symm ⟨i, hi⟩ ∈ S) else false))
            (R (fun _ => false)) =
        par (∑ a ∈ S, (rP a).toNat) := by
      classical
      intro S
      induction S using Finset.induction_on with
      | empty =>
        have : (fun i : Fin m => if hi : i ∈ P then decide (eP.symm ⟨i, hi⟩ ∈ (∅ : Finset (Fin k))) else false) =
            fun _ => false := by funext i; split_ifs <;> simp
        rw [this]; simp [par]
      | insert a S ha ih =>
        let vS : Fin m → Bool := fun i => if hi : i ∈ P then decide (eP.symm ⟨i, hi⟩ ∈ S) else false
        have hv_eq : (fun i => if hi : i ∈ P then decide (eP.symm ⟨i, hi⟩ ∈ insert a S) else false) =
            fun i => xor (stdBasis (eP a).val i) (vS i) := by
          funext i
          by_cases hi : i ∈ P
          · rw [dif_pos hi]; dsimp only [vS]; rw [dif_pos hi]
            by_cases he : eP.symm ⟨i, hi⟩ = a
            · have hi_eq : i = (eP a).val := by
                rw [← he]; exact (congrArg Subtype.val (eP.apply_symm_apply ⟨i, hi⟩)).symm
              subst hi_eq; simp [stdBasis, he, ha]
            · have hi_ne : i ≠ (eP a).val := fun h => he (by
                apply eP.injective; rw [eP.apply_symm_apply]; exact Subtype.ext h)
              simp [stdBasis, he, hi_ne]
          · rw [dif_neg hi]; dsimp only [vS]; rw [dif_neg hi]
            have hi_ne : i ≠ (eP a).val := fun h => hi (h ▸ (eP a).property)
            simp [stdBasis, hi_ne]
        have hpol0 : polar R (stdBasis (eP a).val) vS = false :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp (eP a).property).2).2 vS
        rw [hv_eq, quad_add_expand R (stdBasis (eP a).val) vS, hpol0, Finset.sum_insert ha,
          par_add, par_toNat, ← ih]
        dsimp only [rP]
        cases R (stdBasis (eP a).val) <;> cases R vS <;> cases R (fun _ => false) <;> rfl
    let Sz : Finset (Fin k) := Finset.univ.filter (fun a => zP a = true)
    have hz_eq : zExt = fun i => if hi : i ∈ P then decide (eP.symm ⟨i, hi⟩ ∈ Sz) else false := by
      funext i; dsimp only [zExt]
      split_ifs with hi
      · simp only [Sz, Finset.mem_filter, Finset.mem_univ, true_and]; cases zP _ <;> rfl
      · rfl
    rw [hz_eq, hR_lin Sz]
    unfold linGen
    congr 1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    cases zP a <;> simp
  have hpol_w0_z : polar (fun v : (Fin m × Fin 3) → Bool => q (fun i l => v (i, l)))
      (fun p => w₀ p.1 p.2) (fun p => zVec p.1 p.2) = linGen (νP uP) zP := by
    have hpeq : polar (fun v : (Fin m × Fin 3) → Bool => q (fun i l => v (i, l)))
        (fun p => w₀ p.1 p.2) (fun p => zVec p.1 p.2) =
        polar (quadFormGen b0 l0 a0) (fun p => w₀ p.1 p.2) (fun p => zVec p.1 p.2) := by
      unfold polar; simp only [hqeq]; rfl
    rw [hpeq, polar_quadFormGen]
    unfold linGen νP
    have hmod : par (∑ a : Fin k, (par (∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p).toNat) && zP a).toNat) =
        par (∑ a : Fin k, ∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p && zP a).toNat) := by
      refine par_sum_congr_mod Finset.univ _ _ fun a _ => ?_
      cases zP a
      · simp
      · simp only [Bool.and_true, par]
        have hm : (∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p).toNat) % 2 = 0 ∨
            (∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p).toNat) % 2 = 1 := by omega
        rcases hm with hm | hm <;> simp [hm]
    rw [hmod]
    conv_rhs => rw [Finset.sum_comm]
    congr 1
    have hrhs_col : ∀ j : Fin m × Fin 3,
        (∑ x : Fin m × Fin 3, (Bcoeff j x && w₀ j.1 j.2 && zVec x.1 x.2).toNat) =
        ∑ a : Fin k, (Bcoeff j ((eP a).val, laneP a) && w₀ j.1 j.2 && zP a).toNat := by
      intro j
      rw [Fintype.sum_prod_type]
      have hinner : ∀ i : Fin m,
          (∑ l : Fin 3, (Bcoeff j (i, l) && w₀ j.1 j.2 && zVec i l).toNat) =
          (Bcoeff j (i, lane i) && w₀ j.1 j.2 && zExt i).toNat := fun i => by
        rw [Finset.sum_eq_single (lane i)]
        · simp [zVec]
        · intro l _ hne; simp [zVec, beq_false_of_ne hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hinner]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i ∈ P)]
      have hnotP_zero : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ P),
          (Bcoeff j (i, lane i) && w₀ j.1 j.2 && zExt i).toNat) = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [zExt, (Finset.mem_filter.mp hi).2]
      rw [hnotP_zero, Nat.add_zero]
      refine Finset.sum_bij (fun i hi => eP.symm ⟨i, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        have := congrArg (fun a => (eP a).val) h
        simpa [eP.apply_symm_apply] using this
      · intro a _
        refine ⟨(eP a).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (eP a).property⟩, ?_⟩
        exact eP.symm_apply_apply a
      · intro i hi
        have hiP : i ∈ P := (Finset.mem_filter.mp hi).2
        have hev : (eP (eP.symm ⟨i, hiP⟩)).val = i := congrArg Subtype.val (eP.apply_symm_apply ⟨i, hiP⟩)
        simp [laneP, zExt, hiP, hev]
    have hrew_col : ∀ j : Fin m × Fin 3,
        (∑ x : Fin m × Fin 3, (xor (a0 j x) (a0 x j) && w₀ j.1 j.2 && zVec x.1 x.2).toNat) =
        ∑ a : Fin k, (Bcoeff j ((eP a).val, laneP a) && w₀ j.1 j.2 && zP a).toNat := hrhs_col
    simp_rw [hrew_col]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i ∈ P)]
    have hQ_zero : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ P),
        ∑ l : Fin 3, ∑ a : Fin k, (Bcoeff (i, l) ((eP a).val, laneP a) && w₀ i l && zP a).toNat) = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun a _ => ?_
      have hiQ : i ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun hm => (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩
      have h0 := hB_QP_zero (eP a).val (eP a).property (i, l) hiQ
      simp [Bcoeff, laneP, h0]
    rw [hQ_zero, Nat.add_zero]
    trans (∑ a' : Fin k, ∑ l : Fin 3, ∑ a : Fin k,
        (Bcoeff ((eP a').val, l) ((eP a).val, laneP a) && uVecP uP (a', l) && zP a).toNat)
    · refine Finset.sum_bij (fun i hi => eP.symm ⟨i, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        have := congrArg (fun a => (eP a).val) h
        simpa [eP.apply_symm_apply] using this
      · intro a' _
        refine ⟨(eP a').val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (eP a').property⟩,
          eP.symm_apply_apply a'⟩
      · intro i hi
        have hiP : i ∈ P := (Finset.mem_filter.mp hi).2
        have hev : (eP (eP.symm ⟨i, hiP⟩)).val = i := congrArg Subtype.val (eP.apply_symm_apply ⟨i, hiP⟩)
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
        have hw0_eq : w₀ i l = uVecP uP (eP.symm ⟨i, hiP⟩, l) := by
          dsimp only [w₀, mergeW, mergeWC3, uVecP, mergeLane, laneP]
          rw [dif_pos hiP]; simp only [hev]
        rw [hev, hw0_eq]
    · rw [Fintype.sum_prod_type]
  have hq_split : q (mergeW uP zP wQ) =
      xor (q w₀) (xor (linGen rP zP) (linGen (νP uP) zP)) := by
    rw [hw_xor]
    let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun i l => v (i, l))
    have h := quad_add_expand Qv (fun p => w₀ p.1 p.2) (fun p => zVec p.1 p.2)
    change Qv (fun p => xor (w₀ p.1 p.2) (zVec p.1 p.2)) = _
    rw [h, hpol_w0_z]
    change xor (xor (q w₀) (xor (q zVec) (q (fun _ _ => false)))) (linGen (νP uP) zP) = _
    rw [hq_zVec]
    cases q w₀ <;> cases linGen rP zP <;> cases linGen (νP uP) zP <;> rfl
  have hf_split : par (∑ i : Fin m, (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 && mergeW uP zP wQ i 2).toNat) =
      xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
          (linGen (fun a => uP a 0 && uP a 1) zP) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i ∈ P), par_add]
    have hP_part : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ P),
        (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 && mergeW uP zP wQ i 2).toNat) =
        ∑ a : Fin k, ((uP a 0 && uP a 1) && zP a).toNat := by
      refine Finset.sum_bij (fun i hi => eP.symm ⟨i, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        have := congrArg (fun a => (eP a).val) h
        simpa [eP.apply_symm_apply] using this
      · intro a _
        refine ⟨(eP a).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (eP a).property⟩,
          eP.symm_apply_apply a⟩
      · intro i hi
        have hiP : i ∈ P := (Finset.mem_filter.mp hi).2
        simp only [mergeW, mergeWC3, dif_pos hiP]
        generalize hl : lane i = li
        fin_cases li <;> cases uP (eP.symm ⟨i, hiP⟩) 0 <;>
          cases uP (eP.symm ⟨i, hiP⟩) 1 <;> cases zP (eP.symm ⟨i, hiP⟩) <;>
          decide
    have hQ_part : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ P),
        (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 && mergeW uP zP wQ i 2).toNat) =
        ∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat := by
      refine Finset.sum_bij (fun i hi => eQ.symm ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun hm => (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        have := congrArg (fun b => (eQ b).val) h
        simpa [eQ.apply_symm_apply] using this
      · intro b _
        have hnotP : (eQ b).val ∉ P := fun hm =>
          (Finset.mem_filter.mp (eQ b).property).2 (Finset.mem_filter.mp hm).2
        refine ⟨(eQ b).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotP⟩, ?_⟩
        apply eQ.injective; apply Subtype.ext
        exact congrArg Subtype.val (eQ.apply_symm_apply _)
      · intro i hi
        have hnotP : i ∉ P := (Finset.mem_filter.mp hi).2
        simp [mergeW, mergeWC3, hnotP]
    rw [hP_part, hQ_part, Bool.xor_comm]
    rfl
  have hlin_α : linGen (fun a => xor (rP a) (αP uP a)) zP =
      xor (linGen (fun a => uP a 0 && uP a 1) zP)
          (xor (linGen rP zP) (linGen (νP uP) zP)) := by
    unfold linGen αP
    have hpt : ∀ a : Fin k,
        (xor (rP a) (xor (uP a 0 && uP a 1) (νP uP a)) && zP a) =
        xor ((uP a 0 && uP a 1) && zP a) (xor (rP a && zP a) (νP uP a && zP a)) := fun a => by
      cases rP a <;> cases uP a 0 <;> cases uP a 1 <;> cases νP uP a <;> cases zP a <;> rfl
    simp_rw [hpt]
    rw [par_sum_xor, par_sum_xor]
  rw [hf_split, hq_split, hlin_α]
  cases par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat) <;>
    cases q w₀ <;> cases linGen (fun a => uP a 0 && uP a 1) zP <;>
    cases linGen rP zP <;> cases linGen (νP uP) zP <;> rfl

theorem case3_fiber_Q (m k s : ℕ) (hs_pos : 0 < s)
    (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3)
    (P Q : Finset (Fin m))
    (hP_def : P = Finset.univ.filter (fun i : Fin m => stdBasis i ∈
      (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hQ_def : Q = Finset.univ.filter (fun i : Fin m => stdBasis i ∉
      (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hPQ : ∀ i, i ∉ P → i ∈ Q)
    (hRad_sub : IsSubgroup ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hRad_mem : ∀ h : Fin m → Bool,
      h ∈ (Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false) ↔
      ∀ i ∉ P, h i = false)
    (eP : Fin k ≃ {i : Fin m // i ∈ P}) (eQ : Fin (2 * s) ≃ {i : Fin m // i ∈ Q}) :
    ∀ uP : Fin k → Fin 2 → Bool,
      8 * |∑ wQ : Fin (2 * s) → Fin 3 → Bool,
        sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                 (q (mergeWC3 P Q hPQ eP eQ lane uP (fun _ => false) wQ)))| ≤ 7 * 2 ^ (5 * s) := by
  subst hP_def; subst hQ_def
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hRquad : IsQuadGen R := restrict_isQuadGen q ⟨b0, l0, a0, hqeq⟩ lane
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ Rad)
  let Q : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∉ Rad)
  let laneQ : Fin (2 * s) → Fin 3 := fun b => lane (eQ b).val
  let mergeW := mergeWC3 P Q hPQ eP eQ lane
  intro uP
  let qQ : (Fin (2 * s) → Fin 3 → Bool) → Bool := fun wQ => q (mergeW uP (fun _ => false) wQ)
  have hqQ_quad : ∃ (b : Bool) (l : (Fin (2 * s) × Fin 3) → Bool)
      (a : (Fin (2 * s) × Fin 3) → (Fin (2 * s) × Fin 3) → Bool),
      ∀ wQ, qQ wQ = xor (xor b (par (∑ j : Fin (2 * s) × Fin 3, (l j && wQ j.1 j.2).toNat)))
        (par (∑ i : Fin (2 * s) × Fin 3, ∑ j : Fin (2 * s) × Fin 3,
          (a i j && wQ i.1 i.2 && wQ j.1 j.2).toNat)) := by
    have hQv : IsQuadGen (fun v : (Fin m × Fin 3) → Bool => q (fun i l => v (i, l))) :=
      quad_to_gen q ⟨b0, l0, a0, hqeq⟩
    have hΦ : ∀ p : Fin m × Fin 3,
        ∃ (c : Bool) (ml : (Fin (2 * s) × Fin 3) → Bool),
          ∀ vQ : (Fin (2 * s) × Fin 3) → Bool,
            mergeW uP (fun _ => false) (fun b l => vQ (b, l)) p.1 p.2 = xor c (linGen ml vQ) := by
      intro ⟨i, l⟩
      by_cases hi : i ∈ P
      · refine ⟨mergeW uP (fun _ => false) (fun _ _ => false) i l, fun _ => false, fun vQ => ?_⟩
        simp [mergeW, mergeWC3, hi, linGen, par]
      · let b := eQ.symm ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩⟩
        refine ⟨false, fun p => decide (p = (b, l)), fun vQ => ?_⟩
        simp only [mergeW, mergeWC3, dif_neg hi, Bool.false_xor, linGen]
        have hpt : ∀ p : Fin (2 * s) × Fin 3, (decide (p = (b, l)) && vQ p) =
            if p = (b, l) then vQ (b, l) else false := fun p => by
          by_cases hp : p = (b, l) <;> simp [hp]
        simp_rw [hpt]
        exact (par_sum_ite_eq Finset.univ (b, l) (Finset.mem_univ _) (vQ (b, l))).symm
    obtain ⟨bq, lq, aq, hqQeq⟩ := isQuadGen_comp_affine hQv
      (fun vQ p => mergeW uP (fun _ => false) (fun b l => vQ (b, l)) p.1 p.2) hΦ
    exact ⟨bq, lq, aq, fun wQ => hqQeq (fun p => wQ p.1 p.2)⟩
  have hqQ_rad : ((Finset.univ : Finset (Fin (2 * s) → Bool)).filter (fun h => ∀ t : Fin (2 * s) → Bool,
      xor (xor (qQ (fun i j => (j == laneQ i) && xor (h i) (t i)))
               (qQ (fun i j => (j == laneQ i) && h i)))
          (xor (qQ (fun i j => (j == laneQ i) && t i))
               (qQ (fun i j => (j == laneQ i) && false))) = false)).card = 1 := by
    let RQ : (Fin (2 * s) → Bool) → Bool := fun zQ => qQ (fun i j => (j == laneQ i) && zQ i)
    let extQ : (Fin (2 * s) → Bool) → (Fin m → Bool) := fun zQ i =>
      if hi : i ∈ Q then zQ (eQ.symm ⟨i, hi⟩) else false
    have hpol_eq : ∀ h t : Fin (2 * s) → Bool, polar RQ h t = polar R (extQ h) (extQ t) := by
      intro h t
      let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun i l => v (i, l))
      have hQv : IsQuadGen Qv := quad_to_gen q ⟨b0, l0, a0, hqeq⟩
      let v0 : (Fin m × Fin 3) → Bool := fun p => mergeW uP (fun _ => false) (fun _ _ => false) p.1 p.2
      let zV : (Fin (2 * s) → Bool) → (Fin m × Fin 3) → Bool :=
        fun zQ p => (p.2 == lane p.1) && extQ zQ p.1
      have hRQ_eq : ∀ zQ : Fin (2 * s) → Bool,
          RQ zQ = Qv (fun p => xor (v0 p) (zV zQ p)) := by
        intro zQ
        dsimp only [RQ, qQ, Qv, v0, zV, extQ]
        congr 1; funext i l
        dsimp only [mergeW, mergeWC3, mergeWC3]
        by_cases hi : i ∈ P
        · have hnotQ : i ∉ Q := fun hm => (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hi).2
          rw [dif_pos hi, dif_pos hi, dif_neg hnotQ]; simp
        · have hiQ : i ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩
          rw [dif_neg hi, dif_neg hi, dif_pos hiQ]
          have hev : laneQ (eQ.symm ⟨i, hiQ⟩) = lane i := by
            dsimp only [laneQ]; rw [congrArg Subtype.val (eQ.apply_symm_apply ⟨i, hiQ⟩)]
          rw [hev]; simp
      have hshift : ∀ a b : (Fin m × Fin 3) → Bool,
          xor (xor (Qv (fun p => xor (v0 p) (xor (a p) (b p)))) (Qv (fun p => xor (v0 p) (a p))))
              (xor (Qv (fun p => xor (v0 p) (b p))) (Qv v0)) =
          polar Qv a b := by
        intro a b
        have h1 := quad_add_expand Qv v0 (fun p => xor (a p) (b p))
        have h2 := quad_add_expand Qv v0 a
        have h3 := quad_add_expand Qv v0 b
        rw [h1, h2, h3, polar_xor_right hQv v0 a b, quad_add_expand Qv a b]
        cases Qv v0 <;> cases Qv a <;> cases Qv b <;> cases Qv (fun _ => false) <;>
          cases polar Qv v0 a <;> cases polar Qv v0 b <;> cases polar Qv a b <;> rfl
      unfold polar
      simp_rw [hRQ_eq]
      have hz0 : (fun p => xor (v0 p) (zV (fun _ => false) p)) = v0 := by
        funext p; dsimp only [zV, extQ]; split_ifs <;> simp
      have hzx : (fun p => xor (v0 p) (zV (fun i => xor (h i) (t i)) p)) =
          fun p => xor (v0 p) (xor (zV h p) (zV t p)) := by
        funext p; dsimp only [zV, extQ]
        by_cases hp : p.1 ∈ Q
        · rw [dif_pos hp, dif_pos hp, dif_pos hp]
          cases (p.2 == lane p.1) <;> cases h _ <;> cases t _ <;> rfl
        · rw [dif_neg hp, dif_neg hp, dif_neg hp]; simp
      rw [hz0, hzx, hshift (zV h) (zV t)]
      unfold polar
      have hR1 : ∀ z : Fin m → Bool, R z = Qv (fun p => (p.2 == lane p.1) && z p.1) := fun _ => rfl
      rw [hR1, hR1, hR1, hR1]
      have he0 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && false) = fun _ => false := by
        funext p; simp
      have hex : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && xor (extQ h p.1) (extQ t p.1)) =
          fun p => xor (zV h p) (zV t p) := by
        funext p; dsimp only [zV]
        cases (p.2 == lane p.1) <;> cases extQ h p.1 <;> cases extQ t p.1 <;> rfl
      rw [he0, hex]
    have hset_eq : (Finset.univ : Finset (Fin (2 * s) → Bool)).filter (fun h => ∀ t : Fin (2 * s) → Bool,
        xor (xor (RQ (fun i => xor (h i) (t i))) (RQ h))
            (xor (RQ t) (RQ (fun _ => false))) = false) = {fun _ => false} := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hpol
        have hrad_ext : extQ h ∈ Rad := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
          let tP : Fin m → Bool := fun i => if i ∈ P then t i else false
          let tQ : Fin (2 * s) → Bool := fun b => t (eQ b).val
          have ht_split : t = fun i => xor (tP i) (extQ tQ i) := by
            funext i; dsimp only [tP, extQ, tQ]
            by_cases hi : i ∈ P
            · have hnotQ : i ∉ Q := fun hm => (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hi).2
              rw [if_pos hi, dif_neg hnotQ]; simp
            · have hiQ : i ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩
              rw [if_neg hi, dif_pos hiQ]
              have hev : (eQ (eQ.symm ⟨i, hiQ⟩)).val = i := congrArg Subtype.val (eQ.apply_symm_apply ⟨i, hiQ⟩)
              rw [hev]; simp
          have htP_Rad : tP ∈ Rad := by
            rw [hRad_mem]; intro i hi; dsimp only [tP]; rw [if_neg hi]
          rw [ht_split, polar_xor_right hRquad, polar_symm R (extQ h) tP,
            (Finset.mem_filter.mp htP_Rad).2 (extQ h), ← hpol_eq h tQ, Bool.false_xor]
          exact hpol tQ
        funext b
        have hnotP : (eQ b).val ∉ P := fun hm =>
          (Finset.mem_filter.mp (eQ b).property).2 (Finset.mem_filter.mp hm).2
        have hf := (hRad_mem (extQ h)).mp hrad_ext (eQ b).val hnotP
        dsimp only [extQ] at hf
        rw [dif_pos (eQ b).property, eQ.symm_apply_apply] at hf
        exact hf
      · rintro rfl t
        rw [show xor (xor (RQ (fun i => xor false (t i))) (RQ (fun _ => false)))
            (xor (RQ t) (RQ (fun _ => false))) = polar RQ (fun _ => false) t from rfl, hpol_eq]
        have h0 : extQ (fun _ => false) = fun _ => false := by funext i; dsimp only [extQ]; split_ifs <;> rfl
        rw [h0]
        exact (Finset.mem_filter.mp hRad_sub.1).2 _
    rw [hset_eq]; simp
  exact nondeg_lane_bound s hs_pos qQ hqQ_quad laneQ hqQ_rad

theorem lane_rank_case3_coord_zero (m s : ℕ) (hs_pos : 0 < s) (hs : 2 * s ≤ m)
    (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3)
    (hCoord : IsCoordSubgroup ((Finset.univ : Finset (Fin m → Bool)).filter
      (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)))
    (hRad_card : ((Finset.univ : Finset (Fin m → Bool)).filter
      (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)).card = 2 ^ (m - 2 * s))
    (hcrossB : ∀ p ∈ Finset.univ.filter (fun i : Fin m => stdBasis i ∈
        (Finset.univ : Finset (Fin m → Bool)).filter
          (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)),
      ∀ q₀ ∈ Finset.univ.filter (fun i : Fin m => stdBasis i ∉
        (Finset.univ : Finset (Fin m → Bool)).filter
          (fun h => ∀ t, polar (fun z => q (fun i j => (j == lane i) && z i)) h t = false)),
      ∀ r : Fin 2, xor (a0 (q₀, otherIdx (lane q₀) r) (p, lane p))
                       (a0 (p, lane p) (q₀, otherIdx (lane q₀) r)) ≠ true) :
    8 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    7 * 8 ^ s * 6 ^ m := by
  let R : (Fin m → Bool) → Bool := fun z => q (fun i j => (j == lane i) && z i)
  have hRquad : IsQuadGen R := restrict_isQuadGen q ⟨b0, l0, a0, hqeq⟩ lane
  let Rad : Finset (Fin m → Bool) := Finset.univ.filter (fun h => ∀ t, polar R h t = false)
  let Bcoeff : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool := fun p₁ p₂ => xor (a0 p₁ p₂) (a0 p₂ p₁)
  have hRad_sub : IsSubgroup Rad := by
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      unfold polar
      have : (fun i => xor false (t i)) = t := by funext i; simp
      rw [this]; cases R t <;> cases R (fun _ => false) <;> rfl
    · intro a ha b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      rw [polar_xor_left hRquad, (Finset.mem_filter.mp ha).2 t, (Finset.mem_filter.mp hb).2 t]
      rfl
  let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ Rad)
  let Q : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∉ Rad)
  have hRad_mem := coordSubgroup_mem_iff hRad_sub hCoord
  dsimp only at hRad_mem
  have hPcard : P.card = m - 2 * s := by
    have hc := coordSubgroup_card hRad_sub hCoord
    exact Nat.pow_right_injective (by omega) (hc.symm.trans hRad_card)
  have hQcard : Q.card = 2 * s := by
    have hcomp : Q = Pᶜ := by ext i; simp [P, Q]
    rw [hcomp, Finset.card_compl, Fintype.card_fin, hPcard]; omega
  have hB_QP_zero : ∀ p ∈ P, ∀ j : Fin m × Fin 3, j.1 ∈ Q →
      Bcoeff j (p, lane p) = false := by
    intro p hpP ⟨j1, j2⟩ hjQ
    by_cases hl : j2 = lane j1
    · subst hl
      have hrad_p : polar R (stdBasis p) (stdBasis j1) = false :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hpP).2).2 (stdBasis j1)
      have hpol_eq : polar R (stdBasis p) (stdBasis j1) = Bcoeff (j1, lane j1) (p, lane p) := by
        let Qv : ((Fin m × Fin 3) → Bool) → Bool := fun v => q (fun a b => v (a, b))
        have hR1 : ∀ z : Fin m → Bool, R z = Qv (fun x => (x.2 == lane x.1) && z x.1) := fun _ => rfl
        have hep : (fun x : Fin m × Fin 3 => (x.2 == lane x.1) && stdBasis p x.1) =
            fun x => decide (x = (p, lane p)) := by
          funext ⟨a, b⟩; by_cases ha : a = p
          · rw [ha]; by_cases hb : b = lane p
            · rw [hb]; simp [stdBasis]
            · simp [stdBasis, beq_false_of_ne hb, Prod.mk.injEq, hb]
          · simp [stdBasis, ha]
        have hej : (fun x : Fin m × Fin 3 => (x.2 == lane x.1) && stdBasis j1 x.1) =
            fun x => decide (x = (j1, lane j1)) := by
          funext ⟨a, b⟩; by_cases ha : a = j1
          · rw [ha]; by_cases hb : b = lane j1
            · rw [hb]; simp [stdBasis]
            · simp [stdBasis, beq_false_of_ne hb, Prod.mk.injEq, hb]
          · simp [stdBasis, ha]
        have hepj : (fun x : Fin m × Fin 3 => (x.2 == lane x.1) && xor (stdBasis p x.1) (stdBasis j1 x.1)) =
            fun x => xor (decide (x = (p, lane p))) (decide (x = (j1, lane j1))) := by
          funext x
          have h1 := congrFun hep x; have h2 := congrFun hej x
          rw [← h1, ← h2]
          cases (x.2 == lane x.1) <;> cases stdBasis p x.1 <;> cases stdBasis j1 x.1 <;> rfl
        have he0 : (fun x : Fin m × Fin 3 => (x.2 == lane x.1) && false) = fun _ => false := by
          funext x; simp
        have hpeq : polar R (stdBasis p) (stdBasis j1) =
            polar (quadFormGen b0 l0 a0) (fun x => decide (x = (p, lane p)))
              (fun x => decide (x = (j1, lane j1))) := by
          unfold polar
          rw [hR1, hR1, hR1, hR1, hep, hej, hepj, he0]
          simp only [Qv, hqeq]; rfl
        rw [hpeq, polar_quadFormGen]
        have hsum : (∑ x₁ : Fin m × Fin 3, ∑ x₂ : Fin m × Fin 3,
            (xor (a0 x₁ x₂) (a0 x₂ x₁) && decide (x₁ = (p, lane p)) &&
              decide (x₂ = (j1, lane j1))).toNat) =
            (xor (a0 (p, lane p) (j1, lane j1)) (a0 (j1, lane j1) (p, lane p))).toNat := by
          rw [Finset.sum_eq_single (p, lane p)]
          · rw [Finset.sum_eq_single (j1, lane j1)]
            · simp
            · intro x₂ _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro x₁ _ hne; exact Finset.sum_eq_zero fun x₂ _ => by simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, par_toNat]
        dsimp only [Bcoeff]; exact Bool.xor_comm _ _
      rw [← hpol_eq, hrad_p]
    · have hoth : j2 = otherIdx (lane j1) 0 ∨ j2 = otherIdx (lane j1) 1 := by
        generalize hl1 : lane j1 = lj at hl ⊢
        fin_cases lj <;> fin_cases j2 <;> simp [otherIdx] at hl ⊢
      rcases hoth with rfl | rfl
      · cases hv : Bcoeff (j1, otherIdx (lane j1) 0) (p, lane p)
        · rfl
        · exact absurd hv (hcrossB p hpP j1 hjQ 0)
      · cases hv : Bcoeff (j1, otherIdx (lane j1) 1) (p, lane p)
        · rfl
        · exact absurd hv (hcrossB p hpP j1 hjQ 1)
  let k := m - 2 * s
  let eP : Fin k ≃ {i : Fin m // i ∈ P} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hPcard)).symm
  let eQ : Fin (2 * s) ≃ {i : Fin m // i ∈ Q} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hQcard)).symm
  have hPQ : ∀ i : Fin m, i ∉ P → i ∈ Q := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩
  let mergeW := mergeWC3 P Q hPQ eP eQ lane
  let eqW : (Fin m → Fin 3 → Bool) ≃
      ((Fin k → Fin 2 → Bool) × (Fin k → Bool)) × (Fin (2 * s) → Fin 3 → Bool) :=
    { toFun := fun w =>
        ((fun a r => w (eP a).val (otherIdx (lane (eP a).val) r),
          fun a => w (eP a).val (lane (eP a).val)),
         fun b l => w (eQ b).val l)
      invFun := fun p => mergeW p.1.1 p.1.2 p.2
      left_inv := fun w => by
        funext i l
        dsimp only [mergeW, mergeWC3, mergeWC3]
        by_cases hi : i ∈ P
        · rw [dif_pos hi]
          have hev : (eP (eP.symm ⟨i, hi⟩)).val = i := congrArg Subtype.val (eP.apply_symm_apply ⟨i, hi⟩)
          rw [hev]
          generalize hl : lane i = li
          fin_cases li <;> fin_cases l <;> simp [otherIdx]
        · rw [dif_neg hi]
          have hiQ : i ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun hm => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩
          have hev : (eQ (eQ.symm ⟨i, hiQ⟩)).val = i := congrArg Subtype.val (eQ.apply_symm_apply ⟨i, hiQ⟩)
          rw [hev]
      right_inv := fun ⟨⟨uP, zP⟩, wQ⟩ => by
        apply Prod.ext
        · apply Prod.ext
          · funext a r
            dsimp only [mergeW, mergeWC3, mergeWC3]
            rw [dif_pos (eP a).property, eP.symm_apply_apply]
            generalize hl : lane (eP a).val = li
            fin_cases li <;> fin_cases r <;> simp [otherIdx]
          · funext a
            dsimp only [mergeW, mergeWC3, mergeWC3]
            rw [dif_pos (eP a).property, eP.symm_apply_apply]
            simp
        · funext b l
          dsimp only [mergeW, mergeWC3, mergeWC3]
          have hnotP : (eQ b).val ∉ P := fun h =>
            (Finset.mem_filter.mp (eQ b).property).2 (Finset.mem_filter.mp h).2
          rw [dif_neg hnotP]
          have heq : eQ.symm ⟨(eQ b).val, (eQ b).property⟩ = b :=
            eQ.symm_apply_apply b
          rw [heq] }
  let laneP : Fin k → Fin 3 := fun a => lane (eP a).val
  let laneQ : Fin (2 * s) → Fin 3 := fun b => lane (eQ b).val
  let BcoeffP : (Fin k × Fin 3) → (Fin k × Fin 3) → Bool :=
    fun p₁ p₂ => Bcoeff ((eP p₁.1).val, p₁.2) ((eP p₂.1).val, p₂.2)
  let uVecP : (Fin k → Fin 2 → Bool) → (Fin k × Fin 3) → Bool :=
    fun uP p => mergeLane laneP uP (fun _ => false) p.1 p.2
  let νP : (Fin k → Fin 2 → Bool) → Fin k → Bool := fun uP a =>
    par (∑ p : Fin k × Fin 3, (BcoeffP p (a, laneP a) && uVecP uP p).toNat)
  let rP : Fin k → Bool := fun a => xor (R (stdBasis (eP a).val)) (R (fun _ => false))
  let αP : (Fin k → Fin 2 → Bool) → Fin k → Bool :=
    fun uP a => xor (uP a 0 && uP a 1) (νP uP a)
  have hdecomp := case3_decomp m k s q b0 l0 a0 hqeq lane P Q rfl rfl hPQ hRad_mem hB_QP_zero eP eQ
  let AP : Finset (Fin k → Fin 2 → Bool) := Finset.univ.filter (fun uP => αP uP = rP)
  have hS_factor : (∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))) =
      (2 ^ k : ℤ) * ∑ uP ∈ AP, ∑ wQ : Fin (2 * s) → Fin 3 → Bool,
        sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                 (q (mergeW uP (fun _ => false) wQ))) := by
    trans (∑ p : ((Fin k → Fin 2 → Bool) × (Fin k → Bool)) × (Fin (2 * s) → Fin 3 → Bool),
      sgn (xor (par (∑ i : Fin m, (mergeW p.1.1 p.1.2 p.2 i 0 && mergeW p.1.1 p.1.2 p.2 i 1 &&
        mergeW p.1.1 p.1.2 p.2 i 2).toNat)) (q (mergeW p.1.1 p.1.2 p.2))))
    · refine Fintype.sum_equiv eqW _ _ fun w => ?_
      have h : mergeW (eqW w).1.1 (eqW w).1.2 (eqW w).2 = w := eqW.left_inv w
      rw [h]
    · rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hinner_all : ∀ uP : Fin k → Fin 2 → Bool,
          (∑ zP : Fin k → Bool, ∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ i : Fin m, (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 &&
              mergeW uP zP wQ i 2).toNat)) (q (mergeW uP zP wQ)))) =
          ∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ))) *
            if (fun a => xor (rP a) (αP uP a)) = fun _ => false then
              (Fintype.card (Fin k → Bool) : ℤ)
            else 0 := by
        intro uP
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun wQ _ => ?_
        have hinner : (∑ zP : Fin k → Bool,
            sgn (xor (par (∑ i : Fin m, (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 &&
              mergeW uP zP wQ i 2).toNat)) (q (mergeW uP zP wQ)))) =
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ))) *
            ∑ zP : Fin k → Bool, sgn (linGen (fun a => xor (rP a) (αP uP a)) zP) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun zP _ => ?_
          have hd : xor (par (∑ i : Fin m, (mergeW uP zP wQ i 0 && mergeW uP zP wQ i 1 &&
              mergeW uP zP wQ i 2).toNat)) (q (mergeW uP zP wQ)) =
            xor (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ)))
                (linGen (fun a => xor (rP a) (αP uP a)) zP) := hdecomp uP zP wQ
          rw [hd, sgn_xor]
        rw [hinner, sum_sgn_linGen]
      simp_rw [hinner_all]
      have hzero_iff : ∀ uP : Fin k → Fin 2 → Bool,
          ((fun a => xor (rP a) (αP uP a)) = fun _ => false) ↔ αP uP = rP := fun uP => by
        constructor
        · intro h; funext a
          have ha := congrFun h a
          cases h1 : rP a <;> cases h2 : αP uP a <;> rw [h1, h2] at ha <;> first | rfl | cases ha
        · intro h; funext a; rw [h]; simp
      simp_rw [hzero_iff, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have hstep : ∀ uP : Fin k → Fin 2 → Bool,
          (∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ))) *
            if αP uP = rP then ((2 ^ k : ℕ) : ℤ) else 0) =
          if uP ∈ AP then (2 ^ k : ℤ) * ∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ)))
          else 0 := fun uP => by
        by_cases h : αP uP = rP
        · have hm : uP ∈ AP := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          simp [h, hm, Finset.mul_sum, mul_comm]
        · have hm : uP ∉ AP := fun hm => h (Finset.mem_filter.mp hm).2
          simp [h, hm]
      simp_rw [hstep, ← Finset.sum_filter, ← Finset.mul_sum]
      congr 2
      ext uP; simp [AP]
  have hAP_card : (AP.card : ℤ) ≤ 3 ^ k := by
    have hsum_id : (2 ^ k : ℤ) * (AP.card : ℤ) =
        ∑ hP : Fin k → Bool, sgn (linGen rP hP) * ∑ uP : Fin k → Fin 2 → Bool, sgn (linGen (αP uP) hP) := by
      have h1 : ∀ uP : Fin k → Fin 2 → Bool,
          (∑ hP : Fin k → Bool, sgn (linGen (fun a => xor (rP a) (αP uP a)) hP)) =
          if uP ∈ AP then (2 ^ k : ℤ) else 0 := fun uP => by
        rw [sum_sgn_linGen]
        have hiff : ((fun a => xor (rP a) (αP uP a)) = fun _ => false) ↔ uP ∈ AP := by
          simp only [AP, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; funext a
            have ha := congrFun h a
            cases h1 : rP a <;> cases h2 : αP uP a <;> rw [h1, h2] at ha <;> first | rfl | cases ha
          · intro h; funext a; rw [h]; simp
        by_cases hm : uP ∈ AP
        · rw [if_pos (hiff.mpr hm), if_pos hm]; simp [Fintype.card_fun]
        · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
      have h2 : (2 ^ k : ℤ) * (AP.card : ℤ) =
          ∑ uP : Fin k → Fin 2 → Bool, ∑ hP : Fin k → Bool,
            sgn (linGen (fun a => xor (rP a) (αP uP a)) hP) := by
        simp_rw [h1, ← Finset.sum_filter]
        have hf : Finset.univ.filter (fun uP => uP ∈ AP) = AP := by ext uP; simp
        rw [hf, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun hP _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun uP _ => ?_
      have hl : linGen (fun a => xor (rP a) (αP uP a)) hP = xor (linGen rP hP) (linGen (αP uP) hP) := by
        unfold linGen
        have hpt : ∀ a, (xor (rP a) (αP uP a) && hP a) = xor (rP a && hP a) (αP uP a && hP a) := fun a => by
          cases rP a <;> cases αP uP a <;> cases hP a <;> rfl
        simp_rw [hpt]; exact par_sum_xor Finset.univ _ _
      rw [hl, sgn_xor]
    have hwt_univ : (∑ hP : Fin k → Bool, (2 ^ (k - wt hP) : ℤ)) ≤ 3 ^ k := by
      have huniv : IsSubgroup (Finset.univ : Finset (Fin k → Bool)) :=
        ⟨Finset.mem_univ _, fun _ _ _ _ => Finset.mem_univ _⟩
      obtain ⟨k', _, hk'card, hk'sum⟩ := subgroup_wt_bound k Finset.univ huniv
      have hkeq : k' = k := by
        have : 2 ^ k' = 2 ^ k := by simpa [Fintype.card_fun] using hk'card.symm
        exact Nat.pow_right_injective (by omega) this
      have h0 := hk'sum (fun _ => false)
      have hsimpl : ∀ h ∈ (Finset.univ : Finset (Fin k → Bool)),
          2 ^ (k - wt (fun i => xor false (h i))) = 2 ^ (k - wt h) := fun h _ => by simp
      rw [Finset.sum_congr rfl hsimpl, hkeq, Nat.sub_self, pow_zero, mul_one] at h0
      exact_mod_cast h0
    have hle : (2 ^ k : ℤ) * (AP.card : ℤ) ≤ (2 ^ k : ℤ) * 3 ^ k := by
      calc (2 ^ k : ℤ) * (AP.card : ℤ)
          = ∑ hP : Fin k → Bool, sgn (linGen rP hP) * ∑ uP : Fin k → Fin 2 → Bool, sgn (linGen (αP uP) hP) := hsum_id
        _ ≤ ∑ hP : Fin k → Bool, |sgn (linGen rP hP) * ∑ uP : Fin k → Fin 2 → Bool, sgn (linGen (αP uP) hP)| :=
            Finset.sum_le_sum fun hP _ => le_abs_self _
        _ = ∑ hP : Fin k → Bool, |∑ uP : Fin k → Fin 2 → Bool, sgn (linGen (αP uP) hP)| :=
            Finset.sum_congr rfl fun hP _ => by rw [abs_mul, sgn_abs, one_mul]
        _ ≤ ∑ hP : Fin k → Bool, (2 ^ k : ℤ) * (2 ^ (k - wt hP) : ℤ) :=
            Finset.sum_le_sum fun hP _ => lane_u_factor_bound k laneP BcoeffP hP
        _ = (2 ^ k : ℤ) * ∑ hP : Fin k → Bool, (2 ^ (k - wt hP) : ℤ) := (Finset.mul_sum ..).symm
        _ ≤ (2 ^ k : ℤ) * 3 ^ k := mul_le_mul_of_nonneg_left hwt_univ (by positivity)
    exact le_of_mul_le_mul_left hle (by positivity)
  have hfiber_Q := case3_fiber_Q m k s hs_pos q b0 l0 a0 hqeq lane P Q rfl rfl hPQ hRad_sub hRad_mem eP eQ
  have hS_bound : 8 * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 ^ k : ℤ) * (3 ^ k : ℤ) * (7 * 2 ^ (5 * s)) := by
    rw [hS_factor, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ k)]
    calc 8 * ((2 ^ k : ℤ) * |∑ uP ∈ AP, ∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ)))|)
        ≤ 8 * ((2 ^ k : ℤ) * ∑ uP ∈ AP, |∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ)))|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)) (by norm_num)
      _ = (2 ^ k : ℤ) * ∑ uP ∈ AP, 8 * |∑ wQ : Fin (2 * s) → Fin 3 → Bool,
            sgn (xor (par (∑ b : Fin (2 * s), (wQ b 0 && wQ b 1 && wQ b 2).toNat))
                     (q (mergeW uP (fun _ => false) wQ)))| := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (2 ^ k : ℤ) * ∑ _uP ∈ AP, (7 * 2 ^ (5 * s) : ℤ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun uP _ => hfiber_Q uP) (by positivity)
      _ = (2 ^ k : ℤ) * ((AP.card : ℤ) * (7 * 2 ^ (5 * s))) := by simp
      _ ≤ (2 ^ k : ℤ) * ((3 ^ k : ℤ) * (7 * 2 ^ (5 * s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAP_card (by positivity)) (by positivity)
      _ = (2 ^ k : ℤ) * (3 ^ k : ℤ) * (7 * 2 ^ (5 * s)) := by ring
  have hfinal_id : (9 ^ s : ℤ) * ((2 ^ k : ℤ) * (3 ^ k : ℤ) * (7 * 2 ^ (5 * s))) =
      7 * 8 ^ s * 6 ^ m := by
    have h9 : (9 ^ s : ℤ) = 3 ^ (2 * s) := by rw [pow_mul]; norm_num
    have h8 : (8 ^ s : ℤ) = 2 ^ (3 * s) := by rw [pow_mul]; norm_num
    have h6 : (6 ^ m : ℤ) = 2 ^ m * 3 ^ m := by rw [← mul_pow]; norm_num
    rw [h9, h8, h6]
    have h2e : (2 ^ k : ℤ) * 2 ^ (5 * s) = 2 ^ (3 * s) * 2 ^ m := by
      rw [← pow_add, ← pow_add]; congr 1; dsimp only [k]; omega
    have h3e : (3 ^ (2 * s) : ℤ) * 3 ^ k = 3 ^ m := by
      rw [← pow_add]; congr 1; dsimp only [k]; omega
    calc (3 ^ (2 * s) : ℤ) * (2 ^ k * 3 ^ k * (7 * 2 ^ (5 * s)))
        = 7 * (3 ^ (2 * s) * 3 ^ k) * (2 ^ k * 2 ^ (5 * s)) := by ring
      _ = 7 * 3 ^ m * (2 ^ (3 * s) * 2 ^ m) := by rw [h3e, h2e]
      _ = 7 * 2 ^ (3 * s) * (2 ^ m * 3 ^ m) := by ring
  calc 8 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|
      = (9 ^ s : ℤ) * (8 * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by ring
    _ ≤ (9 ^ s : ℤ) * ((2 ^ k : ℤ) * (3 ^ k : ℤ) * (7 * 2 ^ (5 * s))) :=
        mul_le_mul_of_nonneg_left hS_bound (by positivity)
    _ = 7 * 8 ^ s * 6 ^ m := hfinal_id

theorem lane_rank_bound_sharp (m s : ℕ) (hs_pos : 0 < s) (hs : 2 * s ≤ m)
    (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (lane : Fin m → Fin 3)
    (hrad : ((Finset.univ : Finset (Fin m → Bool)).filter (fun h => ∀ t : Fin m → Bool,
      xor (xor (q (fun i j => (j == lane i) && xor (h i) (t i)))
               (q (fun i j => (j == lane i) && h i)))
          (xor (q (fun i j => (j == lane i) && t i))
               (q (fun i j => (j == lane i) && false))) = false)).card = 2 ^ (m - 2 * s)) :
    8 * 9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
    7 * 8 ^ s * 6 ^ m := by
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
  have hRad_sub : IsSubgroup Rad := by
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      unfold polar
      have : (fun i => xor false (t i)) = t := by funext i; simp
      rw [this]; cases R t <;> cases R (fun _ => false) <;> rfl
    · intro a ha b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_⟩
      rw [polar_xor_left hRquad, (Finset.mem_filter.mp ha).2 t, (Finset.mem_filter.mp hb).2 t]
      rfl
  have hmul_rad : (Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤
      (2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
        |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
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
    have h1 := mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg Rad.card)
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
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left h3 (by positivity)))
  have hrhs_id : (9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
      ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) =
      (2 ^ (m - 2 * s) : ℤ) * (8 ^ s * 6 ^ m) := by
    have h9 : (9 ^ s : ℤ) = 3 ^ (2 * s) := by rw [pow_mul]; norm_num
    have h8 : (8 ^ s : ℤ) = 2 ^ (3 * s) := by rw [pow_mul]; norm_num
    have h6 : (6 ^ m : ℤ) = 2 ^ m * 3 ^ m := by rw [← mul_pow]; norm_num
    rw [h9, h8, h6]
    have h2exp : (2 ^ (m - s) : ℤ) * 2 ^ m * 2 ^ (2 * s) = 2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    have h3exp : (3 ^ (2 * s) : ℤ) * 3 ^ (m - 2 * s) = 3 ^ m := by
      rw [← pow_add]; congr 1; omega
    calc (3 ^ (2 * s) : ℤ) * (2 ^ (m - s) * 2 ^ m * (3 ^ (m - 2 * s) * 2 ^ (2 * s)))
        = (3 ^ (2 * s) * 3 ^ (m - 2 * s)) * (2 ^ (m - s) * 2 ^ m * 2 ^ (2 * s)) := by ring
      _ = 3 ^ m * (2 ^ (m - 2 * s) * 2 ^ (3 * s) * 2 ^ m) := by rw [h3exp, h2exp]
      _ = 2 ^ (m - 2 * s) * (2 ^ (3 * s) * (2 ^ m * 3 ^ m)) := by ring
  by_cases hCoord : IsCoordSubgroup Rad
  · let P : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∈ Rad)
    let Q : Finset (Fin m) := Finset.univ.filter (fun i => stdBasis i ∉ Rad)
    have hRad_mem := coordSubgroup_mem_iff hRad_sub hCoord
    dsimp only at hRad_mem
    have hPcard : P.card = m - 2 * s := by
      have hc := coordSubgroup_card hRad_sub hCoord
      exact Nat.pow_right_injective (by omega) (hc.symm.trans hRad_card)
    have hQcard : Q.card = 2 * s := by
      have hcomp : Q = Pᶜ := by ext i; simp [P, Q]
      rw [hcomp, Finset.card_compl, Fintype.card_fin, hPcard]; omega
    by_cases hcrossB : ∃ p ∈ P, ∃ q₀ ∈ Q, ∃ r : Fin 2,
        Bcoeff (q₀, otherIdx (lane q₀) r) (p, lane p) = true
    · obtain ⟨p₀, hp₀P, q₀, hq₀Q, r₀, hBpq⟩ := hcrossB
      let d0 : (Fin m → Bool) → Fin m → Bool := fun h j =>
        par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 0) (i, lane i) && h i).toNat)
      let d1 : (Fin m → Bool) → Fin m → Bool := fun h j =>
        par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) 1) (i, lane i) && h i).toNat)
      let K : Finset (Fin m → Bool) :=
        Rad.filter (fun h => ∀ j ∈ Q, d0 h j = false ∧ d1 h j = false)
      have hK_sub : IsSubgroup K := by
        refine ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨hRad_sub.1, fun j _ => ?_⟩
          simp [d0, d1, par]
        · intro a ha b hb
          obtain ⟨haR, haQ⟩ := Finset.mem_filter.mp ha
          obtain ⟨hbR, hbQ⟩ := Finset.mem_filter.mp hb
          refine Finset.mem_filter.mpr ⟨hRad_sub.2 a haR b hbR, fun j hj => ?_⟩
          have hd_xor : ∀ r : Fin 2,
              par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && xor (a i) (b i)).toNat) =
              xor (par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && a i).toNat))
                  (par (∑ i : Fin m, (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && b i).toNat)) := fun r => by
            have hpt : ∀ i, (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && xor (a i) (b i)) =
                xor (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && a i)
                    (Bcoeff (j, otherIdx (lane j) r) (i, lane i) && b i) := fun i => by
              cases Bcoeff (j, otherIdx (lane j) r) (i, lane i) <;> cases a i <;> cases b i <;> rfl
            simp_rw [hpt]; exact par_sum_xor Finset.univ _ _
          exact ⟨by
            have ha1 := (haQ j hj).1; have hb1 := (hbQ j hj).1
            dsimp only [d0] at ha1 hb1 ⊢; rw [hd_xor 0, ha1, hb1]; rfl,
                 by
            have ha2 := (haQ j hj).2; have hb2 := (hbQ j hj).2
            dsimp only [d1] at ha2 hb2 ⊢; rw [hd_xor 1, ha2, hb2]; rfl⟩
      have hep_notK : stdBasis p₀ ∉ K := by
        intro hmem
        have hQ := (Finset.mem_filter.mp hmem).2 q₀ hq₀Q
        have hval : ∀ r : Fin 2,
            par (∑ i : Fin m, (Bcoeff (q₀, otherIdx (lane q₀) r) (i, lane i) && stdBasis p₀ i).toNat) =
            Bcoeff (q₀, otherIdx (lane q₀) r) (p₀, lane p₀) := fun r => by
          have hpt : ∀ i : Fin m, (Bcoeff (q₀, otherIdx (lane q₀) r) (i, lane i) && stdBasis p₀ i) =
              if i = p₀ then Bcoeff (q₀, otherIdx (lane q₀) r) (p₀, lane p₀) else false := fun i => by
            by_cases hi : i = p₀ <;> simp [stdBasis, hi]
          simp_rw [hpt]
          exact par_sum_ite_eq Finset.univ p₀ (Finset.mem_univ _) _
        fin_cases r₀
        · have hB0 : Bcoeff (q₀, otherIdx (lane q₀) 0) (p₀, lane p₀) = true := hBpq
          have := hQ.1; dsimp only [d0] at this; rw [hval 0, hB0] at this; exact Bool.noConfusion this
        · have hB1 : Bcoeff (q₀, otherIdx (lane q₀) 1) (p₀, lane p₀) = true := hBpq
          have := hQ.2; dsimp only [d1] at this; rw [hval 1, hB1] at this; exact Bool.noConfusion this
      have hep_Rad : stdBasis p₀ ∈ Rad := (Finset.mem_filter.mp hp₀P).2
      have hK_lt : K.card < Rad.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,
          fun heq => hep_notK (heq ▸ hep_Rad)⟩)
      obtain ⟨k', hk'm, hKcard, hKsum⟩ := subgroup_wt_bound m K hK_sub
      have hk'_lt : k' < m - 2 * s := by
        rw [hKcard, hRad_card] at hK_lt
        exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hK_lt
      have hzero_out : ∀ h ∈ Rad, h ∉ K →
          ∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h) = 0 := by
        intro h hhR hhnotK
        have hex : ∃ j₀ ∈ Q, d0 h j₀ = true ∨ d1 h j₀ = true := by
          by_contra hall
          push Not at hall
          apply hhnotK
          refine Finset.mem_filter.mpr ⟨hhR, fun j hj => ?_⟩
          have hnot := hall j hj
          exact ⟨Bool.eq_false_iff.mpr hnot.1, Bool.eq_false_iff.mpr hnot.2⟩
        obtain ⟨j₀, hj₀Q, hd⟩ := hex
        have hj₀_notP : j₀ ∉ P := by
          intro hjP
          exact (Finset.mem_filter.mp hj₀Q).2 (Finset.mem_filter.mp hjP).2
        have hh_j0 : h j₀ = false := (hRad_mem h).mp hhR j₀ hj₀_notP
        exact lane_u_factor_eq_zero m lane Bcoeff h j₀ hh_j0 hd
      have hsum_eq_K : (∑ h ∈ Rad,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) =
          ∑ h ∈ K,
            |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)| := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun h hhR hhnotK => ?_
        rw [hzero_out h hhR hhnotK, abs_zero]
      have hwt_K : (∑ h ∈ K, (2 ^ (m - wt h) : ℤ)) ≤ (3 ^ k' : ℤ) * (2 ^ (m - k') : ℤ) := by
        have h0 := hKsum (fun _ => false)
        have hsimpl : ∀ h ∈ K, 2 ^ (m - wt (fun i => xor false (h i))) = 2 ^ (m - wt h) := fun h _ => by simp
        rw [Finset.sum_congr rfl hsimpl] at h0
        exact_mod_cast h0
      have h23 : 3 * ((3 ^ k' : ℤ) * (2 ^ (m - k') : ℤ)) ≤ 2 * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)) := by
        let d := (m - 2 * s) - k'
        have hd : 1 ≤ d := by omega
        have hpow_le : (2 ^ (d - 1) : ℤ) ≤ 3 ^ (d - 1) := by
          exact_mod_cast Nat.pow_le_pow_left (by omega : 2 ≤ 3) (d - 1)
        have hlhs : 3 * ((3 ^ k' : ℤ) * (2 ^ (m - k') : ℤ)) =
            3 ^ (k' + 1) * 2 ^ (2 * s + 1) * 2 ^ (d - 1) := by
          have : m - k' = (2 * s + 1) + (d - 1) := by omega
          rw [this, pow_add, pow_succ']; ring
        have hrhs : 2 * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)) =
            3 ^ (k' + 1) * 2 ^ (2 * s + 1) * 3 ^ (d - 1) := by
          have : m - 2 * s = (k' + 1) + (d - 1) := by omega
          rw [this, pow_add, pow_succ']; ring
        rw [hlhs, hrhs]
        exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
      have hmain3 : 3 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) ≤
          2 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) := by
        calc 3 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)
            = 3 * ((Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by
              rw [hRad_card]; push_cast; rfl
          _ ≤ 3 * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
                |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) :=
              mul_le_mul_of_nonneg_left hmul_rad (by norm_num)
          _ = 3 * ((2 ^ (m - s) : ℤ) * ∑ h ∈ K,
                |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) := by
              rw [hsum_eq_K]
          _ ≤ 3 * ((2 ^ (m - s) : ℤ) * ∑ h ∈ K, (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun h _ => lane_u_factor_bound m lane Bcoeff h) (by positivity)) (by norm_num)
          _ = (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (3 * ∑ h ∈ K, (2 ^ (m - wt h) : ℤ)) := by
              rw [← Finset.mul_sum]; ring
          _ ≤ (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (3 * ((3 ^ k' : ℤ) * (2 ^ (m - k') : ℤ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt_K (by norm_num)) (by positivity)
          _ ≤ (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (2 * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) :=
              mul_le_mul_of_nonneg_left h23 (by positivity)
          _ = 2 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) := by ring
      have hstep : (2 ^ (m - 2 * s) : ℤ) * (3 * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
          sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)) ≤
          (2 ^ (m - 2 * s) : ℤ) * (2 * (8 ^ s * 6 ^ m)) := by
        calc (2 ^ (m - 2 * s) : ℤ) * (3 * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|))
            = (9 ^ s : ℤ) * (3 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
                sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)) := by ring
          _ ≤ (9 ^ s : ℤ) * (2 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
                ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) :=
              mul_le_mul_of_nonneg_left hmain3 (by positivity)
          _ = 2 * ((9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
                ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) := by ring
          _ = (2 ^ (m - 2 * s) : ℤ) * (2 * (8 ^ s * 6 ^ m)) := by rw [hrhs_id]; ring
      have h32 := le_of_mul_le_mul_left hstep (by positivity : (0 : ℤ) < 2 ^ (m - 2 * s))
      have hnonneg : (0 : ℤ) ≤ 8 ^ s * 6 ^ m := by positivity
      linarith
    · push Not at hcrossB
      exact lane_rank_case3_coord_zero m s hs_pos hs q b0 l0 a0 hqeq lane hCoord hRad_card hcrossB
  · obtain ⟨k, hkm, hRad_k, hwt_sum⟩ := subgroup_wt_bound_noncoord m Rad hRad_sub hCoord
    have hk_eq : k = m - 2 * s := Nat.pow_right_injective (by omega) (hRad_k.symm.trans hRad_card)
    have hwt_nat : 6 * ∑ h ∈ Rad, 2 ^ (m - wt h) ≤ 5 * (3 ^ (m - 2 * s) * 2 ^ (2 * s)) := by
      have h0 := hwt_sum (fun _ => false)
      have hsimpl : ∀ h ∈ Rad, 2 ^ (m - wt (fun i => xor false (h i))) = 2 ^ (m - wt h) := fun h _ => by simp
      rw [Finset.sum_congr rfl hsimpl, hk_eq] at h0
      have hsub : m - (m - 2 * s) = 2 * s := by omega
      rwa [hsub] at h0
    have hwt_int : 6 * (∑ h ∈ Rad, (2 ^ (m - wt h) : ℤ)) ≤ 5 * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)) := by
      exact_mod_cast hwt_nat
    have hmain6 : 6 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) ≤
        5 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) := by
      calc 6 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)
          = 6 * ((Rad.card : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|) := by
            rw [hRad_card]; push_cast; rfl
        _ ≤ 6 * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad,
              |∑ u : Fin m → Fin 2 → Bool, sgn (linGen (fun i => xor (u i 0 && u i 1) (ν u i)) h)|) :=
            mul_le_mul_of_nonneg_left hmul_rad (by norm_num)
        _ ≤ 6 * ((2 ^ (m - s) : ℤ) * ∑ h ∈ Rad, (2 ^ m : ℤ) * (2 ^ (m - wt h) : ℤ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun h _ => lane_u_factor_bound m lane Bcoeff h) (by positivity)) (by norm_num)
        _ = (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (6 * ∑ h ∈ Rad, (2 ^ (m - wt h) : ℤ)) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ (2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * (5 * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) :=
            mul_le_mul_of_nonneg_left hwt_int (by positivity)
        _ = 5 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) * ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ))) := by ring
    have hstep : (2 ^ (m - 2 * s) : ℤ) * (6 * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
        sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)) ≤
        (2 ^ (m - 2 * s) : ℤ) * (5 * (8 ^ s * 6 ^ m)) := by
      calc (2 ^ (m - 2 * s) : ℤ) * (6 * (9 ^ s * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|))
          = (9 ^ s : ℤ) * (6 * ((2 ^ (m - 2 * s) : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
              sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))|)) := by ring
        _ ≤ (9 ^ s : ℤ) * (5 * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
              ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) :=
            mul_le_mul_of_nonneg_left hmain6 (by positivity)
        _ = 5 * ((9 ^ s : ℤ) * ((2 ^ (m - s) : ℤ) * (2 ^ m : ℤ) *
              ((3 ^ (m - 2 * s) : ℤ) * (2 ^ (2 * s) : ℤ)))) := by ring
        _ = (2 ^ (m - 2 * s) : ℤ) * (5 * (8 ^ s * 6 ^ m)) := by rw [hrhs_id]; ring
    have h65 := le_of_mul_le_mul_left hstep (by positivity : (0 : ℤ) < 2 ^ (m - 2 * s))
    have hnonneg : (0 : ℤ) ≤ 8 ^ s * 6 ^ m := by positivity
    linarith

theorem cross_gap_bound_sharp (m : ℕ) (q : (Fin m → Fin 3 → Bool) → Bool)
    (b0 : Bool) (l0 : (Fin m × Fin 3) → Bool) (a0 : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool)
    (hqeq : ∀ w, q w = xor (xor b0 (par (∑ j : Fin m × Fin 3, (l0 j && w j.1 j.2).toNat)))
      (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a0 i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (i j : Fin m × Fin 3) (hij : i.1 ≠ j.1) (hcross : xor (a0 i j) (a0 j i) = true) :
    |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))| ≤ 28 * 6 ^ (m - 2) := by
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
      funext ⟨k, l⟩; rcases i with ⟨i1, i2⟩; by_cases hk : k = i1
      · subst hk; by_cases hl : l = i2
        · subst hl; simp [ei, hlane_i]
        · simp [ei, hlane_i, hl, beq_false_of_ne hl]
      · simp [ei, hk]
    have he2 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && decide (p.1 = j.1)) = ej := by
      funext ⟨k, l⟩; rcases j with ⟨j1, j2⟩; by_cases hk : k = j1
      · subst hk; by_cases hl : l = j2
        · subst hl; simp [ej, hlane_j]
        · simp [ej, hlane_j, hl, beq_false_of_ne hl]
      · simp [ej, hk]
    have he12 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && xor (decide (p.1 = i.1)) (decide (p.1 = j.1))) =
        fun p => xor (ei p) (ej p) := by
      funext p
      have h1 := congrFun he1 p; have h2 := congrFun he2 p
      rw [← h1, ← h2]
      cases (p.2 == lane p.1) <;> cases decide (p.1 = i.1) <;> cases decide (p.1 = j.1) <;> rfl
    have he0 : (fun p : Fin m × Fin 3 => (p.2 == lane p.1) && false) = fun _ => false := by funext p; simp
    have hpeq : polar R (fun k => decide (k = i.1)) (fun k => decide (k = j.1)) = polar Qv ei ej := by
      unfold polar; rw [hR1, hR1, hR1, hR1, he1, he2, he12, he0]
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
      · intro p₁ _ hne; exact Finset.sum_eq_zero fun p₂ _ => by simp [ei, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, par_toNat, hcross]
  have hs1 : 0 < s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    subst hs_eq
    simp only [mul_zero, Nat.sub_zero] at hrad
    have hRad_univ : (Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false)) = Finset.univ := by
      apply Finset.eq_univ_of_card; rw [hrad]; simp [Fintype.card_fun]
    have hmem : (fun k => decide (k = i.1)) ∈
        Finset.univ.filter (fun h : Fin m → Bool => ∀ t, polar R h t = false) := by
      rw [hRad_univ]; exact Finset.mem_univ _
    have hf := (Finset.mem_filter.mp hmem).2 (fun k => decide (k = j.1))
    rw [hpol_true] at hf; exact Bool.noConfusion hf
  have hm2 : 2 ≤ m := by omega
  have hrb := lane_rank_bound_sharp m s hs1 hs q hq lane hrad
  have h89 : (8 ^ s : ℤ) ≤ 8 * 9 ^ (s - 1) := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
    have hle : (8 ^ (s - 1) : ℤ) ≤ 9 ^ (s - 1) := by
      exact_mod_cast Nat.pow_le_pow_left (by omega : 8 ≤ 9) (s - 1)
    nlinarith
  have h6eq : (6 ^ m : ℤ) = 36 * 6 ^ (m - 2) := by
    have : m = (m - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  have h9eq : (9 ^ s : ℤ) = 9 * 9 ^ (s - 1) := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
  have hstep : (8 * 9 ^ s : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))| ≤
      (8 * 9 ^ s : ℤ) * (28 * 6 ^ (m - 2)) := by
    calc (8 * 9 ^ s : ℤ) * |∑ w : Fin m → Fin 3 → Bool,
            sgn (xor (par (∑ k : Fin m, (w k 0 && w k 1 && w k 2).toNat)) (q w))|
        ≤ 7 * 8 ^ s * 6 ^ m := hrb
      _ ≤ 7 * (8 * 9 ^ (s - 1)) * 6 ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h89 (by norm_num)) (by positivity)
      _ = 7 * (8 * 9 ^ (s - 1)) * (36 * 6 ^ (m - 2)) := by rw [h6eq]
      _ = (8 * (9 * 9 ^ (s - 1))) * (28 * 6 ^ (m - 2)) := by ring
      _ = (8 * 9 ^ s : ℤ) * (28 * 6 ^ (m - 2)) := by rw [← h9eq]
  exact le_of_mul_le_mul_left hstep (by positivity)

theorem evalQuad3_lt6_le4 : ∀ c0 l0 l1 l2 q01 q02 q12 : Bool,
    let S : ℤ := ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool,
      sgn (xor (b0 && b1 && b2) (evalQuad3 c0 l0 l1 l2 q01 q02 q12 b0 b1 b2))
    |S| < 6 → |S| ≤ 4 := by
  decide

theorem single_triple_lt6_le4 (b0 : Bool) (l0 : Fin 3 → Bool) (a0 : Fin 3 → Fin 3 → Bool) :
    let g := quadFormGen b0 l0 a0
    |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (g x))| < 6 →
    |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (g x))| ≤ 4 := by
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
    all_goals try rfl
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
  exact evalQuad3_lt6_le4 c0 k0 k1 k2 q01 q02 q12

theorem lt_six_pow_le_second (m : ℕ) (hm : 2 ≤ m) (q : (Fin m → Fin 3 → Bool) → Bool)
    (hq : ∃ (b : Bool) (l : (Fin m × Fin 3) → Bool) (a : (Fin m × Fin 3) → (Fin m × Fin 3) → Bool),
      ∀ w, q w = xor (xor b (par (∑ j : Fin m × Fin 3, (l j && w j.1 j.2).toNat)))
        (par (∑ i : Fin m × Fin 3, ∑ j : Fin m × Fin 3, (a i j && w i.1 i.2 && w j.1 j.2).toNat)))
    (hlt : |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| < 6 ^ m) :
    |∑ w : Fin m → Fin 3 → Bool,
      sgn (xor (par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| ≤ 28 * 6 ^ (m - 2) := by
  obtain ⟨b0, l0, a0, hqeq⟩ := hq
  by_cases hcr : ∃ p₁ p₂ : Fin m × Fin 3, p₁.1 ≠ p₂.1 ∧ xor (a0 p₁ p₂) (a0 p₂ p₁) = true
  · obtain ⟨p₁, p₂, hne, hxt⟩ := hcr
    exact cross_gap_bound_sharp m q b0 l0 a0 hqeq p₁ p₂ hne hxt
  · push Not at hcr
    have hno_cross : ∀ p₁ p₂ : Fin m × Fin 3, p₁.1 ≠ p₂.1 → a0 p₁ p₂ = a0 p₂ p₁ := by
      intro p₁ p₂ hne
      have h := hcr p₁ p₂ hne
      cases h1 : a0 p₁ p₂ <;> cases h2 : a0 p₂ p₁ <;> rw [h1, h2] at h <;> first | rfl | exact absurd rfl h
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
        have hm' : (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 0 ∨
            (∑ k : Fin 3, (l0 (i, k) && w i k).toNat) % 2 = 1 := by omega
        rcases hm' with hm' | hm' <;> simp [hm']
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
          · congr 1; ext p
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            rcases lt_trichotomy p.1.1 p.2.1 with h | h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rw [Finset.disjoint_left]; intro p hp1 hp2
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
            rcases hp1 with h | h <;> omega
          · rw [Finset.disjoint_left]; intro p hp1 hp2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2; omega
        have hlt_gt : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.2.1 < p.1.1), F p) =
            ∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 < p.2.1), F p := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
          · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p₁ _ p₂ _ h; exact Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
          · intro p hp; refine ⟨(p.2, p.1), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p hp
            have hne : p.1.1 ≠ p.2.1 := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; omega
            dsimp only [F]; rw [hno_cross p.1 p.2 hne]; congr 1
            cases a0 p.2 p.1 <;> cases w p.1.1 p.1.2 <;> cases w p.2.1 p.2.2 <;> rfl
        have hdiag : (∑ p ∈ Finset.univ.filter (fun p : (Fin m × Fin 3) × (Fin m × Fin 3) => p.1.1 = p.2.1), F p) =
            ∑ i : Fin m, ∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat := by
          rw [Finset.sum_filter]
          trans (∑ i : Fin m, ∑ k₁ : Fin 3, ∑ p₂ : Fin m × Fin 3, if i = p₂.1 then F ((i, k₁), p₂) else 0)
          · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
          · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k₁ _ => ?_
            rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
            · simp [F]
            · intro j _ hne; exact Finset.sum_eq_zero fun k₂ _ => by simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
        rw [hpart, hlt_gt, hdiag]
        have heven : ∀ a b : ℕ, par (a + b + b) = par a := fun a b => by
          have : (a + b + b) % 2 = a % 2 := by omega
          simp [par, this]
        rw [heven]
        refine par_sum_congr_mod Finset.univ _ _ fun i _ => ?_
        unfold par
        have hm' : (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 0 ∨
            (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, (a0 (i, k₁) (i, k₂) && w i k₁ && w i k₂).toNat) % 2 = 1 := by omega
        rcases hm' with hm' | hm' <;> simp [hm']
      rw [hlin_split, hquad_split, Bool.xor_assoc, ← par_sum_xor]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [qi, quadFormGen]; simp
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
    rw [hprod] at hlt ⊢
    have hle_each : ∀ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| ≤ 6 := fun i =>
      (single_triple_quad_bound false (fun k => l0 (i, k)) (fun k₁ k₂ => a0 (i, k₁) (i, k₂))).1
    have hex_lt : ∃ i₀ : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| < 6 := by
      by_contra hall
      push Not at hall
      have heq6 : ∀ i : Fin m, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i x))| = 6 := fun i =>
        le_antisymm (hle_each i) (hall i)
      simp_rw [heq6] at hlt
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hlt
      omega
    obtain ⟨i₀, hi₀_lt⟩ := hex_lt
    have hi₀_le4 : |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| ≤ 4 :=
      single_triple_lt6_le4 false (fun k => l0 (i₀, k)) (fun k₁ k₂ => a0 (i₀, k₁) (i₀, k₂)) hi₀_lt
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    have hrest_le : (∏ j ∈ Finset.univ.erase i₀,
        |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|) ≤ 6 ^ (m - 1) := by
      calc (∏ j ∈ Finset.univ.erase i₀, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|)
          ≤ ∏ _j ∈ Finset.univ.erase i₀, (6 : ℤ) :=
            prod_le_prod_nonneg _ _ _ (fun j _ => abs_nonneg _) (fun j _ => hle_each j)
        _ = 6 ^ (m - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    have h6eq : (6 ^ (m - 1) : ℤ) = 6 * 6 ^ (m - 2) := by
      have : m - 1 = (m - 2) + 1 := by omega
      rw [this, pow_succ']
    calc |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi i₀ x))| *
            ∏ j ∈ Finset.univ.erase i₀, |∑ x : Fin 3 → Bool, sgn (xor (x 0 && x 1 && x 2) (qi j x))|
        ≤ 4 * 6 ^ (m - 1) :=
          mul_le_mul hi₀_le4 hrest_le (Finset.prod_nonneg fun j _ => abs_nonneg _) (by norm_num)
      _ = 24 * 6 ^ (m - 2) := by rw [h6eq]; ring
      _ ≤ 28 * 6 ^ (m - 2) := by
          have : (0 : ℤ) ≤ 6 ^ (m - 2) := by positivity
          linarith

end PEqualNP.Outside.L_lib_441

theorem PEqualNP.Outside.L_lib_441 : ∀ m : Nat,
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
    (∀ (lane : Fin m → Fin 3) (s : Nat), 0 < s → 2*s ≤ m →
      radicalSize q lane = 2^(m-2*s) → 8 * 9^s * gap Finset.univ q ≤ 7 * 8^s * 6^m) ∧
    (2 ≤ m → (gap Finset.univ q < 6^m ↔ gap Finset.univ q ≤ 28*6^(m-2))) ∧
    (cross q → gap Finset.univ q ≤ 28*6^(m-2))) ∧
  (2 ≤ m → ∃ q : W → Bool, quad q ∧ cross q ∧ gap Finset.univ q = 28*6^(m-2)) := by
  intro m W J get par lin quad f gap flip cross radicalSize
  constructor
  · intro q hq
    have hgap_int : (gap Finset.univ q : ℤ) =
        |∑ w : Fin m → Fin 3 → Bool,
          PEqualNP.Outside.L_lib_441.sgn
            (xor (PEqualNP.Outside.L_lib_441.par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| := by
      dsimp only [gap]
      rw [← Int.abs_eq_natAbs, PEqualNP.Outside.L_lib_441.gap_eq_natAbs_sum]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · intro lane s hs_pos hs hrad
      have h := PEqualNP.Outside.L_lib_441.lane_rank_bound_sharp m s hs_pos hs q hq lane hrad
      rw [← hgap_int] at h
      exact_mod_cast h
    · intro hm
      constructor
      · intro hlt
        have hlt_int : |∑ w : Fin m → Fin 3 → Bool,
            PEqualNP.Outside.L_lib_441.sgn
              (xor (PEqualNP.Outside.L_lib_441.par (∑ i : Fin m, (w i 0 && w i 1 && w i 2).toNat)) (q w))| < 6 ^ m := by
          rw [← hgap_int]; exact_mod_cast hlt
        have h := PEqualNP.Outside.L_lib_441.lt_six_pow_le_second m hm q hq hlt_int
        rw [← hgap_int] at h
        exact_mod_cast h
      · intro hle
        have h6 : 6 ^ m = 36 * 6 ^ (m - 2) := by
          have : m = (m - 2) + 2 := by omega
          conv_lhs => rw [this, pow_add]
          ring
        have hpos : 0 < 6 ^ (m - 2) := by positivity
        omega
    · intro hcr
      obtain ⟨b0, l0, a0, hqeq⟩ := hq
      obtain ⟨i, j, w, hij, hdiff⟩ := hcr
      have hxt : xor (a0 i j) (a0 j i) = true := by
        have := PEqualNP.Outside.L_lib_441.flip_second_diff q b0 l0 a0 hqeq i j w
        dsimp only at this
        rw [← this]; exact hdiff
      have h := PEqualNP.Outside.L_lib_441.cross_gap_bound_sharp m q b0 l0 a0 hqeq i j hij hxt
      rw [← hgap_int] at h
      exact_mod_cast h
  · intro hm
    exact PEqualNP.Outside.L_lib_441.cross_witness_exists m hm

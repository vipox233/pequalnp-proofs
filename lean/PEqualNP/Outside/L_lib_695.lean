import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_695_aux

open Finset

theorem key (n : ℕ) : ∀ (s : Multiset ℕ), s.card = n → ∀ t : ℕ,
    2 ^ t ∣ (s.map (fun b => 2 ^ b)).sum → ∀ a ∈ s, t ≤ a + n - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs t hdvd a ha
  obtain ⟨m, hm, hmin⟩ := s.toFinset.exists_min_image id ⟨a, Multiset.mem_toFinset.mpr ha⟩
  rw [Multiset.mem_toFinset] at hm
  simp only [id, Multiset.mem_toFinset] at hmin
  have hma := hmin a ha
  have hn : 1 ≤ n := by rw [← hs]; exact Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩
  suffices t ≤ m + n - 1 by omega
  by_cases htm : t ≤ m
  · omega
  push Not at htm
  have hsplit := Multiset.filter_add_not (fun x => x = m) s
  rw [Multiset.filter_eq' s m] at hsplit
  have hrest : 2 ^ (m+1) ∣ ((s.filter (fun x => ¬ x = m)).map (fun b => 2 ^ b)).sum := by
    apply Multiset.dvd_sum
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Multiset.mem_filter] at hx
    have : m < x := lt_of_le_of_ne (hmin x hx.1) (Ne.symm hx.2)
    exact pow_dvd_pow 2 this
  have htot : 2 ^ (m+1) ∣ (s.map (fun b => 2 ^ b)).sum := (pow_dvd_pow 2 htm).trans hdvd
  rw [← hsplit, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Multiset.sum_replicate, smul_eq_mul] at htot
  have hc : 2 ^ (m+1) ∣ Multiset.count m s * 2 ^ m := (Nat.dvd_add_left hrest).mp htot
  rw [pow_succ, mul_comm (2^m) 2] at hc
  have hc2 : 2 ∣ Multiset.count m s := Nat.dvd_of_mul_dvd_mul_right (by positivity) hc
  have hc1 : 1 ≤ Multiset.count m s := Multiset.one_le_count_iff_mem.mpr hm
  have hc2' : 2 ≤ Multiset.count m s := by obtain ⟨k, hk⟩ := hc2; omega
  have hm' : m ∈ s.erase m := by
    rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self]; omega
  have hs_eq : s = m ::ₘ m ::ₘ ((s.erase m).erase m) := by
    rw [Multiset.cons_erase hm', Multiset.cons_erase hm]
  have hcard' : ((m+1) ::ₘ ((s.erase m).erase m)).card = n - 1 := by
    have := congrArg Multiset.card hs_eq
    simp only [Multiset.card_cons] at this ⊢; omega
  have hsum' : (((m+1) ::ₘ ((s.erase m).erase m)).map (fun b => 2^b)).sum
      = (s.map (fun b => 2^b)).sum := by
    conv_rhs => rw [hs_eq]
    simp only [Multiset.map_cons, Multiset.sum_cons, pow_succ]; ring
  have := ih (n-1) (by omega) _ hcard' t (hsum' ▸ hdvd) (m+1) (Multiset.mem_cons_self _ _)
  omega

theorem prod_eq {ι : Type*} [Fintype ι] (ch : ι → ℕ) (h : ι → ℕ) (hch : ∀ t, ch t ≤ 2)
    (h0 : ∀ t, ch t = 0 → h t = 0) :
    (∏ t, ch t ^ h t) * 2 ^ (∑ t ∈ univ.filter (fun u => ch u = 1), h t) = 2 ^ (∑ t, h t) := by
  have e1 : ∀ t, ch t ^ h t = 2 ^ (if ch t = 2 then h t else 0) := by
    intro t
    obtain hc | hc | hc : ch t = 0 ∨ ch t = 1 ∨ ch t = 2 := by have := hch t; omega
    · simp [hc, h0 t hc]
    · simp [hc]
    · simp [hc]
  rw [Finset.prod_congr rfl (fun t _ => e1 t), Finset.prod_pow_eq_pow_sum, Finset.sum_filter,
    ← pow_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  obtain hc | hc | hc : ch t = 0 ∨ ch t = 1 ∨ ch t = 2 := by have := hch t; omega
  · simp [hc, h0 t hc]
  · simp [hc]
  · simp [hc]

def fib {α ι : Type*} [Fintype ι] (ok : α → Prop) [DecidablePred ok] (ch : ι → α → ℕ)
    (h : ι → ℕ) (w : α) : ℕ :=
  if ok w then ∏ t, ch t w ^ h t else 0

theorem live_iff {α ι : Type*} [Fintype ι] (ok : α → Prop) [DecidablePred ok]
    (ch : ι → α → ℕ) (h : ι → ℕ) (w : α) :
    0 < fib ok ch h w ↔ ok w ∧ ∀ t, ch t w = 0 → h t = 0 := by
  unfold fib
  split_ifs with hok
  · simp only [Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff, mem_univ, true_implies,
      ne_eq, pow_eq_zero_iff', not_and, not_not, hok, true_and]
  · simp [hok]

theorem part1 {α ι : Type*} [Fintype α] [Fintype ι] (c d : ℕ) (ok : α → Prop) [DecidablePred ok]
    (ch : ι → α → ℕ) (hch : ∀ t w, ch t w ≤ 2) (h : ι → ℕ)
    (hdiv : 2 ^ (c + ∑ t, h t) ∣ (∑ w, fib ok ch h w) * 2 ^ d) :
    ∀ w, 0 < fib ok ch h w →
      c + ∑ t ∈ univ.filter (fun u => ch u w = 1), h t
        ≤ d + (univ.filter (fun w => 0 < fib ok ch h w)).card - 1 := by
  intro w0 hw0
  set S := univ.filter (fun w => 0 < fib ok ch h w) with hS
  set W := c + ∑ t, h t with hW
  let e : α → ℕ := fun w => c + ∑ t ∈ univ.filter (fun u => ch u w = 1), h t
  have he_le : ∀ w, e w ≤ W := by
    intro w
    have : ∑ t ∈ univ.filter (fun u => ch u w = 1), h t ≤ ∑ t, h t :=
      Finset.sum_le_sum_of_subset (filter_subset _ _)
    simp only [e, hW]; omega
  have hfib : ∀ w ∈ S, fib ok ch h w = 2 ^ (W - e w) := by
    intro w hw
    rw [hS, mem_filter, live_iff] at hw
    have hp := prod_eq (fun t => ch t w) h (fun t => hch t w) hw.2.2
    have hfw : fib ok ch h w = ∏ t, ch t w ^ h t := by simp [fib, hw.2.1]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos two_pos (e w))
    rw [← pow_add, Nat.sub_add_cancel (he_le w), hfw, hW]
    simp only [e, pow_add]
    rw [← hp]; ring
  have hsum : (∑ w, fib ok ch h w) * 2 ^ d = ∑ w ∈ S, 2 ^ (W - e w + d) := by
    rw [Finset.sum_mul, ← Finset.sum_filter_of_ne (p := fun w => 0 < fib ok ch h w)
      (fun x _ hx => Nat.pos_of_ne_zero (left_ne_zero_of_mul hx))]
    apply Finset.sum_congr rfl
    intro w hw
    rw [hfib w hw, pow_add]
  rw [hsum, Finset.sum_eq_multiset_sum] at hdiv
  have hdiv' : 2 ^ W ∣ ((S.val.map (fun w => W - e w + d)).map (fun b => 2 ^ b)).sum := by
    rw [Multiset.map_map]; exact hdiv
  have hw0S : w0 ∈ S := by rw [hS, mem_filter]; exact ⟨mem_univ _, hw0⟩
  have hk := key S.card (S.val.map (fun w => W - e w + d)) (by simp) W hdiv'
    (W - e w0 + d) (Multiset.mem_map_of_mem _ hw0S)
  have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨w0, hw0S⟩
  have := he_le w0
  show e w0 ≤ d + S.card - 1
  omega

theorem part2 {α ι : Type*} [Fintype α] [Fintype ι] (c d : ℕ) (ok : α → Prop) [DecidablePred ok]
    (ch : ι → α → ℕ) (hch : ∀ t w, ch t w ≤ 2) (hcard : Fintype.card α ≤ 2 ^ c) (h : ι → ℕ)
    (hdiv : 2 ^ (c + ∑ t, h t) ∣ (∑ w, fib ok ch h w) * 2 ^ d) :
    ∀ w, fib ok ch (fun t => min (h t) (d + 2 ^ c)) w * 2 ^ (c + ∑ t, h t)
      = fib ok ch h w * 2 ^ (c + ∑ t, min (h t) (d + 2 ^ c)) := by
  intro w
  have hB : 1 ≤ d + 2 ^ c := by have := Nat.one_le_two_pow (n := c); omega
  by_cases hok : ok w
  swap
  · simp [fib, hok]
  by_cases hz : ∃ t, ch t w = 0 ∧ h t ≠ 0
  · obtain ⟨t, ht0, hth⟩ := hz
    have e1 : fib ok ch h w = 0 := by
      simp only [fib, hok, ite_true]
      exact Finset.prod_eq_zero (mem_univ t) (by rw [ht0]; exact zero_pow hth)
    have e2 : fib ok ch (fun t => min (h t) (d + 2 ^ c)) w = 0 := by
      simp only [fib, hok, ite_true]
      exact Finset.prod_eq_zero (mem_univ t) (by rw [ht0]; exact zero_pow (by omega))
    rw [e1, e2]; simp
  push Not at hz
  have hlive : 0 < fib ok ch h w := (live_iff ok ch h w).mpr ⟨hok, hz⟩
  have h1 := part1 c d ok ch hch h hdiv w hlive
  have hL : (univ.filter (fun w => 0 < fib ok ch h w)).card ≤ 2 ^ c :=
    (Finset.card_le_univ _).trans hcard
  have hsmall : ∀ t ∈ univ.filter (fun u => ch u w = 1), min (h t) (d + 2 ^ c) = h t := by
    intro t ht
    have : h t ≤ ∑ t ∈ univ.filter (fun u => ch u w = 1), h t :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht
    omega
  have hS1 : ∑ t ∈ univ.filter (fun u => ch u w = 1), min (h t) (d + 2 ^ c)
      = ∑ t ∈ univ.filter (fun u => ch u w = 1), h t := Finset.sum_congr rfl hsmall
  have hz' : ∀ t, ch t w = 0 → min (h t) (d + 2 ^ c) = 0 := by
    intro t ht; rw [hz t ht]; simp
  have ph := prod_eq (fun t => ch t w) h (fun t => hch t w) hz
  have pc := prod_eq (fun t => ch t w) (fun t => min (h t) (d + 2 ^ c)) (fun t => hch t w) hz'
  rw [hS1] at pc
  simp only [fib, hok, ite_true]
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos two_pos (∑ t ∈ univ.filter (fun u => ch u w = 1), h t))
  calc (∏ t, ch t w ^ min (h t) (d + 2 ^ c)) * 2 ^ (c + ∑ t, h t)
        * 2 ^ (∑ t ∈ univ.filter (fun u => ch u w = 1), h t)
      = ((∏ t, ch t w ^ min (h t) (d + 2 ^ c))
          * 2 ^ (∑ t ∈ univ.filter (fun u => ch u w = 1), h t)) * 2 ^ (c + ∑ t, h t) := by ring
    _ = 2 ^ (∑ t, min (h t) (d + 2 ^ c)) * 2 ^ (c + ∑ t, h t) := by rw [pc]
    _ = 2 ^ (∑ t, h t) * 2 ^ (c + ∑ t, min (h t) (d + 2 ^ c)) := by ring
    _ = ((∏ t, ch t w ^ h t) * 2 ^ (∑ t ∈ univ.filter (fun u => ch u w = 1), h t))
          * 2 ^ (c + ∑ t, min (h t) (d + 2 ^ c)) := by rw [ph]
    _ = _ := by ring

end PEqualNP.Outside.L_lib_695_aux

open PEqualNP.Outside.L_lib_695_aux


theorem PEqualNP.Outside.L_lib_695 : (let W := fun k : ℕ => Fin k → Bool
let Lit := fun k : ℕ => Fin k × Bool
let F := fun k : ℕ => Finset (Lit k × Lit k)
∀ c d : ℕ,
  let T := Finset (Lit c × Bool)
  let choices := fun (t : T) (w : W c) =>
    (Finset.univ.filter (fun b : Bool => ∀ edge ∈ t,
      w edge.1.1 ≠ edge.1.2 ∨ b ≠ edge.2)).card
  let width := fun h : T → ℕ => c + ∑ t, h t
  let fiber := fun (D : F c) (h : T → ℕ) (w : W c) =>
    if ∀ e ∈ D, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2 then
      ∏ t, (choices t w) ^ (h t)
    else 0
  let score := fun (D : F c) (h : T → ℕ) => ∑ w, fiber D h w
  ∀ (D : F c) (h : T → ℕ), 2 ^ (width h) ∣ score D h * 2 ^ d →
    let B := d + 2 ^ c
    let cropped := fun t : T => min (h t) B
    let live := (Finset.univ.filter (fun w : W c => 0 < fiber D h w)).card
    (∀ w : W c, 0 < fiber D h w →
      c + ∑ t ∈ (Finset.univ.filter (fun u : T => choices u w = 1)), h t ≤ d + live - 1) ∧
    ∀ w : W c, fiber D cropped w * 2 ^ (width h) = fiber D h w * 2 ^ (width cropped)) := by
  intro W Lit F c d T choices width fiber score D h hdiv B cropped live
  have hch : ∀ (t : T) (w : W c), choices t w ≤ 2 := by
    intro t w
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hcard : Fintype.card (W c) ≤ 2 ^ c := by simp [W]
  exact ⟨part1 c d _ choices hch h hdiv, part2 c d _ choices hch hcard h hdiv⟩

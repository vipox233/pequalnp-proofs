import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_657_aux

theorem foldl_congr_aux {α β σ : Type*} (g : σ → β → σ) (ch ch' : α → β) :
    ∀ (L : List α) (s : σ), (∀ a ∈ L, ch a = ch' a) →
      L.foldl (fun u a => g u (ch a)) s = L.foldl (fun u a => g u (ch' a)) s := by
  intro L
  induction L with
  | nil => intro s _; rfl
  | cons a L ih =>
    intro s h
    simp only [List.foldl_cons]
    rw [h a (by simp)]
    exact ih _ (fun x hx => h x (by simp [hx]))

theorem exists_choices {α β σ : Type*} [DecidableEq α] (b0 : β) (g : σ → β → σ)
    (Inv : σ → ℕ → Prop) (hstep : ∀ s m, Inv s (m+1) → ∃ k, Inv (g s k) m) :
    ∀ (L : List α), L.Nodup → ∀ s, Inv s L.length →
      ∃ ch : α → β, Inv (L.foldl (fun u a => g u (ch a)) s) 0 := by
  intro L
  induction L with
  | nil => intro _ s hs; exact ⟨fun _ => b0, hs⟩
  | cons a L ih =>
    intro hnd s hs
    rw [List.nodup_cons] at hnd
    obtain ⟨k, hk⟩ := hstep s L.length hs
    obtain ⟨ch', hch'⟩ := ih hnd.2 (g s k) hk
    refine ⟨Function.update ch' a k, ?_⟩
    simp only [List.foldl_cons, Function.update_self]
    rw [foldl_congr_aux g (Function.update ch' a k) ch' L (g s k)]
    · exact hch'
    · intro x hx
      have : x ≠ a := fun h => hnd.1 (h ▸ hx)
      simp [this]

theorem card_foldl {α V : Type*} [DecidableEq V] (g : Finset V → α → Finset V)
    (hg : ∀ u a, (g u a).card ≤ u.card + 1) :
    ∀ (L : List α) (s : Finset V), (L.foldl g s).card ≤ s.card + L.length := by
  intro L
  induction L with
  | nil => intro s; simp
  | cons a L ih =>
    intro s
    simp only [List.foldl_cons, List.length_cons]
    have := ih (g s a)
    have := hg s a
    omega

end PEqualNP.Outside.L_lib_657_aux

open PEqualNP.Outside.L_lib_657_aux in
theorem PEqualNP.Outside.L_lib_657 : ∀ (n b r : Nat), 0 < b →
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  ∀ (clauses : List Clause) (center : Point),
    let F := clauses.toFinset
    let bad := fun (x : Point) (c : Clause) => ∀ lit ∈ c, x lit.1 ≠ lit.2
    let vars := fun (c : Clause) => c.image Prod.fst
    let state := fun (flipped : Finset V) (v : V) =>
      if v ∈ flipped then !(center v) else center v
    let run := fun (choices : Fin r → Fin b) =>
      (List.finRange r).foldl (fun used step =>
        let c := (clauses.find? (fun d => decide (bad (state used) d))).getD ∅
        let options := ((vars c) \ used).sort (· ≤ ·)
        let picked := options[ (choices step).val ]?
        used ∪ picked.toList.toFinset) (∅ : Finset V)
    (∀ c ∈ F, (vars c).card ≤ b+1) →
    (∀ c ∈ F, bad center c → (vars c).card ≤ b) →
    ((∃ y : Point, sat F y ∧ ((Finset.univ : Finset V).filter (fun i => y i ≠ center i)).card ≤ r) ↔
      (∃ choices : Fin r → Fin b, sat F (state (run choices)))) := by
  intro n b r hb V Point Clause sat clauses center F bad vars state run hw hbad
  have hfilt : ∀ U : Finset V,
      (Finset.univ : Finset V).filter (fun i => state U i ≠ center i) = U := by
    intro U
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, state]
    by_cases h : i ∈ U <;> simp [h]
  constructor
  · rintro ⟨y, hy, hd⟩
    set D := (Finset.univ : Finset V).filter (fun i => y i ≠ center i) with hD
    have hstate : state D = y := by
      funext v
      simp only [state, hD, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : y v = center v
      · simp [h]
      · cases hy' : y v <;> cases hc : center v <;> simp_all
    let g : Finset V → Fin b → Finset V := fun (used : Finset V) (k : Fin b) =>
        let c := (clauses.find? (fun d => decide (bad (state used) d))).getD ∅
        let options := ((vars c) \ used).sort (· ≤ ·)
        let picked := options[ k.val ]?
        used ∪ picked.toList.toFinset
    let Inv : Finset V → ℕ → Prop :=
      fun used m => used ⊆ D ∧ (sat F (state used) ∨ D.card ≤ used.card + m)
    have hstep : ∀ used m, Inv used (m+1) → ∃ k, Inv (g used k) m := by
      rintro used m ⟨hsub, hor⟩
      by_cases hs : sat F (state used)
      · refine ⟨⟨0, hb⟩, ?_⟩
        have hfind : clauses.find? (fun d => decide (bad (state used) d)) = none := by
          rw [List.find?_eq_none]
          intro d hd
          obtain ⟨lit, hl, he⟩ := hs d (List.mem_toFinset.2 hd)
          simp only [decide_eq_true_eq, bad, not_forall, not_not]
          exact ⟨lit, hl, he⟩
        have heq : g used ⟨0, hb⟩ = used := by
          ext x
          have hv : Finset.image (Prod.fst : V × Bool → V) (∅ : Finset (V × Bool)) = ∅ :=
            Finset.image_empty _
          simp only [g, hfind, Option.getD_none, vars]
          erw [hv]
          simp
        rw [heq]
        exact ⟨hsub, Or.inl hs⟩
      · have hex : ∃ c ∈ clauses, bad (state used) c := by
          simp only [sat, not_forall, not_exists, not_and] at hs
          obtain ⟨c, hc, h⟩ := hs
          exact ⟨c, List.mem_toFinset.1 hc, fun lit hl => h lit hl⟩
        obtain ⟨c0, hc0⟩ : ∃ c0, clauses.find? (fun d => decide (bad (state used) d)) = some c0 := by
          rw [← Option.isSome_iff_exists, List.find?_isSome]
          obtain ⟨c, hc, h⟩ := hex
          exact ⟨c, hc, by simpa using h⟩
        have hc0mem : c0 ∈ clauses := List.mem_of_find?_eq_some hc0
        have hc0bad : bad (state used) c0 := by simpa using List.find?_some hc0
        have hc0F : c0 ∈ F := List.mem_toFinset.2 hc0mem
        obtain ⟨lit, hl, hyl⟩ := hy c0 hc0F
        have hsl := hc0bad lit hl
        have hvnu : lit.1 ∉ used := by
          intro hu
          have hdv := hsub hu
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hdv
          simp only [state, hu, if_true] at hsl
          apply hsl
          rw [← hyl]
          cases hy' : y lit.1 <;> cases hc : center lit.1 <;> simp_all
        have hvD : lit.1 ∈ D := by
          simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
          intro h
          simp only [state, hvnu, if_false] at hsl
          exact hsl (h ▸ hyl)
        have hvopt : lit.1 ∈ vars c0 \ used :=
          Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨lit, hl, rfl⟩, hvnu⟩
        have hcard : (vars c0 \ used).card ≤ b := by
          by_cases hbc : bad center c0
          · exact (Finset.card_le_card Finset.sdiff_subset).trans (hbad c0 hc0F hbc)
          · simp only [bad, not_forall, not_not] at hbc
            obtain ⟨l2, hl2, he2⟩ := hbc
            have hu2 : l2.1 ∈ used := by
              by_contra hn
              exact hc0bad l2 hl2 (by simp only [state, hn, if_false]; exact he2)
            have : (vars c0 \ used).card < (vars c0).card := by
              apply Finset.card_lt_card
              refine ⟨Finset.sdiff_subset, fun h => ?_⟩
              exact (Finset.mem_sdiff.1 (h (Finset.mem_image.2 ⟨l2, hl2, rfl⟩))).2 hu2
            have := hw c0 hc0F
            omega
        set opts := (vars c0 \ used).sort (· ≤ ·) with hopts
        have hmem : lit.1 ∈ opts := by rw [hopts, Finset.mem_sort]; exact hvopt
        have hidx : opts.idxOf lit.1 < opts.length := List.idxOf_lt_length_of_mem hmem
        have hlen : opts.length = (vars c0 \ used).card := by rw [hopts, Finset.length_sort]
        refine ⟨⟨opts.idxOf lit.1, by omega⟩, ?_⟩
        have hget : opts[opts.idxOf lit.1]? = some lit.1 := by
          rw [List.getElem?_eq_getElem hidx, List.getElem_idxOf]
        have heq : g used ⟨opts.idxOf lit.1, by omega⟩ = insert lit.1 used := by
          ext x
          simp only [g, hc0, Option.getD_some, ← hopts, hget, Option.toList_some,
            Finset.mem_union, List.mem_toFinset, List.mem_singleton, Finset.mem_insert]
          tauto
        rw [heq]
        refine ⟨Finset.insert_subset hvD hsub, Or.inr ?_⟩
        rcases hor with h | h
        · exact absurd h hs
        · rw [Finset.card_insert_of_notMem hvnu]
          omega
    obtain ⟨ch, hch⟩ := exists_choices (⟨0, hb⟩ : Fin b) g Inv hstep
      (List.finRange r) (List.nodup_finRange r) ∅
      ⟨Finset.empty_subset _, Or.inr (by simpa using hd)⟩
    refine ⟨ch, ?_⟩
    rcases hch with ⟨hsub, hs | hc⟩
    · exact hs
    · have := Finset.eq_of_subset_of_card_le hsub (by simpa using hc)
      change sat F (state (List.foldl (fun u a => g u (ch a)) ∅ (List.finRange r)))
      rw [this, hstate]
      exact hy
  · rintro ⟨ch, hs⟩
    refine ⟨state (run ch), hs, ?_⟩
    rw [hfilt]
    have := card_foldl (fun (used : Finset V) (step : Fin r) =>
        let c := (clauses.find? (fun d => decide (bad (state used) d))).getD ∅
        let options := ((vars c) \ used).sort (· ≤ ·)
        let picked := options[ (ch step).val ]?
        used ∪ picked.toList.toFinset) ?_ (List.finRange r) ∅
    · simpa using this
    · intro u a
      refine (Finset.card_union_le _ _).trans ?_
      apply Nat.add_le_add_left
      cases (((vars ((clauses.find? (fun d => decide (bad (state u) d))).getD ∅)) \ u).sort
        (· ≤ ·))[(ch a).val]? <;> simp

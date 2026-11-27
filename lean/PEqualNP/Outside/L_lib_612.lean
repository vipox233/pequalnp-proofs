import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PEqualNP.Outside.L_lib_612

section Poly
variable {α : Type} [DecidableEq α]

def Rep (F : Finset (Finset α)) (w : α → Bool) : Bool :=
  ((F.filter (fun mon => ∀ v ∈ mon, w v = true)).card % 2) == 1

theorem rep_eq_true (F : Finset (Finset α)) (w : α → Bool) :
    Rep F w = true ↔ (F.filter (fun mon => ∀ v ∈ mon, w v = true)).card % 2 = 1 := by
  simp [Rep]

theorem sum_mod_two {β : Type} [DecidableEq β] (X : Finset β) (c : β → ℕ) :
    (∑ U ∈ X, c U) % 2 = (X.filter (fun U => c U % 2 = 1)).card % 2 := by
  induction X using Finset.induction_on with
  | empty => simp
  | insert a X ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [ha])]
      omega
    · omega

theorem rep_empty (w : α → Bool) : Rep (∅ : Finset (Finset α)) w = false := by
  simp [Rep]

theorem rep_single (T : Finset α) (w : α → Bool) :
    Rep {T} w = decide (∀ v ∈ T, w v = true) := by
  unfold Rep
  rw [Finset.filter_singleton]
  split_ifs with h <;> simp_all

theorem rep_xor (F G : Finset (Finset α)) (w : α → Bool) :
    Rep (symmDiff F G) w = xor (Rep F w) (Rep G w) := by
  set P : Finset α → Prop := fun mon => ∀ v ∈ mon, w v = true
  have h1 : (symmDiff F G).filter P = symmDiff (F.filter P) (G.filter P) := by
    ext x; simp [Finset.mem_symmDiff]; tauto
  have h2 : ∀ A B : Finset (Finset α), (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
    intro A B
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have e1 := Finset.card_sdiff_add_card_inter A B
    have e2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at e2
    omega
  have h3 := h2 (F.filter P) (G.filter P)
  unfold Rep
  rw [h1]
  simp only [P] at h3 ⊢
  rcases Nat.mod_two_eq_zero_or_one (F.filter (fun mon => ∀ v ∈ mon, w v = true)).card with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one (G.filter (fun mon => ∀ v ∈ mon, w v = true)).card with b | b <;>
    simp only [a, b] <;> simp <;> omega

def mulT (F G : Finset (Finset α)) : Finset (Finset α) :=
  ((F ×ˢ G).image (fun p => p.1 ∪ p.2)).filter
    (fun U => ((F ×ˢ G).filter (fun p => p.1 ∪ p.2 = U)).card % 2 = 1)

theorem rep_mul (F G : Finset (Finset α)) (w : α → Bool) :
    Rep (mulT F G) w = (Rep F w && Rep G w) := by
  set P : Finset α → Prop := fun mon => ∀ v ∈ mon, w v = true
  have hPu : ∀ S T : Finset α, P (S ∪ T) ↔ P S ∧ P T := by
    intro S T; simp only [P, Finset.mem_union]; constructor
    · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
    · rintro ⟨h1, h2⟩ v (hv | hv); exacts [h1 v hv, h2 v hv]
  set X := ((F ×ˢ G).image (fun p => p.1 ∪ p.2)).filter P
  set c : Finset α → ℕ := fun U => ((F ×ˢ G).filter (fun p => p.1 ∪ p.2 = U)).card
  have hm : (mulT F G).filter P = X.filter (fun U => c U % 2 = 1) := by
    ext U; simp only [mulT, X, c, Finset.mem_filter]; tauto
  have hsum : ∑ U ∈ X, c U = ((F ×ˢ G).filter (fun p => P (p.1 ∪ p.2))).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Finset α × Finset α => p.1 ∪ p.2)
      (t := X)]
    · apply Finset.sum_congr rfl
      intro U hU
      have hPU : P U := (Finset.mem_filter.1 hU).2
      simp only [c]
      congr 1
      ext p; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, he⟩; exact ⟨⟨hp, he ▸ hPU⟩, he⟩
      · rintro ⟨⟨hp, _⟩, he⟩; exact ⟨hp, he⟩
    · intro p hp
      rw [Finset.mem_coe] at hp ⊢
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_image.2 ⟨p, hp.1, rfl⟩, hp.2⟩
  have hprod : ((F ×ˢ G).filter (fun p => P (p.1 ∪ p.2))).card
      = (F.filter P).card * (G.filter P).card := by
    rw [← Finset.card_product]
    congr 1
    ext p; simp only [Finset.mem_filter, Finset.mem_product, hPu]; tauto
  have key : ((mulT F G).filter P).card % 2 = ((F.filter P).card * (G.filter P).card) % 2 := by
    rw [hm, ← sum_mod_two, hsum, hprod]
  unfold Rep
  rw [key, Nat.mul_mod]
  have a := Nat.mod_two_eq_zero_or_one (F.filter P).card
  have b := Nat.mod_two_eq_zero_or_one (G.filter P).card
  simp only [P] at a b ⊢
  rcases a with a | a <;> rcases b with b | b <;> simp [a, b]

theorem mulT_card (F G : Finset (Finset α)) (a b : ℕ) (hF : ∀ T ∈ F, T.card ≤ a)
    (hG : ∀ T ∈ G, T.card ≤ b) : ∀ U ∈ mulT F G, U.card ≤ a + b := by
  intro U hU
  simp only [mulT, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at hU
  obtain ⟨⟨p, ⟨h1, h2⟩, rfl⟩, -⟩ := hU
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hF _ h1) (hG _ h2))

def dT (v : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  (F.filter (fun T => v ∈ T)).image (fun T => T.erase v)

theorem rep_dT (v : α) (F : Finset (Finset α)) (w : α → Bool) :
    Rep (dT v F) w = xor (Rep F (Function.update w v true)) (Rep F (Function.update w v false)) := by
  set P : (α → Bool) → Finset α → Prop := fun x mon => ∀ u ∈ mon, x u = true
  set A := F.filter (fun T => v ∉ T)
  set B := F.filter (fun T => v ∈ T)
  have hsplit : ∀ Q : Finset α → Prop, [DecidablePred Q] →
      (F.filter Q).card = (A.filter Q).card + (B.filter Q).card := by
    intro Q _
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext T; simp only [A, B, Finset.mem_filter, Finset.mem_union]; tauto
    · rw [Finset.disjoint_left]; intro T h1 h2
      simp only [A, B, Finset.mem_filter] at h1 h2; exact h1.1.2 h2.1.2
  have hA1 : A.filter (P (Function.update w v true)) = A.filter (P w) := by
    apply Finset.filter_congr; intro T hT
    have hv : v ∉ T := (Finset.mem_filter.1 hT).2
    simp only [P]; constructor
    · intro h u hu; have := h u hu; rwa [Function.update_of_ne (by rintro rfl; exact hv hu)] at this
    · intro h u hu; rw [Function.update_of_ne (by rintro rfl; exact hv hu)]; exact h u hu
  have hA0 : A.filter (P (Function.update w v false)) = A.filter (P w) := by
    apply Finset.filter_congr; intro T hT
    have hv : v ∉ T := (Finset.mem_filter.1 hT).2
    simp only [P]; constructor
    · intro h u hu; have := h u hu; rwa [Function.update_of_ne (by rintro rfl; exact hv hu)] at this
    · intro h u hu; rw [Function.update_of_ne (by rintro rfl; exact hv hu)]; exact h u hu
  have hB0 : B.filter (P (Function.update w v false)) = ∅ := by
    apply Finset.filter_false_of_mem; intro T hT h
    have := h v (Finset.mem_filter.1 hT).2
    simp at this
  have hB1 : (B.filter (P (Function.update w v true))).card = ((dT v F).filter (P w)).card := by
    have hinj : Set.InjOn (fun T : Finset α => T.erase v) (B.filter (P (Function.update w v true))) := by
      intro S hS T hT h
      have hS' : v ∈ S := (Finset.mem_filter.1 (Finset.mem_filter.1 hS).1).2
      have hT' : v ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hT).1).2
      simp only at h
      rw [← Finset.insert_erase hS', ← Finset.insert_erase hT', h]
    rw [← Finset.card_image_of_injOn hinj]
    congr 1
    ext U
    simp only [dT, Finset.mem_image, Finset.mem_filter, B, P]
    constructor
    · rintro ⟨T, ⟨⟨hTF, hvT⟩, hP⟩, rfl⟩
      refine ⟨⟨T, ⟨hTF, hvT⟩, rfl⟩, fun u hu => ?_⟩
      have hne : u ≠ v := Finset.ne_of_mem_erase hu
      have := hP u (Finset.mem_of_mem_erase hu)
      rwa [Function.update_of_ne hne] at this
    · rintro ⟨⟨T, ⟨hTF, hvT⟩, rfl⟩, hP⟩
      refine ⟨T, ⟨⟨hTF, hvT⟩, fun u hu => ?_⟩, rfl⟩
      by_cases hne : u = v
      · subst hne; simp
      · rw [Function.update_of_ne hne]; exact hP u (Finset.mem_erase.2 ⟨hne, hu⟩)
  have e1 := hsplit (P (Function.update w v true))
  have e0 := hsplit (P (Function.update w v false))
  rw [hA1, hB1] at e1
  rw [hA0, hB0, Finset.card_empty, add_zero] at e0
  unfold Rep
  simp only [P] at e1 e0
  rw [e1, e0]
  set a := (A.filter (fun mon => ∀ u ∈ mon, w u = true)).card
  set b := ((dT v F).filter (fun mon => ∀ u ∈ mon, w u = true)).card
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [ha, hb, Nat.add_mod]

end Poly

section Deriv
variable {α : Type} [DecidableEq α]

def Dfun : List α → ((α → Bool) → Bool) → (α → Bool) → Bool
  | [], f => f
  | v :: l, f => Dfun l (fun w => xor (f (Function.update w v true)) (f (Function.update w v false)))

def DT : List α → Finset (Finset α) → Finset (Finset α)
  | [], F => F
  | v :: l, F => DT l (dT v F)

theorem rep_DT : ∀ (l : List α) (F : Finset (Finset α)), Rep (DT l F) = Dfun l (Rep F)
  | [], _ => rfl
  | v :: l, F => by
    simp only [DT, Dfun]
    rw [rep_DT l (dT v F)]
    congr 1
    funext w
    exact rep_dT v F w

theorem Dfun_true : ∀ (l : List α) (f : (α → Bool) → Bool) (z : α → Bool), Dfun l f z = true →
    ∃ w, (∀ u, u ∉ l → w u = z u) ∧ f w = true
  | [], _, z, h => ⟨z, fun _ _ => rfl, h⟩
  | v :: l, f, z, h => by
    obtain ⟨w, hw, hf⟩ := Dfun_true l _ z h
    have hoff : ∀ c u, u ∉ v :: l → Function.update w v c u = z u := by
      intro c u hu
      have hne : u ≠ v := by rintro rfl; simp at hu
      rw [Function.update_of_ne hne]
      exact hw u (fun hm => hu (List.mem_cons_of_mem _ hm))
    by_cases h1 : f (Function.update w v true) = true
    · exact ⟨_, hoff true, h1⟩
    · have h0 : f (Function.update w v false) = true := by
        simp only [Bool.not_eq_true] at h1
        rw [h1] at hf
        simpa using hf
      exact ⟨_, hoff false, h0⟩

theorem Dfun_xor : ∀ (l : List α) (f g : (α → Bool) → Bool) (z : α → Bool),
    Dfun l (fun w => xor (f w) (g w)) z = xor (Dfun l f z) (Dfun l g z)
  | [], _, _, _ => rfl
  | v :: l, f, g, z => by
    simp only [Dfun]
    rw [← Dfun_xor l]
    congr 1
    funext w
    cases f (Function.update w v true) <;> cases f (Function.update w v false) <;>
      cases g (Function.update w v true) <;> cases g (Function.update w v false) <;> rfl

theorem mem_DT : ∀ (l : List α), l.Nodup → ∀ (F : Finset (Finset α)) (U : Finset α),
    U ∈ DT l F ↔ ∃ T ∈ F, (∀ v ∈ l, v ∈ T) ∧ U = T \ l.toFinset
  | [], _, F, U => by simp [DT]
  | v :: l, hl, F, U => by
    have hv : v ∉ l := (List.nodup_cons.1 hl).1
    have hl' := (List.nodup_cons.1 hl).2
    simp only [DT]
    rw [mem_DT l hl' (dT v F) U]
    constructor
    · rintro ⟨T', hT', hl2, rfl⟩
      simp only [dT, Finset.mem_image, Finset.mem_filter] at hT'
      obtain ⟨T, ⟨hTF, hvT⟩, rfl⟩ := hT'
      refine ⟨T, hTF, ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hvT
        · exact Finset.mem_of_mem_erase (hl2 u hu)
      · ext x; simp [List.toFinset_cons]; tauto
    · rintro ⟨T, hTF, hall, rfl⟩
      refine ⟨T.erase v, ?_, ?_, ?_⟩
      · simp only [dT, Finset.mem_image, Finset.mem_filter]
        exact ⟨T, ⟨hTF, hall v (List.mem_cons_self ..)⟩, rfl⟩
      · intro u hu
        exact Finset.mem_erase.2 ⟨fun e => hv (e ▸ hu), hall u (List.mem_cons_of_mem _ hu)⟩
      · ext x; simp [List.toFinset_cons]; tauto

theorem DT_max (F : Finset (Finset α)) (M : Finset α) (hM : M ∈ F)
    (hmax : ∀ T ∈ F, T.card ≤ M.card) : DT M.toList F = {∅} := by
  ext U
  rw [mem_DT _ (Finset.nodup_toList M), Finset.mem_singleton]
  simp only [Finset.mem_toList, Finset.toList_toFinset]
  constructor
  · rintro ⟨T, hT, hMT, rfl⟩
    have : M = T := Finset.eq_of_subset_of_card_le (fun v hv => hMT v hv) (hmax T hT)
    subst this
    simp
  · rintro rfl
    exact ⟨M, hM, fun v hv => hv, by simp⟩

theorem extend_max (F : Finset (Finset α)) (M : Finset α) (hM : M ∈ F)
    (hmax : ∀ T ∈ F, T.card ≤ M.card) (z : α → Bool) :
    ∃ w, (∀ u, u ∉ M → w u = z u) ∧ Rep F w = true := by
  have h : Dfun M.toList (Rep F) z = true := by
    rw [← rep_DT, DT_max F M hM hmax, rep_single]
    simp
  obtain ⟨w, hw, hf⟩ := Dfun_true _ _ z h
  exact ⟨w, fun u hu => hw u (by simpa using hu), hf⟩

variable [Fintype α]

theorem Dfun_univ_rep (F : Finset (Finset α)) (z : α → Bool) :
    Dfun (Finset.univ : Finset α).toList (Rep F) z = decide (Finset.univ ∈ F) := by
  rw [← rep_DT]
  by_cases h : (Finset.univ : Finset α) ∈ F
  · have : DT (Finset.univ : Finset α).toList F = {∅} := by
      apply DT_max F _ h
      intro T _
      exact Finset.card_le_univ T
    rw [this, rep_single]
    simp [h]
  · have : DT (Finset.univ : Finset α).toList F = ∅ := by
      ext U
      rw [mem_DT _ (Finset.nodup_toList _)]
      simp only [Finset.mem_toList, Finset.notMem_empty, iff_false]
      rintro ⟨T, hT, hall, -⟩
      have : T = Finset.univ := Finset.eq_univ_of_forall (fun v => hall v (Finset.mem_univ v))
      exact h (this ▸ hT)
    rw [this, rep_empty]
    simp [h]

theorem card_lt_of_dfun (F : Finset (Finset α)) (z : α → Bool)
    (hz : Dfun (Finset.univ : Finset α).toList (Rep F) z = false) :
    ∀ T ∈ F, T.card < Fintype.card α := by
  rw [Dfun_univ_rep] at hz
  intro T hT
  have hne : T ≠ Finset.univ := by
    rintro rfl
    simp [hT] at hz
  rw [← Finset.card_univ]
  exact Finset.card_lt_card (Finset.ssubset_univ_iff.2 hne)

theorem and_eq_rep (z : α → Bool) :
    decide (∀ v, z v = true) = Rep {(Finset.univ : Finset α)} z := by
  rw [rep_single]
  simp

theorem miss (F : Finset (Finset α)) (hF : ∀ T ∈ F, T.card < Fintype.card α) :
    ∃ z, Rep F z ≠ decide (∀ v, z v = true) := by
  by_contra h
  push_neg at h
  have e : Rep F = Rep {(Finset.univ : Finset α)} := by
    funext z
    rw [h z, and_eq_rep]
  have h1 := Dfun_univ_rep F (fun _ => true)
  have h2 := Dfun_univ_rep {(Finset.univ : Finset α)} (fun _ => true)
  rw [e] at h1
  rw [h1] at h2
  have hu : (Finset.univ : Finset α) ∉ F := by
    intro hu
    have := hF _ hu
    rw [Finset.card_univ] at this
    exact lt_irrefl _ this
  simp [hu] at h2

def agree (S : List α) (b : α → Bool) (w : α → Bool) : Bool := decide (∀ u, u ∉ S → w u = b u)

theorem agree_step (S : List α) (b : α → Bool) (v : α) (hv : v ∉ S) (w : α → Bool) :
    xor (agree S b (Function.update w v true)) (agree S b (Function.update w v false))
      = agree (v :: S) b w := by
  have key : ∀ c, agree S b (Function.update w v c) = (decide (c = b v) && agree (v :: S) b w) := by
    intro c
    unfold agree
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, not_or]
    constructor
    · intro h
      refine ⟨?_, fun u hu => ?_⟩
      · have := h v hv
        simpa using this
      · have := h u hu.2
        rwa [Function.update_of_ne hu.1] at this
    · rintro ⟨hc, h⟩ u hu
      by_cases e : u = v
      · subst e
        simpa using hc
      · rw [Function.update_of_ne e]
        exact h u ⟨e, hu⟩
  rw [key, key]
  cases hb : b v <;> simp

theorem Dfun_agree : ∀ (l S : List α) (b : α → Bool), (∀ v ∈ l, v ∉ S) → l.Nodup →
    ∀ z, Dfun l (agree S b) z = agree (l ++ S) b z
  | [], _, _, _, _, _ => rfl
  | v :: l, S, b, hd, hl, z => by
    simp only [Dfun]
    have hvS : v ∉ S := hd v (List.mem_cons_self ..)
    have hfun : (fun w => xor (agree S b (Function.update w v true))
        (agree S b (Function.update w v false))) = agree (v :: S) b := by
      funext w
      exact agree_step S b v hvS w
    rw [hfun]
    have hd' : ∀ u ∈ l, u ∉ v :: S := by
      intro u hu hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact (List.nodup_cons.1 hl).1 hu
      · exact hd u (List.mem_cons_of_mem _ hu) hm
    rw [Dfun_agree l (v :: S) b hd' (List.nodup_cons.1 hl).2 z]
    unfold agree
    simp only [List.mem_append, List.mem_cons]
    congr 1
    apply propext
    constructor
    · intro h u hu
      exact h u (by tauto)
    · intro h u hu
      exact h u (by tauto)

def litT (v : α) (c : Bool) : Finset (Finset α) :=
  if c then {{v}} else symmDiff {∅} {{v}}

theorem rep_lit (v : α) (c : Bool) (w : α → Bool) : Rep (litT v c) w = decide (w v = c) := by
  unfold litT
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rep_xor, rep_single, rep_single]
    cases h : w v <;> simp [h]
  · simp only [↓reduceIte]
    rw [rep_single]
    simp

def ptT (b : α → Bool) : List α → Finset (Finset α)
  | [] => {∅}
  | v :: l => mulT (litT v (b v)) (ptT b l)

theorem rep_pt (b : α → Bool) : ∀ (l : List α) (w : α → Bool),
    Rep (ptT b l) w = decide (∀ v ∈ l, w v = b v)
  | [], w => by rw [ptT, rep_single]; simp
  | v :: l, w => by
    rw [ptT, rep_mul, rep_lit, rep_pt b l w]
    simp [List.mem_cons]

theorem low_flip (b : α → Bool) : ∃ F : Finset (Finset α), (∀ T ∈ F, T.card < Fintype.card α) ∧
    ∀ z, xor (decide (∀ v, z v = true)) (decide (z = b)) = Rep F z := by
  set F := symmDiff {(Finset.univ : Finset α)} (ptT b (Finset.univ : Finset α).toList)
  have hrep : ∀ z, xor (decide (∀ v, z v = true)) (decide (z = b)) = Rep F z := by
    intro z
    rw [rep_xor, rep_pt, and_eq_rep]
    congr 1
    simp only [Finset.mem_toList, Finset.mem_univ, true_implies]
    exact decide_eq_decide.2 ⟨fun h v => congrFun h v, fun h => funext h⟩
  refine ⟨F, ?_, hrep⟩
  apply card_lt_of_dfun F (fun _ => true)
  have e : Rep F = fun z => xor (agree [] (fun _ => true) z) (agree [] b z) := by
    funext z
    rw [← hrep z]
    unfold agree
    simp only [List.not_mem_nil, not_false_eq_true, true_implies]
    congr 1
    all_goals exact decide_eq_decide.2 ⟨fun h v => congrFun h v, fun h => funext h⟩
  rw [e, Dfun_xor, Dfun_agree _ _ _ (by simp) (Finset.nodup_toList _),
    Dfun_agree _ _ _ (by simp) (Finset.nodup_toList _)]
  unfold agree
  simp

end Deriv

section Protocol
variable {X : Type}

def run (ask : ℕ → ℕ → X → Bool) (len : ℕ) (x : X) : ℕ :=
  (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0

theorem run_succ (ask : ℕ → ℕ → X → Bool) (t : ℕ) (x : X) :
    run ask (t + 1) x = run ask t x + (ask t (run ask t x) x).toNat * 2 ^ t := by
  unfold run
  rw [List.range_succ, List.foldl_append]
  simp [Nat.shiftLeft_eq]

theorem run_lt (ask : ℕ → ℕ → X → Bool) : ∀ (t : ℕ) (x : X), run ask t x < 2 ^ t
  | 0, x => by simp [run]
  | t + 1, x => by
    rw [run_succ, pow_succ]
    have := run_lt ask t x
    cases ask t (run ask t x) x <;> simp <;> omega

theorem run_add (ask : ℕ → ℕ → X → Bool) (t : ℕ) (x : X) : ∀ k : ℕ,
    ∃ q, q < 2 ^ k ∧ run ask (t + k) x = run ask t x + 2 ^ t * q
  | 0 => ⟨0, by simp, by simp⟩
  | k + 1 => by
    obtain ⟨q, hq, h⟩ := run_add ask t x k
    refine ⟨q + (ask (t + k) (run ask (t + k) x) x).toNat * 2 ^ k, ?_, ?_⟩
    · rw [pow_succ]
      cases ask (t + k) (run ask (t + k) x) x <;> simp <;> omega
    · rw [show t + (k + 1) = (t + k) + 1 by omega, run_succ, h, pow_add]
      ring

theorem div_mod_split (a b c : ℕ) (ha : a < 2 ^ c) : (a + 2 ^ c * b) / 2 ^ c = b := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]

theorem run_succ_eq (ask : ℕ → ℕ → X → Bool) (t : ℕ) (x y : X) :
    run ask (t + 1) x = run ask (t + 1) y ↔
      run ask t x = run ask t y ∧ ask t (run ask t x) x = ask t (run ask t y) y := by
  rw [run_succ, run_succ]
  have hx := run_lt ask t x
  have hy := run_lt ask t y
  constructor
  · intro h
    have h1 := congrArg (· % 2 ^ t) h
    have h2 := congrArg (· / 2 ^ t) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
    rw [mul_comm _ (2 ^ t), mul_comm _ (2 ^ t)] at h2
    rw [div_mod_split _ _ _ hx, div_mod_split _ _ _ hy] at h2
    refine ⟨h1, ?_⟩
    rw [h1] at h2 ⊢
    cases hb1 : ask t (run ask t y) x <;> cases hb2 : ask t (run ask t y) y <;> simp_all
  · rintro ⟨h1, h2⟩
    rw [h1] at h2 ⊢
    rw [h2]

theorem testBit_run (ask : ℕ → ℕ → X → Bool) (x : X) (t len : ℕ) (ht : t < len) :
    (run ask len x).testBit t = ask t (run ask t x) x := by
  obtain ⟨q, hq, h⟩ := run_add ask (t + 1) x (len - (t + 1))
  rw [show t + 1 + (len - (t + 1)) = len by omega] at h
  rw [h, run_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hl := run_lt ask t x
  have e : run ask t x + (ask t (run ask t x) x).toNat * 2 ^ t + 2 ^ (t + 1) * q
      = run ask t x + 2 ^ t * ((ask t (run ask t x) x).toNat + 2 * q) := by
    rw [pow_succ]; ring
  rw [e, div_mod_split _ _ _ hl]
  cases ask t (run ask t x) x <;> simp [Nat.add_mod]

end Protocol

section Reach
variable {α : Type} [DecidableEq α]

theorem reach (ask : ℕ → ℕ → (α → Bool) → Bool) (cost : ℕ → ℕ → ℕ) (n : ℕ) (w0 : α → Bool)
    (hdeg : ∀ t < n, ∃ G : Finset (Finset α), (∀ T ∈ G, T.card ≤ cost t (run ask t w0)) ∧
      ∀ w, ask t (run ask t w0) w = Rep G w) :
    ∀ t ≤ n, ∃ F : Finset (Finset α),
      (∀ T ∈ F, T.card ≤ ∑ u ∈ Finset.range t, cost u (run ask u w0)) ∧
      ∀ w, Rep F w = decide (run ask t w = run ask t w0) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨{∅}, by simp, fun w => ?_⟩
    rw [rep_single]
    simp [run]
  | succ t ih =>
    intro ht
    obtain ⟨F, hF, hFr⟩ := ih (by omega)
    obtain ⟨G, hG, hGr⟩ := hdeg t (by omega)
    set c := ask t (run ask t w0) w0
    let G' : Finset (Finset α) := if c then G else symmDiff {∅} G
    have hG' : ∀ w, Rep G' w = decide (ask t (run ask t w0) w = c) := by
      intro w
      simp only [G']
      cases hc : c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [rep_xor, rep_single, ← hGr w]
        cases ask t (run ask t w0) w <;> simp
      · simp only [↓reduceIte]
        rw [← hGr w]
        cases ask t (run ask t w0) w <;> simp
    have hG'c : ∀ T ∈ G', T.card ≤ cost t (run ask t w0) := by
      intro T hT
      simp only [G'] at hT
      split_ifs at hT
      · exact hG T hT
      · rcases Finset.mem_symmDiff.1 hT with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [Finset.mem_singleton.1 h1]; simp
        · exact hG T h1
    refine ⟨mulT F G', ?_, fun w => ?_⟩
    · rw [Finset.sum_range_succ]
      exact mulT_card F G' _ _ hF hG'c
    · rw [rep_mul, hFr, hG', Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [run_succ_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h1]; exact h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h1] at h2; exact h2⟩

end Reach

theorem lower (m r D s L : ℕ) (n : ℕ) (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool)
    (cost : ℕ → ℕ → ℕ) (leaf : ℕ → Fin L → Fin m → (Fin r → Bool) → Bool)
    (hleaf : ∀ h a i, ∃ F : Finset (Finset (Fin r)), (∀ T ∈ F, T.card < r) ∧
      ∀ z, leaf h a i z = Rep F z)
    (hdeg : ∀ (input : Fin m × Fin r → Bool) (u : Fin n), ∃ G : Finset (Finset (Fin m × Fin r)),
      (∀ T ∈ G, T.card ≤ cost u.val (run ask u.val input)) ∧
      ∀ w, ask u.val (run ask u.val input) w = Rep G w)
    (hcost : ∀ w : Fin m × Fin r → Bool, (∑ t : Fin n, cost t.val (run ask t.val w)) ≤ D)
    (hcorr : ∀ w : Fin m × Fin r → Bool, ∃ a, ∀ i, leaf (run ask (n + s) w) a i (fun v => w (i, v))
      = decide (∀ v : Fin r, w (i, v) = true)) :
    ∃ bad : Fin (2 ^ s * L) → Fin (m - D) → (Fin r → Bool),
      ∀ x : Fin (m - D) → (Fin r → Bool), ∃ a, ∀ i, x i ≠ bad a i := by
  classical
  set w0 : Fin m × Fin r → Bool := fun _ => false
  obtain ⟨F, hFc, hFr⟩ := reach ask cost n w0 (fun t ht => hdeg w0 ⟨t, ht⟩) n le_rfl
  have hsum : ∑ u ∈ Finset.range n, cost u (run ask u w0) ≤ D := by
    have := hcost w0
    rwa [Fin.sum_univ_eq_sum_range (fun t => cost t (run ask t w0))] at this
  have hF0 : Rep F w0 = true := by rw [hFr]; simp
  have hFne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [rep_empty] at hF0
    exact Bool.false_ne_true hF0
  obtain ⟨M, hM, hmax⟩ := F.exists_max_image Finset.card hFne
  have hMD : M.card ≤ D := (hFc M hM).trans hsum
  set touched : Finset (Fin m) := M.image Prod.fst
  have htc : touched.card ≤ D := Finset.card_image_le.trans hMD
  have hfree : m - D ≤ (Finset.univ \ touched).card := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
    omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hfree
  let e : Fin (m - D) ↪o Fin m := t.orderEmbOfFin htcard
  have he_free : ∀ i, e i ∉ touched := fun i h =>
    (Finset.mem_sdiff.1 (hts (Finset.orderEmbOfFin_mem t htcard i))).2 h
  set hn := run ask n w0
  have hmiss : ∀ (g : Fin (2 ^ s)) (a : Fin L) (i : Fin (m - D)),
      ∃ z, leaf (hn + 2 ^ n * g.val) a (e i) z ≠ decide (∀ v, z v = true) := by
    intro g a i
    obtain ⟨G, hG, hGr⟩ := hleaf (hn + 2 ^ n * g.val) a (e i)
    obtain ⟨z, hz⟩ := miss G (by simpa using hG)
    exact ⟨z, by rw [hGr]; convert hz⟩
  let badGA : Fin (2 ^ s) → Fin L → Fin (m - D) → (Fin r → Bool) :=
    fun g a i => Classical.choose (hmiss g a i)
  refine ⟨fun idx i => badGA (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2 i, ?_⟩
  intro x
  let z : Fin m × Fin r → Bool := fun p =>
    if h : ∃ i, e i = p.1 then x (Classical.choose h) p.2 else false
  have hz : ∀ i v, z (e i, v) = x i v := by
    intro i v
    have h : ∃ j, e j = e i := ⟨i, rfl⟩
    simp only [z, dif_pos h]
    rw [e.injective (Classical.choose_spec h)]
  obtain ⟨w, hw, hwF⟩ := extend_max F M hM hmax z
  have hwn : run ask n w = hn := by
    have := hFr w
    rw [hwF] at this
    exact of_decide_eq_true this.symm
  have hwx : ∀ i v, w (e i, v) = x i v := by
    intro i v
    rw [hw]
    · exact hz i v
    · intro hm
      exact he_free i (Finset.mem_image.2 ⟨(e i, v), hm, rfl⟩)
  obtain ⟨q, hq, hrun⟩ := run_add ask n w s
  obtain ⟨a, ha⟩ := hcorr w
  refine ⟨finProdFinEquiv (⟨q, hq⟩, a), ?_⟩
  intro i hxi
  simp only [Equiv.symm_apply_apply] at hxi
  have hspec := Classical.choose_spec (hmiss ⟨q, hq⟩ a i)
  have hai := ha (e i)
  rw [hrun, hwn] at hai
  have hblock : (fun v => w (e i, v)) = badGA ⟨q, hq⟩ a i := by
    funext v
    rw [hwx, hxi]
  have hv : ∀ v, w (e i, v) = badGA ⟨q, hq⟩ a i v := fun v => congrFun hblock v
  simp only [hv] at hai
  apply hspec
  convert hai using 2

theorem upper (m r D s L : ℕ) (hr : 0 < r)
    (bad : Fin (2 ^ s * L) → Fin (m - D) → (Fin r → Bool))
    (hcov : ∀ x : Fin (m - D) → (Fin r → Bool), ∃ a, ∀ i, x i ≠ bad a i) :
    ∃ (n : ℕ) (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool) (cost : ℕ → ℕ → ℕ)
      (leaf : ℕ → Fin L → Fin m → (Fin r → Bool) → Bool),
    (∀ h a i, ∃ F : Finset (Finset (Fin r)), (∀ T ∈ F, T.card < r) ∧
      ∀ z, leaf h a i z = Rep F z) ∧
    (∀ (input : Fin m × Fin r → Bool) (u : Fin n), ∃ G : Finset (Finset (Fin m × Fin r)),
      (∀ T ∈ G, T.card ≤ cost u.val (run ask u.val input)) ∧
      ∀ w, ask u.val (run ask u.val input) w = Rep G w) ∧
    (∀ w : Fin m × Fin r → Bool, (∑ t : Fin n, cost t.val (run ask t.val w)) ≤ D) ∧
    (∀ w : Fin m × Fin r → Bool, ∃ a, ∀ i, leaf (run ask (n + s) w) a i (fun v => w (i, v))
      = decide (∀ v : Fin r, w (i, v) = true)) := by
  classical
  set k := min D m with hk
  let blk : Fin (m - D) → Fin m := fun i => ⟨k + i.val, by have := i.isLt; omega⟩
  let res : (Fin m × Fin r → Bool) → Fin (m - D) → (Fin r → Bool) := fun w i v => w (blk i, v)
  let idx : (Fin m × Fin r → Bool) → Fin (2 ^ s * L) := fun w => Classical.choose (hcov (res w))
  let G : (Fin m × Fin r → Bool) → ℕ := fun w => (finProdFinEquiv.symm (idx w)).1.val
  let z0 : Fin r := ⟨0, hr⟩
  let ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool := fun t _ w =>
    if ht : t < k then w (⟨t, by omega⟩, z0) else (G w).testBit (t - k)
  let gOf : ℕ → Fin (2 ^ s) := fun h => ⟨(h / 2 ^ k) % 2 ^ s, Nat.mod_lt _ (by positivity)⟩
  let leaf : ℕ → Fin L → Fin m → (Fin r → Bool) → Bool := fun h a i z =>
    if hi : i.val < k then (if h.testBit i.val then decide (∀ v, v ≠ z0 → z v = true) else false)
    else xor (decide (∀ v, z v = true))
      (decide (z = bad (finProdFinEquiv (gOf h, a)) ⟨i.val - k, by have := i.isLt; omega⟩))
  refine ⟨k, ask, fun _ _ => 1, leaf, ?_, ?_, ?_, ?_⟩
  · intro h a i
    by_cases hi : i.val < k
    · by_cases hb : h.testBit i.val = true
      · refine ⟨{Finset.univ.erase z0}, ?_, fun z => ?_⟩
        · intro T hT
          rw [Finset.mem_singleton.1 hT, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin]
          omega
        · simp only [leaf, dif_pos hi, hb, ↓reduceIte]
          rw [rep_single]
          simp [Finset.mem_erase]
      · refine ⟨∅, by simp, fun z => ?_⟩
        simp only [Bool.not_eq_true] at hb
        simp only [leaf, dif_pos hi, hb]
        rw [rep_empty]
        rfl
    · obtain ⟨F, hF, hFr⟩ := low_flip
        (bad (finProdFinEquiv (gOf h, a)) ⟨i.val - k, by have := i.isLt; omega⟩)
      refine ⟨F, by simpa using hF, fun z => ?_⟩
      simp only [leaf, dif_neg hi]
      convert hFr z using 2
      all_goals exact decide_eq_decide.2 Iff.rfl
  · intro input u
    refine ⟨{{(⟨u.val, by have := u.isLt; omega⟩, z0)}}, by simp, fun w => ?_⟩
    simp only [ask, dif_pos u.isLt]
    rw [rep_single]
    simp
  · intro w
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    exact min_le_left _ _
  · intro w
    set H := run ask (k + s) w
    have F1 : ∀ i (hi : i < k), H.testBit i = w (⟨i, by omega⟩, z0) := by
      intro i hi
      rw [testBit_run ask w i (k + s) (by omega)]
      simp only [ask, dif_pos hi]
    have F2 : gOf H = (finProdFinEquiv.symm (idx w)).1 := by
      obtain ⟨q, hq, hrun⟩ := run_add ask k w s
      have hdiv : H / 2 ^ k = q := by
        simp only [H]
        rw [hrun, div_mod_split _ _ _ (run_lt ask k w)]
      apply Fin.ext
      simp only [gOf]
      rw [hdiv, Nat.mod_eq_of_lt hq]
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < s
      · rw [← hdiv, Nat.testBit_div_two_pow, testBit_run ask w (j + k) (k + s) (by omega)]
        simp only [ask, show ¬ (j + k < k) by omega, dite_false, G]
        congr 1
        omega
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (finProdFinEquiv.symm (idx w)).1.isLt
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    refine ⟨(finProdFinEquiv.symm (idx w)).2, fun i => ?_⟩
    by_cases hi : i.val < k
    · simp only [leaf, dif_pos hi]
      rw [F1 i.val hi]
      have hi' : (⟨i.val, by omega⟩ : Fin m) = i := Fin.ext rfl
      rw [hi']
      cases hw0 : w (i, z0)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        symm
        simp only [decide_eq_false_iff_not, not_forall]
        exact ⟨z0, by simp [hw0]⟩
      · simp only [↓reduceIte]
        apply decide_eq_decide.2
        constructor
        · intro h v
          by_cases hv : v = z0
          · rw [hv]; exact hw0
          · exact h v hv
        · intro h v _
          exact h v
    · simp only [leaf, dif_neg hi]
      rw [F2]
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
      have hj : blk ⟨i.val - k, by have := i.isLt; omega⟩ = i := by
        apply Fin.ext
        simp only [blk]
        omega
      have hne := Classical.choose_spec (hcov (res w)) ⟨i.val - k, by have := i.isLt; omega⟩
      have hres : res w ⟨i.val - k, by have := i.isLt; omega⟩ = fun v => w (i, v) := by
        funext v
        simp only [res, hj]
      rw [hres] at hne
      have : decide ((fun v => w (i, v)) = bad (idx w) ⟨i.val - k, by have := i.isLt; omega⟩)
          = false := by
        simpa using hne
      rw [this]
      simp

theorem filter_inst_eq {β : Type} (t : Finset β) (p : β → Prop) (i1 i2 : DecidablePred p) :
    @Finset.filter β p i1 t = @Finset.filter β p i2 t := by
  rw [Subsingleton.elim i1 i2]

end PEqualNP.Outside.L_lib_612

theorem PEqualNP.Outside.L_lib_612 : (∀ (m r D s L : Nat), 0 < r →
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ word,
      f word = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)
  let low := fun (q : Symbol → Bool) => ∃ terms : Finset (Finset (Fin r)),
    (∀ mon ∈ terms, mon.card < r) ∧ ∀ word,
      q word = (((terms.filter (fun mon => ∀ z ∈ mon, word z = true)).card % 2) == 1)
  let run := fun (ask : Nat → Nat → W → Bool) (len : Nat) (x : W) =>
    (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0
  let residual := m-D
  let covers := ∃ bad : Fin (2^s*L) → Fin residual → Symbol,
    ∀ x : Fin residual → Symbol, ∃ a, ∀ i, x i ≠ bad a i
  let possible := ∃ (n : Nat) (ask : Nat → Nat → W → Bool) (cost : Nat → Nat → Nat)
      (leaf : Nat → Fin L → Fin m → Symbol → Bool),
    (∀ h a i, low (leaf h a i)) ∧
    (∀ input (u : Fin n), deg (cost u.val (run ask u.val input))
      (ask u.val (run ask u.val input))) ∧
    (∀ word : W, (∑ t : Fin n, cost t.val (run ask t.val word)) ≤ D) ∧
    ∀ w : W, ∃ a, ∀ i, leaf (run ask (n+s) w) a i (fun v => w (i,v)) =
      decide (∀ v : Fin r, w (i,v) = true)
  possible ↔ covers) := by
  intro m r D s L hr
  intro V W Symbol deg low run residual covers possible
  constructor
  · rintro ⟨n, ask, cost, leaf, hleaf, hdeg, hcost, hcorr⟩
    refine PEqualNP.Outside.L_lib_612.lower m r D s L n ask cost leaf (fun h a i => ?_)
      (fun input u => ?_) hcost hcorr
    · obtain ⟨F, hF, hFr⟩ := hleaf h a i
      refine ⟨F, hF, fun z => ?_⟩
      rw [hFr z]
      unfold PEqualNP.Outside.L_lib_612.Rep
      congr 3 <;> exact PEqualNP.Outside.L_lib_612.filter_inst_eq _ _ _ _
    · obtain ⟨G, hG, hGr⟩ := hdeg input u
      refine ⟨G, hG, fun w => ?_⟩
      have e : PEqualNP.Outside.L_lib_612.run ask u input = run ask u input := rfl
      rw [e, hGr w]
      unfold PEqualNP.Outside.L_lib_612.Rep
      congr 3 <;> exact PEqualNP.Outside.L_lib_612.filter_inst_eq _ _ _ _
  · rintro ⟨bad, hcov⟩
    obtain ⟨n, ask, cost, leaf, h1, h2, h3, h4⟩ :=
      PEqualNP.Outside.L_lib_612.upper m r D s L hr bad hcov
    refine ⟨n, ask, cost, leaf, fun h a i => ?_, fun input u => ?_, h3, h4⟩
    · obtain ⟨F, hF, hFr⟩ := h1 h a i
      refine ⟨F, hF, fun z => ?_⟩
      rw [hFr z]
      unfold PEqualNP.Outside.L_lib_612.Rep
      congr 3 <;> exact PEqualNP.Outside.L_lib_612.filter_inst_eq _ _ _ _
    · obtain ⟨G, hG, hGr⟩ := h2 input u
      refine ⟨G, hG, fun w => ?_⟩
      have e : PEqualNP.Outside.L_lib_612.run ask u input = run ask u input := rfl
      rw [← e, hGr w]
      unfold PEqualNP.Outside.L_lib_612.Rep
      congr 3 <;> exact PEqualNP.Outside.L_lib_612.filter_inst_eq _ _ _ _

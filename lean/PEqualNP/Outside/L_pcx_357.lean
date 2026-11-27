import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_357

open Finset

abbrev Slot (t p : ℕ) : Type := (Σ j : Fin t, Fin (t + j.val) × Bool) ⊕ Fin p

lemma total (t : ℕ) : ∑ j : Fin t, (t + j.val) * 2 = 3 * t ^ 2 - t := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (t + j) * 2), ← sum_mul, sum_add_distrib, sum_const,
    card_range, smul_eq_mul, add_mul, sum_range_id_mul_two]
  cases t with
  | zero => rfl
  | succ k =>
    rw [Nat.add_sub_cancel]
    symm
    apply Nat.sub_eq_of_eq_add
    ring

def mm (t p : ℕ) (c : Fin 3) : Equiv.Perm (Slot t p) :=
  Equiv.sumCongr
    (Equiv.sigmaCongrRight fun j =>
      if c = 1 then
        { toFun := fun x => (if x.2 = false then finRotate _ x.1 else x.1, x.2)
          invFun := fun x => (if x.2 = false then (finRotate _).symm x.1 else x.1, x.2)
          left_inv := fun x => by
            rcases x with ⟨k, b⟩
            cases b
            · exact Prod.ext (Equiv.symm_apply_apply _ k) rfl
            · rfl
          right_inv := fun x => by
            rcases x with ⟨k, b⟩
            cases b
            · exact Prod.ext (Equiv.apply_symm_apply _ k) rfl
            · rfl }
      else if c = 2 then Equiv.prodCongr (Equiv.refl _) Equiv.boolNot
      else Equiv.refl _)
    (Equiv.refl _)

lemma mm0 (t p : ℕ) (s : Slot t p) : mm t p 0 s = s := by
  rcases s with ⟨j, k, b⟩ | q
  · simp [mm, show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide]
  · simp [mm]

lemma mm1a (t p : ℕ) (j : Fin t) (k : Fin (t + j.val)) :
    mm t p 1 (Sum.inl ⟨j, k, false⟩) = Sum.inl ⟨j, finRotate _ k, false⟩ := by
  simp [mm]

lemma mm1b (t p : ℕ) (j : Fin t) (k : Fin (t + j.val)) :
    mm t p 1 (Sum.inl ⟨j, k, true⟩) = Sum.inl ⟨j, k, true⟩ := by
  simp [mm]

lemma mm1c (t p : ℕ) (q : Fin p) : mm t p 1 (Sum.inr q) = Sum.inr q := by
  simp [mm]

lemma mm2a (t p : ℕ) (j : Fin t) (k : Fin (t + j.val)) (b : Bool) :
    mm t p 2 (Sum.inl ⟨j, k, b⟩) = Sum.inl ⟨j, k, !b⟩ := by
  simp [mm, show (2 : Fin 3) ≠ 1 by decide]

lemma mm2c (t p : ℕ) (q : Fin p) : mm t p 2 (Sum.inr q) = Sum.inr q := by
  simp [mm]

lemma unique_block (t : ℕ) (c : Fin t → Bool) (j : Fin t)
    (h : ∑ i : Fin t, (if c i then (t + i.val) * 2 else 0) = (t + j.val) * 2) : c j = true := by
  by_contra hj
  have jt := j.isLt
  by_cases e : ∃ a, c a = true
  · obtain ⟨a, ha⟩ := e
    have aj : a ≠ j := fun x => hj (x ▸ ha)
    by_cases two : ∃ b, b ≠ a ∧ c b = true
    · obtain ⟨b, ba, hb⟩ := two
      have le : ∑ i ∈ ({a, b} : Finset (Fin t)), (if c i then (t + i.val) * 2 else 0) ≤
          ∑ i : Fin t, (if c i then (t + i.val) * 2 else 0) :=
        sum_le_sum_of_subset (subset_univ _)
      rw [sum_pair (Ne.symm ba), if_pos ha, if_pos hb, h] at le
      omega
    · have : ∑ i : Fin t, (if c i then (t + i.val) * 2 else 0) = (t + a.val) * 2 := by
        rw [sum_eq_single a]
        · rw [if_pos ha]
        · intro b _ ba
          rw [if_neg]
          exact fun hb => two ⟨b, ba, hb⟩
        · simp
      rw [this] at h
      exact aj (Fin.ext (by omega))
  · have : ∑ i : Fin t, (if c i then (t + i.val) * 2 else 0) = 0 :=
      sum_eq_zero fun i _ => if_neg fun hi => e ⟨i, hi⟩
    rw [this] at h
    omega

lemma rot_const {m : ℕ} (f : Fin m → Bool) (h : ∀ k, f (finRotate m k) = f k) (k : Fin m)
    (hm : 0 < m) : f k = f ⟨0, hm⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨v, hv⟩ := k
  induction v with
  | zero => rfl
  | succ v ih =>
    have r : finRotate (n + 1) ⟨v, by omega⟩ = ⟨v + 1, hv⟩ := by
      rw [finRotate_of_lt (by omega)]
    rw [← r, h]
    exact ih (by omega)

lemma ball (t d : ℕ) (b : Fin t → Bool) :
    (univ.filter fun a : Fin t → Bool => (univ.filter fun j => b j ≠ a j).card ≤ d).card ≤
      ∑ h ∈ range (d + 1), t.choose h := by
  have le : (univ.filter fun a : Fin t → Bool => (univ.filter fun j => b j ≠ a j).card ≤ d).card ≤
      ((range (d + 1)).biUnion fun h => powersetCard h (univ : Finset (Fin t))).card := by
    apply card_le_card_of_injOn (fun a => univ.filter fun j => b j ≠ a j)
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha
      simp only [coe_biUnion, coe_range, Set.mem_Iio, Set.mem_iUnion, mem_coe, mem_powersetCard]
      exact ⟨_, Nat.lt_succ_of_le ha, subset_univ _, rfl⟩
    · intro x _ y _ e
      funext j
      have := Finset.ext_iff.mp e j
      simp only [mem_filter, mem_univ, true_and] at this
      revert this
      cases b j <;> cases x j <;> cases y j <;> simp
  refine le.trans (card_biUnion_le.trans (le_of_eq (sum_congr rfl fun h _ => ?_)))
  rw [card_powersetCard, card_univ, Fintype.card_fin]

lemma seed (t K : ℕ) (f : (Fin t → Bool) → Fin K) (g : Fin K → Fin t → Bool) :
    ∑ d ∈ range t, (2 ^ t - K * ∑ h ∈ range (d + 1), t.choose h) ≤
      ∑ a : Fin t → Bool, (univ.filter fun j => g (f a) j ≠ a j).card := by
  let e := fun a : Fin t → Bool => (univ.filter fun j => g (f a) j ≠ a j).card
  have layer : ∀ d, 2 ^ t - K * ∑ h ∈ range (d + 1), t.choose h ≤
      (univ.filter fun a => d < e a).card := by
    intro d
    have small : (univ.filter fun a => e a ≤ d).card ≤ K * ∑ h ∈ range (d + 1), t.choose h := by
      have sub : (univ.filter fun a => e a ≤ d) ⊆ (univ : Finset (Fin K)).biUnion fun x =>
          univ.filter fun a : Fin t → Bool => (univ.filter fun j => g x j ≠ a j).card ≤ d := by
        intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha
        simp only [mem_biUnion, mem_filter, mem_univ, true_and]
        exact ⟨f a, ha⟩
      refine (card_le_card sub).trans (card_biUnion_le.trans ?_)
      refine (sum_le_sum fun x _ => ball t d (g x)).trans (le_of_eq ?_)
      rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have both := card_filter_add_card_filter_not (s := (univ : Finset (Fin t → Bool)))
      (fun a => e a ≤ d)
    simp only [not_le] at both
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at both
    omega
  refine (sum_le_sum fun d _ => layer d).trans ?_
  simp only [card_filter]
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  refine le_trans ?_ (le_of_eq (show e a = _ from card_filter _ _))
  rw [← card_filter]
  refine (card_le_card (t := range (e a)) ?_).trans (by rw [card_range])
  intro d hd
  simp only [mem_filter] at hd
  exact mem_range.mpr hd.2

end PEqualNP.Outside.L_pcx_357

theorem PEqualNP.Outside.L_pcx_357 : (∀ t n : ℕ, 3*t^2-t ≤ n →
  let V := Bool × Fin n
  let X := V → Bool
  let Message := Fin t → Bool
  ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (port : V → Option (Fin t)) (hard : X),
    let pin := fun (a : Message) (v : V) => ((port v).map (fun j => !(a j))).getD (hard v)
    let truth := fun (a : Message) (j : Fin t) =>
      decide (0 < ((Finset.univ : Finset X).filter (fun y =>
        (∀ v, pin a v = true → y v = false) ∧
        ∀ c : Fin 3, (Finset.univ.filter (fun i : Fin n =>
          y (false,i) ≠ y (true,M c i))).card =
          (if c = 2 then 2*(t+j.val) else 0))).card)
    (∀ a j, truth a j = a j) ∧
      ∀ (r K : ℕ) (enc : Fin (r+1) → X → Fin K)
        (ans : Fin (r+1) → Fin K → Fin t → Bool),
        let err := fun (s : Fin (r+1)) (a : Message) =>
          (Finset.univ.filter (fun j : Fin t => ans s (enc s (pin a)) j ≠ truth a j)).card
        (r+1) * (∑ d ∈ Finset.range t,
          (2^t - K * (∑ h ∈ Finset.range (d+1), t.choose h))) ≤
          ∑ s : Fin (r+1), ∑ a : Message, err s a) := by
  intro t n hn V X Message
  obtain ⟨p, hp⟩ : ∃ p, n = (3 * t ^ 2 - t) + p := ⟨n - (3 * t ^ 2 - t), by omega⟩
  have hc : Fintype.card (PEqualNP.Outside.L_pcx_357.Slot t p) = n := by
    rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hp]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    exact PEqualNP.Outside.L_pcx_357.total t
  let e : Fin n ≃ PEqualNP.Outside.L_pcx_357.Slot t p := (Fintype.equivFinOfCardEq hc).symm
  let M : Fin 3 → Equiv.Perm (Fin n) := fun c =>
    e.symm.permCongr (PEqualNP.Outside.L_pcx_357.mm t p c)
  let port : V → Option (Fin t) := fun v =>
    match e v.2 with
    | Sum.inl ⟨j, k, false⟩ => if v.1 = false ∧ k.val = 0 then some j else none
    | _ => none
  let hard : X := fun v =>
    match e v.2 with
    | Sum.inl ⟨_, _, false⟩ => false
    | _ => true
  refine ⟨M, port, hard, ?_⟩
  intro pin truth
  have eM : ∀ c i, e (M c i) = PEqualNP.Outside.L_pcx_357.mm t p c (e i) := by
    intro c i
    simp [M, Equiv.permCongr_apply]
  have cnt : ∀ (y : X) (c : Fin 3),
      (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, M c i))).card =
      (Finset.univ.filter (fun s : PEqualNP.Outside.L_pcx_357.Slot t p =>
        y (false, e.symm s) ≠ y (true, e.symm (PEqualNP.Outside.L_pcx_357.mm t p c s)))).card := by
    intro y c
    apply Finset.card_equiv e
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← eM, Equiv.symm_apply_apply]
  have htruth : ∀ a j, truth a j = a j := by
    intro a j
    have m0 : 0 < t + j.val := by have := j.isLt; omega
    have key : (0 < ((Finset.univ : Finset X).filter (fun y =>
        (∀ v, pin a v = true → y v = false) ∧
        ∀ c : Fin 3, (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, M c i))).card =
          (if c = 2 then 2 * (t + j.val) else 0))).card) ↔ a j = true := by
      rw [Finset.card_pos]
      constructor
      · rintro ⟨y, hy⟩
        rw [Finset.mem_filter] at hy
        obtain ⟨_, pins, counts⟩ := hy
        let Y : Bool → PEqualNP.Outside.L_pcx_357.Slot t p → Bool := fun b s => y (b, e.symm s)
        have zero : ∀ c : Fin 3, c ≠ 2 → ∀ s, Y false s = Y true (PEqualNP.Outside.L_pcx_357.mm t p c s) := by
          intro c hc2 s
          have z := counts c
          rw [if_neg hc2, cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at z
          exact not_not.mp (z (Finset.mem_univ s))
        have same : ∀ s, Y false s = Y true s := by
          intro s
          have := zero 0 (by decide) s
          rwa [PEqualNP.Outside.L_pcx_357.mm0] at this
        have bank : ∀ b i k, Y b (Sum.inl ⟨i, k, true⟩) = false := by
          intro b i k
          apply pins
          simp [pin, port, hard]
        have pad : ∀ b q, Y b (Sum.inr q) = false := by
          intro b q
          apply pins
          simp [pin, port, hard]
        have pos : ∀ i : Fin t, 0 < t + i.val := fun i => by have := i.isLt; omega
        let c : Fin t → Bool := fun i => Y false (Sum.inl ⟨i, ⟨0, pos i⟩, false⟩)
        have cyc : ∀ i k, Y false (Sum.inl ⟨i, k, false⟩) = c i := by
          intro i k
          apply PEqualNP.Outside.L_pcx_357.rot_const (fun k => Y false (Sum.inl ⟨i, k, false⟩))
          intro k
          have h1 := zero 1 (by decide) (Sum.inl ⟨i, k, false⟩)
          rw [PEqualNP.Outside.L_pcx_357.mm1a, ← same] at h1
          exact h1.symm
        have two := counts 2
        rw [if_pos rfl, cnt, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma] at two
        have padsum : ∑ q : Fin p, (if y (false, e.symm (Sum.inr q)) ≠
            y (true, e.symm (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inr q))) then 1 else 0) = 0 := by
          refine Finset.sum_eq_zero fun q _ => if_neg ?_
          rw [PEqualNP.Outside.L_pcx_357.mm2c]
          change ¬(Y false (Sum.inr q) ≠ Y true (Sum.inr q))
          rw [pad, pad]
          simp
        have block : ∀ i : Fin t, (∑ x : Fin (t + i.val) × Bool,
            (if y (false, e.symm (Sum.inl ⟨i, x⟩)) ≠
              y (true, e.symm (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inl ⟨i, x⟩))) then 1 else 0)) =
            if c i then (t + i.val) * 2 else 0 := by
          intro i
          have each : ∀ x : Fin (t + i.val) × Bool,
              (if y (false, e.symm (Sum.inl ⟨i, x⟩)) ≠
                y (true, e.symm (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inl ⟨i, x⟩))) then 1 else 0) =
              if c i then 1 else 0 := by
            rintro ⟨k, b⟩
            rw [PEqualNP.Outside.L_pcx_357.mm2a]
            change (if Y false (Sum.inl ⟨i, k, b⟩) ≠ Y true (Sum.inl ⟨i, k, !b⟩) then 1 else 0) = _
            cases b
            · rw [cyc, Bool.not_false, bank]
              cases c i <;> simp
            · rw [Bool.not_true, bank, ← same, cyc]
              cases c i <;> simp
          rw [Finset.sum_congr rfl fun x _ => each x, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          split_ifs <;> simp
        rw [padsum, add_zero, Finset.sum_congr rfl fun i _ => block i, Nat.mul_comm 2] at two
        have cj := PEqualNP.Outside.L_pcx_357.unique_block t c j two
        by_contra na
        have : Y false (Sum.inl ⟨j, ⟨0, pos j⟩, false⟩) = false := by
          apply pins
          simpa [pin, port] using na
        change c j = false at this
        rw [cj] at this
        exact Bool.noConfusion this
      · intro aj
        let Z : PEqualNP.Outside.L_pcx_357.Slot t p → Bool := fun s =>
          match s with
          | Sum.inl ⟨i, _, false⟩ => decide (i = j)
          | _ => false
        let y : X := fun v => Z (e v.2)
        refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
        · intro v hv
          obtain ⟨b, i⟩ := v
          change Z (e i) = false
          rcases h : e i with ⟨i', k, d⟩ | q
          · cases d
            · by_cases ij : i' = j
              · exfalso
                subst ij
                simp only [pin, port, hard, h] at hv
                split_ifs at hv
                · simp [aj] at hv
                · simp at hv
              · simp [Z, ij]
            · rfl
          · rfl
        · intro c
          rw [cnt]
          have yz : ∀ b s, y (b, e.symm s) = Z s := fun b s => by simp [y]
          simp only [yz]
          fin_cases c
          · change _ = (if (0 : Fin 3) = 2 then 2 * (t + j.val) else 0)
            rw [if_neg (by decide), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro s _
            change ¬(Z s ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 0 s))
            rw [PEqualNP.Outside.L_pcx_357.mm0]
            simp
          · change _ = (if (1 : Fin 3) = 2 then 2 * (t + j.val) else 0)
            rw [if_neg (by decide), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro s _
            change ¬(Z s ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 1 s))
            rcases s with ⟨i, k, b⟩ | q
            · cases b
              · rw [PEqualNP.Outside.L_pcx_357.mm1a]; simp [Z]
              · rw [PEqualNP.Outside.L_pcx_357.mm1b]; simp
            · rw [PEqualNP.Outside.L_pcx_357.mm1c]; simp
          · change _ = (if (2 : Fin 3) = 2 then 2 * (t + j.val) else 0)
            rw [if_pos rfl, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
            change (∑ i : Fin t, ∑ x : Fin (t + i.val) × Bool,
                (if Z (Sum.inl ⟨i, x⟩) ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inl ⟨i, x⟩)) then 1 else 0)) +
              (∑ q : Fin p, (if Z (Sum.inr q) ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inr q)) then 1 else 0)) = _
            have padsum : (∑ q : Fin p, (if Z (Sum.inr q) ≠
                Z (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inr q)) then 1 else 0)) = 0 := by
              refine Finset.sum_eq_zero fun q _ => if_neg ?_
              rw [PEqualNP.Outside.L_pcx_357.mm2c]
              simp
            have block : ∀ i : Fin t, (∑ x : Fin (t + i.val) × Bool,
                (if Z (Sum.inl ⟨i, x⟩) ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inl ⟨i, x⟩)) then 1 else 0)) =
                if i = j then (t + i.val) * 2 else 0 := by
              intro i
              have each : ∀ x : Fin (t + i.val) × Bool,
                  (if Z (Sum.inl ⟨i, x⟩) ≠ Z (PEqualNP.Outside.L_pcx_357.mm t p 2 (Sum.inl ⟨i, x⟩)) then 1 else 0) =
                  if i = j then 1 else 0 := by
                rintro ⟨k, b⟩
                rw [PEqualNP.Outside.L_pcx_357.mm2a]
                cases b <;> by_cases ij : i = j <;> simp [Z, ij]
              rw [Finset.sum_congr rfl fun x _ => each x, Finset.sum_const, Finset.card_univ,
                Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
              split_ifs <;> simp
            rw [padsum, add_zero, Finset.sum_congr rfl fun i _ => block i, Finset.sum_ite_eq' Finset.univ j,
              if_pos (Finset.mem_univ _), Nat.mul_comm]
    change decide _ = a j
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact key
  refine ⟨htruth, ?_⟩
  intro r K enc ans err
  have each : ∀ s : Fin (r + 1), (∑ d ∈ Finset.range t,
      (2 ^ t - K * (∑ h ∈ Finset.range (d + 1), t.choose h))) ≤ ∑ a : Message, err s a := by
    intro s
    refine (PEqualNP.Outside.L_pcx_357.seed t K (fun a => enc s (pin a)) (ans s)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [err, htruth]
  have := Finset.sum_le_sum (s := Finset.univ) fun s _ => each s
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this

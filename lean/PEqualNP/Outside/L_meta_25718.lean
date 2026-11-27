import PEqualNP.Outside.L_lib_621

namespace PEqualNP.Outside.L_meta_25718

private def readerTrace {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T : Finset α) : List Bool :=
  (List.range q).foldl (fun h i => h ++ [decide (ask i h ∈ T)]) []

private def readerSeen {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T : Finset α) : Finset α :=
  ((List.range q).map (fun i => ask i (readerTrace ask i T))).toFinset

private lemma readerTrace_succ {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T : Finset α) :
    readerTrace ask (q + 1) T =
      readerTrace ask q T ++ [decide (ask q (readerTrace ask q T) ∈ T)] := by
  simp only [readerTrace, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private lemma readerSeen_succ {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T : Finset α) :
    readerSeen ask (q + 1) T = insert (ask q (readerTrace ask q T)) (readerSeen ask q T) := by
  ext a
  simp only [readerSeen, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_insert]
  exact or_comm

private lemma reader_congr {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T U : Finset α)
    (agree : ∀ a ∈ readerSeen ask q T, a ∈ T ↔ a ∈ U) :
    readerTrace ask q T = readerTrace ask q U ∧ readerSeen ask q T = readerSeen ask q U := by
  induction q with
  | zero => exact ⟨rfl, rfl⟩
  | succ q ih =>
    rw [readerSeen_succ] at agree
    obtain ⟨trace_eq, seen_eq⟩ :=
      ih (fun a ha => agree a (Finset.mem_insert_of_mem ha))
    have bit_eq : decide (ask q (readerTrace ask q T) ∈ T) =
        decide (ask q (readerTrace ask q T) ∈ U) := decide_eq_decide.mpr
      (agree _ (Finset.mem_insert_self _ _))
    constructor
    · rw [readerTrace_succ, readerTrace_succ, ← trace_eq, bit_eq]
    · rw [readerSeen_succ, readerSeen_succ, ← trace_eq, seen_eq]

private lemma card_even_of_pairing {α : Type} [DecidableEq α]
    (S : Finset α) (pair : α → α)
    (closed : ∀ a ∈ S, pair a ∈ S)
    (twice : ∀ a ∈ S, pair (pair a) = a)
    (distinct : ∀ a ∈ S, pair a ≠ a) : S.card % 2 = 0 := by
  induction S using Finset.strongInductionOn
  case _ S ih =>
    by_cases empty : S = ∅
    · simp [empty]
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have hp := closed a ha
      have hpa := distinct a ha
      let R := (S.erase a).erase (pair a)
      have sub : R ⊆ S := fun x hx =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have proper : R ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sub, ?_⟩
        intro eq
        have : a ∈ R := eq.symm ▸ ha
        simp [R] at this
      have closedR : ∀ x ∈ R, pair x ∈ R := by
        intro x hx
        have hxS := sub hx
        simp only [R, Finset.mem_erase] at hx ⊢
        refine ⟨?_, ?_, closed x hxS⟩
        · intro eq
          exact hx.2.1 (by simpa only [twice x hxS, twice a ha] using congrArg pair eq)
        · intro eq
          exact hx.1 (by simpa only [twice x hxS] using congrArg pair eq)
      have evenR := ih R proper closedR
        (fun x hx => twice x (sub hx)) (fun x hx => distinct x (sub hx))
      have h₁ := Finset.card_erase_add_one ha
      have h₂ : R.card + 1 = (S.erase a).card :=
        Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hpa, hp⟩)
      omega

private lemma full_read_parity {α : Type} [DecidableEq α] (F : Finset α)
    (ask : Nat → List Bool → α) (out : List Bool → Bool) (q : Nat) (b : Bool) :
    ((F.powerset.filter
      (fun T => out (readerTrace ask q T) = b ∧ F ⊆ readerSeen ask q T)).card).testBit 0 =
    ((F.powerset.filter (fun T => out (readerTrace ask q T) = b)).card).testBit 0 := by
  classical
  let seen := readerSeen ask q
  let P := F.powerset.filter (fun T => out (readerTrace ask q T) = b)
  let pair (T : Finset α) :=
    if h : (F \ seen T).Nonempty then symmDiff T {h.choose} else T
  have missed (T : Finset α) (h : ¬ F ⊆ seen T) : (F \ seen T).Nonempty := by
    obtain ⟨a, haF, haSeen⟩ := Finset.not_subset.mp h
    exact ⟨a, Finset.mem_sdiff.mpr ⟨haF, haSeen⟩⟩
  have agrees (T : Finset α) (a : α) (ha : a ∈ seen T) : a ∈ T ↔ a ∈ pair T := by
    by_cases h : (F \ seen T).Nonempty
    · have ne : a ≠ h.choose := fun eq =>
        (Finset.mem_sdiff.mp h.choose_spec).2 (eq ▸ ha)
      simp [pair, h, Finset.mem_symmDiff, ne]
    · simp [pair, h]
  have stays (T : Finset α) := reader_congr ask q T (pair T) (agrees T)
  have seen_eq (T : Finset α) : seen (pair T) = seen T := (stays T).2.symm
  have flip_again (T : Finset α) (h : (F \ seen T).Nonempty) :
      pair (pair T) = T := by
    unfold pair
    rw [dite_eq_left h]
    have he : seen (symmDiff T {h.choose}) = seen T := by
      simpa only [pair, dite_eq_left h] using seen_eq T
    simp only [he, dite_eq_left h, symmDiff_symmDiff_cancel_right]
  have even : (P.filter (fun T => ¬ F ⊆ seen T)).card % 2 = 0 := by
    apply card_even_of_pairing _ pair
    · intro T hT
      simp only [P, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      obtain ⟨⟨sub, answer⟩, incomplete⟩ := hT
      refine ⟨⟨?_, (congrArg out (stays T).1).symm.trans answer⟩, ?_⟩
      · have h := missed T incomplete
        intro a ha
        simp only [pair, dite_eq_left h, Finset.mem_symmDiff, Finset.mem_singleton] at ha
        rcases ha with ⟨ha, _⟩ | ⟨rfl, _⟩
        · exact sub ha
        · exact (Finset.mem_sdiff.mp h.choose_spec).1
      · simpa only [seen_eq] using incomplete
    · intro T hT
      exact flip_again T (missed T (Finset.mem_filter.mp hT).2)
    · intro T hT eq
      have h := missed T (Finset.mem_filter.mp hT).2
      have same := congrArg (fun U : Finset α => h.choose ∈ U) eq
      simp [pair, h, Finset.mem_symmDiff] at same
  have split := Finset.card_filter_add_card_filter_not (s := P) (fun T => F ⊆ seen T)
  have good : P.filter (fun T => F ⊆ seen T) =
      F.powerset.filter (fun T => out (readerTrace ask q T) = b ∧ F ⊆ seen T) := by
    ext T
    simp only [P, seen, Finset.mem_filter, and_assoc]
  have parity : (P.filter (fun T => F ⊆ seen T)).card % 2 = P.card % 2 := by omega
  simpa only [good, Nat.testBit_zero] using
    congrArg (fun n : Nat => decide (n = 1)) parity

private lemma readerSeen_card_le {α : Type} [DecidableEq α] (ask : Nat → List Bool → α)
    (q : Nat) (T : Finset α) : (readerSeen ask q T).card ≤ q := by
  have h := List.toFinset_card_le ((List.range q).map (fun i => ask i (readerTrace ask i T)))
  simpa only [readerSeen, List.length_map, List.length_range] using h

private lemma read_all {α : Type} [DecidableEq α] (F : Finset α)
    (nonempty : F.Nonempty) (answer : Finset α → Bool) :
    ∃ (read : Nat → α) (decode : List Bool → Bool), ∀ T ∈ F.powerset,
      decode ((List.range F.card).map (fun i => decide (read i ∈ T))) = answer T := by
  classical
  let index : Fin F.card ≃ F := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
  let read (i : Nat) := if hi : i < F.card then (index ⟨i, hi⟩).val else nonempty.choose
  let decode (bits : List Bool) := answer
    ((F.attach.filter (fun a => bits[(index.symm a).val]? = some true)).image Subtype.val)
  refine ⟨read, decode, ?_⟩
  intro T hT
  have read_back (a : F) :
      ((List.range F.card).map (fun i => decide (read i ∈ T)))[(index.symm a).val]? =
        some (decide (a.val ∈ T)) := by
    simp [(index.symm a).isLt, read]
  apply congrArg answer
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, read_back,
    Option.some.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨⟨a, (Finset.mem_powerset.mp hT) ha⟩, ha, rfl⟩

private lemma cyclic_scope_card {n k : Nat} (hn : 0 < n) (hk : k ≤ n) (i : Fin n) :
    ((Finset.range k).image
      (fun a => (⟨(i.val + a) % n, Nat.mod_lt _ hn⟩ : Fin n))).card = k := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb eq
  have shifted : i.val + a ≡ i.val + b [MOD n] := congrArg Fin.val eq
  have unshifted := Nat.ModEq.add_left_cancel' i.val shifted
  change a % n = b % n at unshifted
  rwa [Nat.mod_eq_of_lt ((Finset.mem_range.mp ha).trans_le hk),
    Nat.mod_eq_of_lt ((Finset.mem_range.mp hb).trans_le hk)] at unshifted

private def slots {n : Nat} (scope : Fin n → Finset (Fin n)) (U : Finset (Fin n)) :
    Finset (Fin n × Finset (Fin n)) :=
  Finset.univ.filter (fun s => s.2 ⊆ scope s.1 ∩ U)

private def solutionCount {n : Nat} (scope : Fin n → Finset (Fin n)) (U : Finset (Fin n))
    (T : Finset (Fin n × Finset (Fin n))) : Nat :=
  (U.powerset.filter (fun x => ∀ i : Fin n, (i, x ∩ scope i) ∈ T)).card

private lemma slots_card {n k : Nat} (scope : Fin n → Finset (Fin n))
    (scope_card : ∀ i, (scope i).card = k) :
    (slots scope Finset.univ).card = n * 2 ^ k := by
  classical
  let rows (i : Fin n) := (scope i).powerset
  calc
    (slots scope Finset.univ).card = (Finset.univ.sigma rows).card := by
      refine Finset.card_nbij' (fun s => ⟨s.1, s.2⟩) (fun s => (s.1, s.2)) ?_ ?_ ?_ ?_
      · intro a ha
        simpa [Finset.mem_sigma, rows, slots] using ha
      · intro a ha
        simpa [Finset.mem_sigma, rows, slots] using ha
      · intro a _
        rfl
      · rintro ⟨i, S⟩ _
        rfl
    _ = n * 2 ^ k := by simp [Finset.card_sigma, rows, Finset.card_powerset, scope_card]

private lemma empty_slots_card {n : Nat} (scope : Fin n → Finset (Fin n)) :
    (slots scope ∅).card = n := by
  let entry (i : Fin n) := (i, (∅ : Finset (Fin n)))
  have entries : slots scope ∅ = Finset.univ.image entry := by
    ext ⟨i, S⟩
    simp [slots, entry, eq_comm]
  have injective : Function.Injective entry := fun _ _ eq => congrArg Prod.fst eq
  rw [entries, Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_fin]

private lemma empty_solutionCount {n : Nat} (scope : Fin n → Finset (Fin n))
    (T : Finset (Fin n × Finset (Fin n))) (sub : T ⊆ slots scope ∅) :
    solutionCount scope ∅ T = if T = slots scope ∅ then 1 else 0 := by
  have all_rows : (∀ i : Fin n, (i, (∅ : Finset (Fin n))) ∈ T) ↔ T = slots scope ∅ := by
    constructor
    · intro h
      apply Finset.Subset.antisymm sub
      rintro ⟨i, S⟩ hi
      have hS : S = ∅ := by simpa [slots] using hi
      simpa [hS] using h i
    · rintro rfl i
      simp [slots]
  simp only [solutionCount, Finset.powerset_empty, Finset.filter_singleton,
    Finset.empty_inter, all_rows]
  split_ifs <;> simp

private lemma table_parity {n : Nat} (hn : 0 < n) (scope : Fin n → Finset (Fin n))
    (g : Nat → Bool) (b : Bool) :
    (((slots scope Finset.univ).powerset.filter
      (fun T => g (solutionCount scope Finset.univ T) = b)).card).testBit 0 =
      xor (g 0) (g (2 ^ n)) := by
  let base := slots scope ∅
  let lift := (slots scope Finset.univ).filter (fun s => (s.1, s.2 ∩ ∅) ∈ base)
  have lift_eq : lift = slots scope Finset.univ := by
    ext s
    simp [lift, base, slots]
  have projected := PEqualNP.Outside.L_lib_621 n n scope ∅ base (Finset.Subset.refl base)
    (fun k => decide (g k = b))
  let p := fun T => g (2 ^ n * solutionCount scope ∅ T) = b
  change ((lift.powerset.filter
    (fun T => decide (g (solutionCount scope Finset.univ T) = b))).card).testBit 0 =
    ((base.powerset.filter
      (fun T => decide (g (2 ^ (n - (∅ : Finset (Fin n)).card) *
        solutionCount scope ∅ T) = b))).card).testBit 0 at projected
  simp only [lift_eq, Finset.card_empty, Nat.sub_zero, decide_eq_true_eq] at projected
  rw [projected]
  change ((base.powerset.filter p).card).testBit 0 = _
  let smaller := base.powerset.erase base
  have base_mem : base ∈ base.powerset := Finset.mem_powerset_self _
  have base_parity : 2 ^ n % 2 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [pow_succ]
    omega
  have smaller_card : smaller.card + 1 = 2 ^ n := by
    rw [Finset.card_erase_add_one base_mem, Finset.card_powerset, empty_slots_card scope]
  have smaller_parity : smaller.card % 2 = 1 := by omega
  have smaller_succ_parity : (smaller.card + 1) % 2 = 0 := by omega
  have filter_smaller : smaller.filter p = if g 0 = b then smaller else ∅ := by
    ext T
    by_cases hT : T ∈ smaller
    · have ⟨ne, mem⟩ := Finset.mem_erase.mp hT
      have hcount := empty_solutionCount scope T (Finset.mem_powerset.mp mem)
      have zero : solutionCount scope ∅ T = 0 := by
        change T ≠ slots scope ∅ at ne
        simpa only [ite_eq_right ne] using hcount
      by_cases h : g 0 = b <;> simp [p, hT, zero, h]
    · by_cases h : g 0 = b <;> simp [hT, h]
  have filter_base : p base ↔ g (2 ^ n) = b := by
    simp [p, empty_solutionCount scope base (Finset.Subset.refl base), base]
  have count : (base.powerset.filter p).card =
      (if g 0 = b then smaller.card else 0) + (if g (2 ^ n) = b then 1 else 0) := by
    conv_lhs => rw [← Finset.insert_erase base_mem, Finset.filter_insert, filter_smaller]
    have not_mem : base ∉ smaller := Finset.notMem_erase _ _
    by_cases h₀ : g 0 = b <;> by_cases h₁ : g (2 ^ n) = b <;>
      simp [h₀, h₁, filter_base, Finset.card_insert_of_notMem, not_mem]
  rw [count, Nat.testBit_zero]
  cases g 0 <;> cases g (2 ^ n) <;> cases b <;>
    simp [smaller_parity, smaller_succ_parity]

end PEqualNP.Outside.L_meta_25718

open PEqualNP.Outside.L_meta_25718 in
theorem PEqualNP.Outside.L_meta_25718 : (∀ (n w : Nat) (hn : 0 < n),
  let Site := Fin n
  let Slot := Site × Finset Site
  let k := min n (w+1)
  let scope := fun i : Site => (Finset.range k).image
    (fun offset => (⟨(i.val+offset)%n, Nat.mod_lt _ hn⟩ : Site))
  let full := (Finset.univ : Finset Slot).filter (fun candidate => candidate.2 ⊆ scope candidate.1)
  let total := fun table : Finset Slot =>
    ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i, x ∩ scope i) ∈ table)).card
  let E := n*2^k
  ∀ g : Nat → Bool,
    (∃ (readAll : Nat → Slot) (decode : List Bool → Bool), ∀ A ∈ full.powerset,
      decode ((List.range E).map (fun h => decide (readAll h ∈ A))) = g (total A)) ∧
    ∀ (q : Nat) (ask : Nat → List Bool → Slot) (out : List Bool → Bool),
    let trace := fun (b : Nat) (input : Finset Slot) =>
      (List.range b).foldl (fun (h : List Bool) step => h ++ [decide (ask step h ∈ input)]) []
    let seen := fun active : Finset Slot =>
      ((List.range q).map (fun idx => ask idx (trace idx active))).toFinset
    (∀ T ∈ full.powerset, out (trace q T) = g (total T)) →
    full.card = E ∧
    (∀ b : Bool,
      (((full.powerset.filter (fun T => out (trace q T) = b ∧ full ⊆ seen T)).card).testBit 0 =
        xor (g 0) (g (2^n)))) ∧
    (g 0 ≠ g (2^n) → E ≤ q)) := by
  intro n w hn Site Slot k scope full total E g
  have full_eq : full = slots scope Finset.univ := by
    ext s
    simp [full, slots]
  have total_eq : total = solutionCount scope Finset.univ := by
    funext T
    simp [total, solutionCount]
    congr 1
  have full_card : full.card = E := by
    rw [full_eq]
    exact slots_card scope (cyclic_scope_card hn (Nat.min_le_left n (w + 1)))
  have full_nonempty : full.Nonempty := by
    rw [← Finset.card_pos, full_card]
    exact Nat.mul_pos hn (pow_pos (by decide) _)
  constructor
  · rw [← full_card]
    exact read_all full full_nonempty (fun T => g (total T))
  · intro q ask out trace seen exact_reader
    have reader_eq : ∀ T, T ∈ full.powerset →
        out (readerTrace ask q T) = g (total T) := exact_reader
    have parity (b : Bool) :
        ((full.powerset.filter (fun T => out (trace q T) = b ∧ full ⊆ seen T)).card).testBit 0 =
          xor (g 0) (g (2 ^ n)) := by
      have filtered : full.powerset.filter (fun T => out (readerTrace ask q T) = b) =
          full.powerset.filter (fun T => g (total T) = b) := by
        apply Finset.filter_congr
        intro T hT
        rw [reader_eq T hT]
      calc
        _ = ((full.powerset.filter
              (fun T => out (readerTrace ask q T) = b)).card).testBit 0 :=
            full_read_parity full ask out q b
        _ = xor (g 0) (g (2 ^ n)) := by
          rw [filtered, full_eq, total_eq]
          exact table_parity hn scope g b
    refine ⟨full_card, parity, ?_⟩
    intro distinct
    let S := full.powerset.filter (fun T => out (trace q T) = true ∧ full ⊆ seen T)
    have odd : S.card.testBit 0 = true := by
      have hx : xor (g 0) (g (2 ^ n)) = true := by
        cases h₀ : g 0 <;> cases h₁ : g (2 ^ n) <;> simp_all
      exact (parity true).trans hx
    have exists_full : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at odd
      simp at odd
    obtain ⟨T, hT⟩ := exists_full
    have cover : full ⊆ readerSeen ask q T := (Finset.mem_filter.mp hT).2.2
    rw [← full_card]
    exact (Finset.card_le_card cover).trans (readerSeen_card_le ask q T)

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_619

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem zmod2_ne_add : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide

theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem zmod2_self_add : ∀ x : ZMod 2, x + x ≠ 1 := by decide

theorem cast_card_odd (k : ℕ) (h : k % 2 = 1) : ((k : ℕ) : ZMod 2) = 1 := by
  rw [← ZMod.natCast_mod, h]
  rfl

theorem parity_form {n : ℕ} (P : Finset (Fin n → ZMod 2))
    (h : ∀ s : Finset (Fin n → ZMod 2), s ⊆ P → s.card ≤ n + 1 → s.card % 2 = 1 →
      (∑ v ∈ s, v) ≠ 0) :
    ∃ f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ v ∈ P, f v = 1 := by
  classical
  obtain ⟨b, hbP, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (P : Set (Fin n → ZMod 2))
  obtain ⟨B, rfl⟩ := (P.finite_toSet.subset hbP).exists_finset_coe
  have hli' : LinearIndepOn (ZMod 2) id (B : Set (Fin n → ZMod 2)) := hli
  have hcard : B.card ≤ n := by
    have := hli.finset_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  let E := Module.Basis.extend hli'
  let f := E.constr (ZMod 2) (fun _ => (1 : ZMod 2))
  have hf1 : ∀ x ∈ B, f x = 1 := by
    intro x hx
    have := E.constr_basis (ZMod 2) (fun _ => (1 : ZMod 2)) ⟨x, hli'.subset_extend _ hx⟩
    simpa [E, f] using this
  refine ⟨f, fun v hv => ?_⟩
  by_cases hvB : v ∈ B
  · exact hf1 v hvB
  have hvs : v ∈ Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2)) := by
    rw [hspan]; exact Submodule.subset_span hv
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hvs
  set T := B.filter (fun a => c a = 1) with hT
  have hTB : T ⊆ B := Finset.filter_subset _ _
  have hsum : ∑ a ∈ B, c a • a = ∑ a ∈ T, a := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs with h1
    · simp [h1]
    · rcases zmod2_cases (c a) with h0 | h0
      · simp [h0]
      · exact absurd h0 h1
  have hfv : f v = (T.card : ZMod 2) := by
    rw [← hc, hsum, map_sum, Finset.sum_congr rfl (fun a ha => hf1 a (hTB ha))]
    simp
  by_contra hne
  have hv0 : f v = 0 := (zmod2_cases _).resolve_right hne
  have hTev : T.card % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one T.card with h2 | h2
    · exact h2
    · rw [hfv, cast_card_odd _ h2] at hv0
      exact absurd hv0 one_ne_zero
  have hvT : v ∉ T := fun h' => hvB (hTB h')
  apply h (insert v T)
  · exact Finset.insert_subset hv (hTB.trans (fun x hx => by exact_mod_cast hbP hx))
  · rw [Finset.card_insert_of_notMem hvT]
    have := Finset.card_le_card hTB
    omega
  · rw [Finset.card_insert_of_notMem hvT]
    omega
  · rw [Finset.sum_insert hvT, ← hsum, hc]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_self (v i)

end PEqualNP.Outside.L_lib_619

open PEqualNP.Outside.L_lib_619 in
theorem PEqualNP.Outside.L_lib_619 : ∀ (n q rows cols pairs names messages : ℕ)
    (Y : Fin rows → Fin pairs → Bool → Fin names) (pass : Fin names → Bool)
    (col : Fin cols → Fin pairs → Bool → Bool) (pick : Fin rows → Fin pairs → Bool)
    (tag : Fin rows → Fin messages) (feature : Fin rows → Fin pairs → Fin n → ZMod 2),
  let V := Fin n → ZMod 2
  let edge := fun (r : Fin rows) (c : Fin cols) =>
    ∃ (z : Fin pairs) (p : Bool), pass (Y r z p) = true ∧ col c z p = true
  let seen := fun (r : Fin rows) (z : Fin pairs) => Y r z (pick r z)
  let direct := fun (r : Fin rows) (c : Fin cols) =>
    ∃ z, pass (seen r z) = true ∧ col c z (pick r z) = true
  let avail := fun (r : Fin rows) (c : Fin cols) (z : Fin pairs) =>
    col c z (!(pick r z)) = true
  let Need := {cell : Fin rows × Fin cols // edge cell.1 cell.2 ∧ ¬direct cell.1 cell.2}
  let conflict := fun (sel : Need → Fin pairs) (d : V) =>
    ∃ (t : Need) (r : Fin rows) (c : Fin cols) (z : Fin pairs),
      ¬edge r c ∧ avail r c z ∧ tag t.val.1 = tag r ∧
      seen t.val.1 (sel t) = seen r z ∧ feature t.val.1 (sel t) + feature r z = d
  (∃ (query : Fin q → (V →ₗ[ZMod 2] ZMod 2))
      (lookup : Fin messages → Fin names → (Fin q → ZMod 2) → Bool),
    ∀ (r : Fin rows) (c : Fin cols), edge r c ↔
      (direct r c ∨ ∃ z, avail r c z ∧
        lookup (tag r) (seen r z) (fun i => query i (feature r z)) = true)) ↔
  ∃ sel : Need → Fin pairs,
    (∀ t, avail t.val.1 t.val.2 (sel t)) ∧ ∃ parts : Fin q → Finset V,
      (∀ d, conflict sel d ↔ ∃ i, d ∈ parts i) ∧
      ∀ (i : Fin q) (s : Finset V), s ⊆ parts i → s.card ≤ n + 1 →
        s.card % 2 = 1 → (∑ v ∈ s, v) ≠ 0 := by
  classical
  intro n q rows cols pairs names messages Y pass col pick tag feature V edge seen direct avail
    Need conflict
  constructor
  · rintro ⟨query, lookup, hQ⟩
    have hNeed : ∀ t : Need, ∃ z, avail t.val.1 t.val.2 z ∧
        lookup (tag t.val.1) (seen t.val.1 z) (fun i => query i (feature t.val.1 z)) = true := by
      intro t
      obtain ⟨he, hd⟩ := t.2
      rcases (hQ _ _).1 he with h | h
      · exact absurd h hd
      · exact h
    choose sel hsel hlk using hNeed
    refine ⟨sel, hsel, fun i => Finset.univ.filter (fun d => conflict sel d ∧ query i d = 1),
      fun d => ⟨fun hc => ?_, fun hc => ?_⟩, ?_⟩
    · obtain ⟨t, r, c, z, hne, hav, htag, hseen, hd⟩ := hc
      have hneg : lookup (tag r) (seen r z) (fun i => query i (feature r z)) ≠ true := by
        intro hl
        exact hne ((hQ r c).2 (Or.inr ⟨z, hav, hl⟩))
      have hdiff : (fun i => query i (feature t.val.1 (sel t))) ≠
          (fun i => query i (feature r z)) := by
        intro heq
        apply hneg
        rw [← htag, ← hseen, ← heq]
        exact hlk t
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hdiff
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨t, r, c, z, hne, hav, htag, hseen, hd⟩, ?_⟩⟩
      rw [← hd, map_add]
      exact zmod2_ne_add _ _ hi
    · obtain ⟨i, hi⟩ := hc
      exact (Finset.mem_filter.mp hi).2.1
    · intro i s hs _ hodd hsum
      have hq : query i (∑ v ∈ s, v) = (s.card : ZMod 2) := by
        rw [map_sum, Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp (hs hv)).2.2)]
        simp
      rw [hsum, map_zero, cast_card_odd _ hodd] at hq
      exact zero_ne_one hq
  · rintro ⟨sel, hsel, parts, hparts, hodd⟩
    choose query hq using fun i => parity_form (parts i) (hodd i)
    refine ⟨query, fun m nm x => decide (∃ t : Need, tag t.val.1 = m ∧
      seen t.val.1 (sel t) = nm ∧ x = fun i => query i (feature t.val.1 (sel t))), ?_⟩
    intro r c
    constructor
    · intro he
      by_cases hd : direct r c
      · exact Or.inl hd
      · refine Or.inr ⟨sel ⟨(r, c), he, hd⟩, hsel ⟨(r, c), he, hd⟩, ?_⟩
        rw [decide_eq_true_eq]
        exact ⟨⟨(r, c), he, hd⟩, rfl, rfl, rfl⟩
    · rintro (hd | ⟨z, hav, hl⟩)
      · obtain ⟨z, hp, hc⟩ := hd
        exact ⟨z, pick r z, hp, hc⟩
      · by_contra hne
        rw [decide_eq_true_eq] at hl
        obtain ⟨t, htag, hseen, hx⟩ := hl
        have hc : conflict sel (feature t.val.1 (sel t) + feature r z) :=
          ⟨t, r, c, z, hne, hav, htag, hseen, rfl⟩
        obtain ⟨i, hi⟩ := (hparts _).1 hc
        have h1 := hq i _ hi
        rw [map_add] at h1
        have h2 := congrFun hx i
        rw [← h2] at h1
        exact zmod2_self_add _ h1

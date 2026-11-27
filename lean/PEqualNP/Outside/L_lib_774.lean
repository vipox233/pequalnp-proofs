import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_533

namespace PEqualNP.Outside.L_lib_774

def H {n m : ℕ} (G : Fin n → Fin m → Bool) : SimpleGraph (Fin (n + m)) :=
  SimpleGraph.fromRel (fun x y : Fin (n + m) =>
    ∃ a b, G a b = true ∧ x = Fin.castAdd m a ∧ y = Fin.natAdd n b)

theorem adj_iff {n m : ℕ} (G : Fin n → Fin m → Bool) (x y : Fin (n + m)) :
    (H G).Adj x y ↔ ∃ a b, G a b = true ∧
      ((x = Fin.castAdd m a ∧ y = Fin.natAdd n b) ∨ (y = Fin.castAdd m a ∧ x = Fin.natAdd n b)) := by
  unfold H
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨a, b, h, h1, h2⟩ | ⟨a, b, h, h1, h2⟩⟩
    · exact ⟨a, b, h, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨a, b, h, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨a, b, h, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨?_, Or.inl ⟨a, b, h, h1, h2⟩⟩
      intro hxy
      have h3 := congrArg Fin.val (h1.symm.trans (hxy.trans h2))
      simp at h3
      omega
    · refine ⟨?_, Or.inr ⟨a, b, h, h1, h2⟩⟩
      intro hxy
      have h3 := congrArg Fin.val (h1.symm.trans (hxy.symm.trans h2))
      simp at h3
      omega

theorem main (n m : ℕ) (G : Fin n → Fin m → Bool) :
    ∃ (k : ℕ) (r : Fin k → Fin n) (c : Fin k → Fin m) (R : Finset (Fin n)) (Cc : Finset (Fin m)),
      Function.Injective r ∧ Function.Injective c ∧ (∀ i, G (r i) (c i) = true) ∧
      (∀ a b, G a b = true → a ∈ R ∨ b ∈ Cc) ∧ R.card + Cc.card = k := by
  classical
  obtain ⟨M, T, hM, hdisj, hcov, hcard⟩ :=
    @PEqualNP.Outside.L_meta_533 (n + m) (H G) (Classical.decRel _)
      ⟨fun x => decide (x.val < n), by
        intro u v huv
        rw [adj_iff] at huv
        obtain ⟨a, b, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := huv <;> simp⟩
  have hedge : ∀ e : {e // e ∈ M}, ∃ p : Fin n × Fin m,
      G p.1 p.2 = true ∧ e.1 = s(Fin.castAdd m p.1, Fin.natAdd n p.2) := by
    rintro ⟨e, he⟩
    have h := hM e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, adj_iff] at h
      obtain ⟨a, b, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
      · exact ⟨(a, b), hab, rfl⟩
      · exact ⟨(a, b), hab, Sym2.eq_swap⟩
  choose ρ hρG hρe using hedge
  have key : ∀ i j : Fin M.card,
      (∃ v, v ∈ (M.equivFin.symm i).1 ∧ v ∈ (M.equivFin.symm j).1) → i = j := by
    rintro i j ⟨v, hvi, hvj⟩
    by_contra hij
    have hne : (M.equivFin.symm i).1 ≠ (M.equivFin.symm j).1 :=
      fun h => hij (M.equivFin.symm.injective (Subtype.ext h))
    exact hdisj _ (M.equivFin.symm i).2 _ (M.equivFin.symm j).2 hne v hvi hvj
  refine ⟨M.card, fun i => (ρ (M.equivFin.symm i)).1, fun i => (ρ (M.equivFin.symm i)).2,
    Finset.univ.filter (fun a => Fin.castAdd m a ∈ T),
    Finset.univ.filter (fun b => Fin.natAdd n b ∈ T), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : (ρ (M.equivFin.symm i)).1 = (ρ (M.equivFin.symm j)).1 := hij
    apply key
    refine ⟨Fin.castAdd m (ρ (M.equivFin.symm i)).1, ?_, ?_⟩
    · rw [hρe]
      exact Sym2.mem_mk_left _ _
    · rw [hρe (M.equivFin.symm j), hij']
      exact Sym2.mem_mk_left _ _
  · intro i j hij
    have hij' : (ρ (M.equivFin.symm i)).2 = (ρ (M.equivFin.symm j)).2 := hij
    apply key
    refine ⟨Fin.natAdd n (ρ (M.equivFin.symm i)).2, ?_, ?_⟩
    · rw [hρe]
      exact Sym2.mem_mk_right _ _
    · rw [hρe (M.equivFin.symm j), hij']
      exact Sym2.mem_mk_right _ _
  · intro i
    exact hρG _
  · intro a b hab
    have hadj : (H G).Adj (Fin.castAdd m a) (Fin.natAdd n b) :=
      (adj_iff G _ _).mpr ⟨a, b, hab, Or.inl ⟨rfl, rfl⟩⟩
    rcases hcov _ _ hadj with h | h
    · left
      simp [h]
    · right
      simp [h]
  · rw [← hcard]
    have h1 : (Finset.univ.filter (fun a : Fin n => Fin.castAdd m a ∈ T)).card =
        (T.filter (fun x => x.val < n)).card := by
      apply Finset.card_bij (fun a _ => Fin.castAdd m a)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp [ha]
      · intro a _ b _ h
        exact Fin.castAdd_injective _ _ h
      · intro x hx
        simp only [Finset.mem_filter] at hx
        refine ⟨⟨x.val, hx.2⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have : Fin.castAdd m ⟨x.val, hx.2⟩ = x := Fin.ext rfl
          rw [this]
          exact hx.1
        · exact Fin.ext rfl
    have h2 : (Finset.univ.filter (fun b : Fin m => Fin.natAdd n b ∈ T)).card =
        (T.filter (fun x => ¬ x.val < n)).card := by
      apply Finset.card_bij (fun b _ => Fin.natAdd n b)
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simp [hb]
      · intro a _ b _ h
        exact Fin.natAdd_injective _ _ h
      · intro x hx
        simp only [Finset.mem_filter, not_lt] at hx
        have hlt : x.val - n < m := by
          have := x.isLt
          omega
        refine ⟨⟨x.val - n, hlt⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have : Fin.natAdd n ⟨x.val - n, hlt⟩ = x := Fin.ext (by simp; omega)
          rw [this]
          exact hx.1
        · exact Fin.ext (by simp; omega)
    rw [h1, h2]
    exact Finset.card_filter_add_card_filter_not _

end PEqualNP.Outside.L_lib_774

theorem PEqualNP.Outside.L_lib_774 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool),
  ∃ (k : ℕ) (r : Fin k → Fin n) (c : Fin k → Fin m) (R : Finset (Fin n)) (Cc : Finset (Fin m)),
    Function.Injective r ∧ Function.Injective c ∧ (∀ i, G (r i) (c i) = true) ∧
    (∀ a b, G a b = true → a ∈ R ∨ b ∈ Cc) ∧ R.card + Cc.card = k) := by
  intro n m G
  exact PEqualNP.Outside.L_lib_774.main n m G

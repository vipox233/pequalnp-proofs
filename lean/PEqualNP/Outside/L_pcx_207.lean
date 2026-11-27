import Mathlib
import PEqualNP.Defs

-- L-pcx-207: keep the line: P is odd, or some x of S outside P is true, for growing P inside S.
-- To add y, first build the line: y false, or P even, from the pair clauses of y (one at a time),
-- then one generic step: weaken both lines to M plus a complementary equation, cut, weaken.
-- Each generic step costs 4 lines, so the total is about 2.5 |S|^2 lines.

namespace PEqualNP.Outside.L_pcx_207_aux

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

-- copied from prep_L_pcx_203.lean
theorem weak_sub {L M : LinKLine V} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

-- copied from prep_L_pcx_203.lean
theorem sat_single (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

def Narrow (M : LinKLine V) : Prop := ∀ T ∈ M, T.card ≤ 1

theorem weak_sem {L M : LinKLine V} (hM : Narrow M)
    (h : ∀ a, LinKLineSat a L → LinKLineSat a M) : IsLinKWeakening L M := by
  intro T hT
  by_cases h0 : (∅ : LinTerm V) ∈ M
  · exact Or.inl ⟨∅, h0, fun _ _ q hq => absurd hq (Finset.notMem_empty q)⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨S, hS, hSa⟩ := h a ⟨T, hT, ha⟩
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 (fun he => h0 (he ▸ hS))
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.1 (le_antisymm (hM S hS) hne.card_pos)
    exact ⟨q, hS, hSa q (Finset.mem_singleton_self q)⟩

theorem sat_insert (a : V → Bool) (T : LinTerm V) (M : LinKLine V) :
    LinKLineSat a (insert T M) ↔ LinTermSat a T ∨ LinKLineSat a M := by
  simp [LinKLineSat]

theorem termSat_single (a : V → Bool) (q : LinEq V) : LinTermSat a {q} ↔ LinEqSat a q := by
  simp [LinTermSat]

theorem sat_neg (a : V → Bool) (e : LinEq V) : LinEqSat a (negLinEq e) ↔ ¬ LinEqSat a e := by
  obtain ⟨f, b⟩ := e
  cases b <;> simp [LinEqSat, negLinEq]

theorem sat_clause (a : V → Bool) (C : Clause V) :
    LinKLineSat a (linKOfClause C) ↔ ∃ l ∈ C, a l.1 = l.2 := by
  unfold LinKLineSat LinTermSat linKOfClause linOfClause
  constructor
  · rintro ⟨T, hT, hTs⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨l, hl, (sat_single a l.1 l.2).1 (hTs _ (Finset.mem_singleton_self _))⟩
  · rintro ⟨l, hl, h⟩
    refine ⟨{(({l.1} : Finset V), l.2)},
      Finset.mem_image.2 ⟨_, Finset.mem_image.2 ⟨l, hl, rfl⟩, rfl⟩, ?_⟩
    intro q hq
    rw [Finset.mem_singleton.1 hq]
    exact (sat_single a l.1 l.2).2 h

theorem narrow_insert {e : LinEq V} {M : LinKLine V} (hM : Narrow M) : Narrow (insert {e} M) := by
  intro T hT
  rcases Finset.mem_insert.1 hT with rfl | hT
  · simp
  · exact hM T hT

theorem step1 {F : Set (LinKLine V)} {π : List (LinKLine V)} {C M : LinKLine V}
    (hπ : IsLinKDerivation 1 IsLinKWeakening F π) (hC : C ∈ π) (hM : Narrow M)
    (h : ∀ a, LinKLineSat a C → LinKLineSat a M) :
    IsLinKDerivation 1 IsLinKWeakening F (M :: π) :=
  IsLinKDerivation.weak hπ hC (weak_sem hM h) hM

theorem step2 {F : Set (LinKLine V)} {π : List (LinKLine V)} {C D M : LinKLine V} (e : LinEq V)
    (hπ : IsLinKDerivation 1 IsLinKWeakening F π) (hC : C ∈ π) (hD : D ∈ π) (hM : Narrow M)
    (h1 : ∀ a, LinKLineSat a C → LinKLineSat a M ∨ LinEqSat a e)
    (h2 : ∀ a, LinKLineSat a D → LinKLineSat a M ∨ ¬ LinEqSat a e) :
    ∃ l : List (LinKLine V), l.length = 4 ∧ M ∈ l ∧
      IsLinKDerivation 1 IsLinKWeakening F (l ++ π) := by
  have d1 := step1 hπ hC (narrow_insert (e := e) hM) (fun a ha => by
    rw [sat_insert, termSat_single]; exact (h1 a ha).symm)
  have d2 := step1 d1 (List.mem_cons_of_mem _ hD) (narrow_insert (e := negLinEq e) hM)
    (fun a ha => by rw [sat_insert, termSat_single, sat_neg]; exact (h2 a ha).symm)
  set R : LinKLine V := (insert {e} M).erase {e} ∪
    (insert {negLinEq e} M \ ({e} : LinTerm V).image (fun e => ({negLinEq e} : LinTerm V)))
    with hRdef
  have hRM : R ⊆ M := by
    intro T hT
    simp only [R, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert,
      Finset.image_singleton, Finset.mem_singleton] at hT
    tauto
  have d3 : IsLinKDerivation 1 IsLinKWeakening F
      (R :: insert {negLinEq e} M :: insert {e} M :: π) :=
    IsLinKDerivation.cut d2 (by simp) (by simp) ⟨{e}, by simp, by simp, rfl⟩
      (fun T hT => hM T (hRM hT))
  have d4 := IsLinKDerivation.weak d3 (by simp) (weak_sub hRM) hM
  exact ⟨[M, R, insert ({negLinEq e} : LinTerm V) M, insert ({e} : LinTerm V) M], rfl,
    by simp, d4⟩

def par (a : V → Bool) (P : Finset V) : Prop := Odd (P.filter (fun v => a v = true)).card

theorem par_insert (a : V → Bool) {y : V} {P : Finset V} (hy : y ∉ P) :
    par a (insert y P) ↔ (par a P ↔ a y = false) := by
  unfold par
  rw [Finset.filter_insert]
  cases h : a y
  · simp
  · have : y ∉ P.filter (fun v => a v = true) := by simp [hy]
    simp [Finset.card_insert_of_notMem this, Nat.odd_add_one]

theorem eqSat (a : V → Bool) (P : Finset V) (b : Bool) :
    LinEqSat a (P, b) ↔ (par a P ↔ b = true) := Iff.rfl

def pos (Q : Finset V) : LinKLine V := Q.image (fun x => ({(({x} : Finset V), true)} : LinTerm V))

def E (S P : Finset V) : LinKLine V := insert {(P, true)} (pos (S \ P))

def Dl (y : V) (P : Finset V) : LinKLine V := {{(({y} : Finset V), false)}, {(P, false)}}

theorem sat_pos (a : V → Bool) (Q : Finset V) :
    LinKLineSat a (pos Q) ↔ ∃ x ∈ Q, a x = true := by
  simp [LinKLineSat, pos, LinTermSat, sat_single]

theorem sat_E (a : V → Bool) (S P : Finset V) :
    LinKLineSat a (E S P) ↔ par a P ∨ ∃ x ∈ S \ P, a x = true := by
  unfold E
  rw [sat_insert, termSat_single, sat_pos, eqSat]
  simp

theorem sat_Dl (a : V → Bool) (y : V) (P : Finset V) :
    LinKLineSat a (Dl y P) ↔ a y = false ∨ ¬ par a P := by
  unfold Dl
  rw [sat_insert, termSat_single, sat_single, ← Finset.insert_empty, sat_insert,
    termSat_single, eqSat]
  simp [LinKLineSat]

theorem narrow_pos (Q : Finset V) : Narrow (pos Q) := by
  intro T hT
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hT
  simp

theorem narrow_E (S P : Finset V) : Narrow (E S P) := narrow_insert (narrow_pos _)

theorem narrow_Dl (y : V) (P : Finset V) : Narrow (Dl y P) := by
  intro T hT
  simp only [Dl, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl <;> simp

theorem addAx {G : Set (Clause V)} {π : List (LinKLine V)}
    (hπ : IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' G) π) {C : Clause V} (hC : C ∈ G) :
    IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' G) (linKOfClause C :: π) :=
  IsLinKDerivation.ax hπ ⟨C, hC, rfl⟩ (by
    intro T hT
    unfold linKOfClause at hT
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT
    simp)

theorem dchain (G : Set (Clause V)) (S : Finset V)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ G) (y : V) (hy : y ∈ S) :
    ∀ P : Finset V, P ⊆ S → y ∉ P → ∀ π : List (LinKLine V),
      IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' G) π → π ≠ [] →
      ∃ l : List (LinKLine V), l.length ≤ 5 * P.card + 1 ∧ Dl y P ∈ l ++ π ∧
        IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' G) (l ++ π) := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ π hπ hne
    obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil π hne
    refine ⟨[Dl y ∅], by simp, by simp, step1 hπ hC (narrow_Dl y ∅) (fun a _ => ?_)⟩
    rw [sat_Dl]
    right
    simp [par]
  | insert x P hx ih =>
    intro hsub hyP π hπ hne
    have hxS : x ∈ S := hsub (Finset.mem_insert_self x P)
    have hPS : P ⊆ S := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    have hyx : y ≠ x := fun h => hyP (h ▸ Finset.mem_insert_self x P)
    have hyP' : y ∉ P := fun h => hyP (Finset.mem_insert_of_mem h)
    obtain ⟨l1, hl1, hm1, hd1⟩ := ih hPS hyP' π hπ hne
    have hax := addAx hd1 (hpair x hxS y hy (Ne.symm hyx))
    obtain ⟨l2, hl2, hm2, hd2⟩ := step2 (C := Dl y P)
      (D := linKOfClause {(x, false), (y, false)}) (M := Dl y (insert x P))
      (({x} : Finset V), true) hax
      (List.mem_cons_of_mem _ hm1) (by simp) (narrow_Dl y (insert x P))
      (fun a ha => by
        rw [sat_Dl] at ha
        rw [sat_Dl, par_insert a hx, sat_single]
        rcases ha with ha | ha
        · exact Or.inl (Or.inl ha)
        · cases h : a x
          · exact Or.inl (Or.inr (by simpa using ha))
          · exact Or.inr rfl)
      (fun a ha => by
        rw [sat_clause] at ha
        rw [sat_Dl, sat_single]
        simp at ha
        cases h : a x <;> simp_all)
    refine ⟨l2 ++ linKOfClause {(x, false), (y, false)} :: l1, ?_, ?_, ?_⟩
    · simp [hl2, Finset.card_insert_of_notMem hx]
      omega
    · simp [hm2]
    · simpa using hd2

theorem echain (G : Set (Clause V)) (S : Finset V) (hpos : S.image (fun x => (x, true)) ∈ G)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ G) :
    ∀ P : Finset V, P ⊆ S → ∃ π : List (LinKLine V),
      IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' G) π ∧ E S P ∈ π ∧
        2 * π.length ≤ 4 + 5 * P.card * (P.card + 1) := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _
    have h0 := addAx (IsLinKDerivation.nil (k := 1) (W := IsLinKWeakening)) hpos
    refine ⟨_, step1 (C := linKOfClause (S.image fun x => (x, true))) h0 (by simp) (narrow_E S ∅) (fun a ha => ?_), by simp, by simp⟩
    rw [sat_clause] at ha
    rw [sat_E]
    right
    simpa using ha
  | insert y P hy ih =>
    intro hsub
    have hyS : y ∈ S := hsub (Finset.mem_insert_self y P)
    have hPS : P ⊆ S := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    obtain ⟨π, hd, hm, hlen⟩ := ih hPS
    obtain ⟨l1, hl1, hm1, hd1⟩ := dchain G S hpair y hyS P hPS hy π hd
      (List.ne_nil_of_mem hm)
    obtain ⟨l2, hl2, hm2, hd2⟩ := step2 (P, true) hd1 (List.mem_append_right _ hm) hm1
      (narrow_E S (insert y P))
      (fun a ha => by
        rw [sat_E] at ha
        rw [sat_E, par_insert a hy, eqSat]
        rcases ha with ha | ⟨x, hx, hax⟩
        · exact Or.inr (by simpa using ha)
        · by_cases hxy : x = y
          · subst hxy
            by_cases hp : par a P
            · exact Or.inr (by simpa using hp)
            · left; left; simp [hp, hax]
          · left; right
            refine ⟨x, ?_, hax⟩
            simp only [Finset.mem_sdiff, Finset.mem_insert] at hx ⊢
            tauto)
      (fun a ha => by
        rw [sat_Dl] at ha
        rw [sat_E, par_insert a hy, eqSat]
        by_cases hp : par a P
        · have : a y = false := by tauto
          left; left; simp [hp, this]
        · right; simpa using hp)
    refine ⟨l2 ++ (l1 ++ π), hd2, by simp [hm2], ?_⟩
    simp only [List.length_append, hl2, Finset.card_insert_of_notMem hy]
    nlinarith

end PEqualNP.Outside.L_pcx_207_aux

open PEqualNP.Outside.L_pcx_207_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_207 :
    ∀ (V : Type) [DecidableEq V] (S : Finset V)
        (F : Set (PEqualNP.ProofComplexity.Clause V)),
      S.image (fun x => (x, true)) ∈ F →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ F) →
      ∃ π : List (PEqualNP.ProofComplexity.LinKLine V),
        PEqualNP.ProofComplexity.IsLinKDerivation 1
          PEqualNP.ProofComplexity.IsLinKWeakening
          (PEqualNP.ProofComplexity.linKOfClause '' F) π ∧
        ({({(S, true)} : PEqualNP.ProofComplexity.LinTerm V)} :
          PEqualNP.ProofComplexity.LinKLine V) ∈ π ∧
        π.length ≤ 4 * (S.card + 1) ^ 2 := by
  intro V _ S F hpos hpair
  obtain ⟨π, hd, hm, hlen⟩ := echain F S hpos hpair S (subset_refl S)
  refine ⟨_, step1 hd hm (M := {{(S, true)}}) ?_ (fun a ha => ?_), by simp, ?_⟩
  · intro T hT
    simp only [Finset.mem_singleton] at hT
    subst hT
    simp
  · rw [sat_E] at ha
    simp only [Finset.sdiff_self, Finset.notMem_empty, false_and, exists_false, or_false] at ha
    exact ⟨{(S, true)}, by simp, by rw [termSat_single, eqSat]; simpa using ha⟩
  · simp only [List.length_cons]
    nlinarith
